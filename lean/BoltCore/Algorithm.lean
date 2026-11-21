import BoltCore.Syntax
import BoltCore.Types

/-!
# A model of the inference algorithm

The OCaml type checker (`lib/typer.ml`), without levels (that is, without
let-polymorphism, as in the paper's proof, Sec. 5). Coalescing
(`lib/coalesce.ml`) only affects how types are printed and is left for the
presentation of types (roadmap, step 5). Following the paper (Sec. 5.2), the only
mutable state of the algorithm, the bounds of type variables, becomes an
explicit `State`, and the algorithm's functions become big-step relations:

* `Constrain s a b s'`: constraining `a ≤ b` in state `s` succeeds with
  final state `s'`. A type error is the absence of a derivation.
* `TypeTerm Γ s t st s'`: typing `t` succeeds with simple type `st`.

Each `Constrain` rule only applies where the OCaml `match` would reach it
(`New`: the pair is neither cached nor reflexive; `_ ≤ Abs` before a
variable on the left; a variable on the left before one on the right), so
the relation is as deterministic as the code.

Parameter lists (issue #2): a signature `sig P` is a simple type, the
domain of a function with a parameter list. It stands for the union of the
closed argument records `Dₖ` (`SParams.domain`), which simple types cannot
write. An argument record below a signature is constrained against the
`Dₖ` for its number of positional arguments (`Constrain.recordSig`, the
OCaml `call`, without its checks for better error messages, which reject
nothing the field constraints accept); a signature below a record or a
signature has every `Dₖ` below it (`Constrain.sigL`).

Deviations from the OCaml code, to revisit: the memo table for row
expansion is keyed by the label list as given rather than as a sorted set.
The labels in a `with` are distinct: the parser (`lib/parser.ml`) rejects a
repeated one.
-/

namespace BoltCore.Alg

/-! ## Simple types (Fig. 6) -/

mutual
inductive SType where
  /-- A type variable: an index into the bounds of the state. -/
  | var : Nat → SType
  | prim : String → SType
  | arrow : SType → SType → SType
  /-- A record type, or a row in tail position (as in `Types.simple_type`). -/
  | record : SFields → SType → SType
  /-- `Abs`: the top field and the top row. -/
  | abs
  /-- The field that is definitely absent. -/
  | missing
  /-- A field: missing, or present at the type. -/
  | opt : SType → SType
  /-- The empty row (in tail position): every label is missing. -/
  | nil
  /-- A parameter list, as the domain of a function only: it stands for the
  union of the closed argument records `Dₖ` (`SParams.domain`). -/
  | sig : SParams → SType

inductive SFields where
  | nil
  | cons : String → SType → SFields → SFields

/-- The parameters of a signature, in order (positional-only, then
either-way, then keyword-only): name, kind, whether it has a default, and
type. -/
inductive SParams where
  | nil
  | cons : String → PKind → Bool → SType → SParams → SParams
end

/-- A present field: a type, as opposed to `Abs`, `Missing` and `Opt τ`. -/
def SType.IsPre : SType → Prop
  | .abs | .missing | .opt _ => False
  | _ => True

theorem SType.IsPre.ne_abs : {f : SType} → f.IsPre → f ≠ .abs
  | .abs, h => absurd h id
  | .var _, _ | .prim _, _ | .arrow _ _, _ | .record _ _, _ | .nil, _ | .sig _, _ =>
    fun h => nomatch h
  | .missing, h | .opt _, h => absurd h id

namespace SFields

def lookup (l : String) : SFields → Option SType
  | nil => none
  | cons n f fs => if n = l then some f else lookup l fs

def append : SFields → SFields → SFields
  | nil, gs => gs
  | cons n f fs, gs => cons n f (append fs gs)

def labels : SFields → List String
  | nil => []
  | cons n _ fs => n :: labels fs

/-- The fields whose labels are in `K`. -/
def absentIn (K : List String) : SFields → SFields
  | nil => nil
  | cons n f fs => if n ∈ K then cons n f (absentIn K fs) else absentIn K fs

/-- The fields whose labels are not in `K`. -/
def presentIn (K : List String) : SFields → SFields
  | nil => nil
  | cons n f fs => if n ∈ K then presentIn K fs else cons n f (presentIn K fs)

/-- The same labels, all absent. -/
def absOf : SFields → SFields
  | nil => nil
  | cons n _ fs => cons n .abs (absOf fs)

/-- Pairs `(f₀, f₁)` for the labels of `fs₁` that `fs₀` also has. -/
def common (fs₀ : SFields) : SFields → List (SType × SType)
  | nil => []
  | cons n f₁ fs => match fs₀.lookup n with
    | some f₀ => (f₀, f₁) :: common fs₀ fs
    | none => common fs₀ fs

/-- The fields of `fs₁` whose labels `fs₀` does not have. -/
def missing (fs₀ : SFields) : SFields → SFields
  | nil => nil
  | cons n f fs => match fs₀.lookup n with
    | some _ => missing fs₀ fs
    | none => cons n f (missing fs₀ fs)

/-- `(abs, f)` for every field. -/
def absPairs : SFields → List (SType × SType)
  | nil => []
  | cons _ f fs => (.abs, f) :: absPairs fs

/-- `(missing, f)` for every field. -/
def misPairs : SFields → List (SType × SType)
  | nil => []
  | cons _ f fs => (.missing, f) :: misPairs fs

/-- `(f, missing)` for every field. -/
def toMisPairs : SFields → List (SType × SType)
  | nil => []
  | cons _ f fs => (f, .missing) :: toMisPairs fs

end SFields

/-- Flatten nested rows: `{fs | {fs' | t}}` is `{fs, fs' | t}` (`row_view`). -/
def rowView : SType → SFields × SType
  | .record fs t => let r := rowView t; (fs.append r.1, r.2)
  | t => (.nil, t)

/-- The rest of a row: its remaining fields over its tail. -/
def restRow (fs : SFields) (t : SType) : SType :=
  match fs with
  | .nil => t
  | _ => .record fs t

/-! ## Signatures

The argument records of a parameter list, as simple types. The split of
the parameters into those passed by position and those passed by name is
the one of the declarative system (`Param.pos`, `Param.named`). -/

/-- The parameters as a list. -/
def SParams.toList : SParams → List (Param SType)
  | .nil => []
  | .cons n k o τ P => ⟨n, k, o, τ⟩ :: P.toList

/-- The type of a list: nested closed records (`list_type`). -/
def SType.list : List SType → SType
  | [] => .record .nil .nil
  | τ :: τs => .record (.cons "hd" τ (.cons "tl" (SType.list τs) .nil)) .nil

/-- A field for each parameter, optional if it has a default. -/
def SFields.ofParams : List (Param SType) → SFields
  | [] => .nil
  | p :: ps => .cons p.name (if p.opt then .opt p.ty else p.ty) (SFields.ofParams ps)

/-- `Dₖ`, the argument record for `k` arguments passed by position
(`sig_domain`): `{*: [τ₁, …, τₖ], Eₖ, Q}`. -/
def SParams.domain (P : SParams) (k : Nat) : SType :=
  .record (.cons "*" (SType.list (Param.pos k P.toList))
    (SFields.ofParams (Param.named k P.toList))) .nil

/-- Every `Dₖ`, for `m ≤ k ≤ p` (`sig_domains`). -/
def SParams.domains (P : SParams) : List SType := (Param.counts P.toList).map P.domain

/-- The number of elements of a list type, if its spine is known
(`list_elems`): each cell is a closed record of a `hd` and a `tl`. -/
def SType.listLen : SType → Option Nat
  | .record .nil .nil => some 0
  | .record (.cons n₁ f₁ (.cons n₂ f₂ .nil)) .nil =>
    if n₁ = "hd" ∧ n₂ = "tl" then f₂.listLen.map (· + 1)
    else if n₁ = "tl" ∧ n₂ = "hd" then f₁.listLen.map (· + 1)
    else none
  | _ => none

/-- A record or a signature: what a signature can be below. -/
def SType.IsRecSig : SType → Prop
  | .record _ _ | .sig _ => True
  | _ => False

/-! ## Levels

Each variable has a level, for let-polymorphism (Sec. 3.5): the right-hand
side of a `let` is typed one level up, and the variables above the level of
the `let` are generalized. The level of a type is the highest level of its
variables (`Types.level`). -/

mutual
def SType.level (L : Nat → Nat) : SType → Nat
  | .var v => L v
  | .prim _ | .abs | .missing | .nil => 0
  | .opt t => t.level L
  | .arrow a b => max (a.level L) (b.level L)
  | .record fs t => max (fs.level L) (t.level L)
  | .sig P => P.level L

def SFields.level (L : Nat → Nat) : SFields → Nat
  | .nil => 0
  | .cons _ f fs => max (f.level L) (fs.level L)

def SParams.level (L : Nat → Nat) : SParams → Nat
  | .nil => 0
  | .cons _ _ _ τ P => max (τ.level L) (P.level L)
end

/-! ## State -/

structure Bounds where
  lower : List SType := []
  upper : List SType := []

structure State where
  /-- Bounds of each variable (variables at or above `next` have none). -/
  bounds : Nat → Bounds
  /-- The next fresh variable. -/
  next : Nat
  /-- Constraints already being or been solved, in the current `constrain` call. -/
  cache : List (SType × SType)
  /-- Memoized row expansions: `(ρ, labels) ↦ ρ'`. -/
  exps : List ((Nat × List String) × Nat)
  /-- *Ghost state* for the proofs, not in the OCaml code: every constraint
  ever accepted, across all `constrain` calls (the cache only lives for
  one call). -/
  log : List (SType × SType)
  /-- The kind of each variable: the labels it does not represent (the
  record it is the tail of lists them). Empty for ordinary type variables.
  The OCaml code sets a variable's kind when allocating it and never
  changes it; the model fixes the whole map up front instead (no step
  changes it), and the rules that allocate a variable require it to have
  the right kind. Every run of the OCaml code is a run of the model, for
  the map of the kinds it ended up allocating. -/
  kind : Nat → List String
  /-- The level of each variable. Like the kind, the OCaml code sets it
  when allocating the variable and never changes it, and the model fixes
  the whole map up front: the rules that allocate a variable at a level
  require it to have that level. -/
  level : Nat → Nat := fun _ => 0

namespace State

/-- The initial state, for the kinds `K` of the run. -/
def initK (K : Nat → List String) : State := ⟨fun _ => {}, 0, [], [], [], K, fun _ => 0⟩

def init : State := initK fun _ => []

/-- Allocate the variable `s.next`. -/
def fresh (s : State) : State := { s with next := s.next + 1 }

def remember (s : State) (a b : SType) : State :=
  { s with cache := (a, b) :: s.cache, log := (a, b) :: s.log }

def addUpper (s : State) (v : Nat) (t : SType) : State :=
  { s with bounds := fun w => if w = v then { s.bounds w with upper := t :: (s.bounds w).upper }
                              else s.bounds w }

def addLower (s : State) (v : Nat) (t : SType) : State :=
  { s with bounds := fun w => if w = v then { s.bounds w with lower := t :: (s.bounds w).lower }
                              else s.bounds w }

/-- Give `v` the lower bounds `ts`, before those it has. -/
def addLowers (s : State) (v : Nat) (ts : List SType) : State :=
  { s with bounds := fun w => if w = v then { s.bounds w with lower := ts ++ (s.bounds w).lower }
                              else s.bounds w }

/-- Give `v` the upper bounds `ts`, before those it has. -/
def addUppers (s : State) (v : Nat) (ts : List SType) : State :=
  { s with bounds := fun w => if w = v then { s.bounds w with upper := ts ++ (s.bounds w).upper }
                              else s.bounds w }

/-- Log constraints that inference relies on without constraining (ghost:
only the log changes). -/
def logAll (s : State) (ps : List (SType × SType)) : State := { s with log := ps ++ s.log }

/-- The pair still has to be solved: it is neither reflexive nor cached
(the first check of `constrain`). -/
def New (s : State) (a b : SType) : Prop := a ≠ b ∧ (a, b) ∉ s.cache

end State

open State

/-! ## No structural recursive types

Like the OCaml code (`check_acyclic`, unless `--rectypes`), the model
rejects structural recursive types, as an occurs check would: no variable may reach itself through a type
constructor. This is witnessed by a *ranking* of the variables (decidable
for a finite graph, and checkable when given): the variables of a
non-variable bound rank strictly below the bounded variable, and a
variable bound ranks at most as high. Cycles of variable bounds such as
`α ≤ β ≤ α` stay allowed: they equate variables without building an
infinite type. -/

mutual
/-- The variables occurring in a type. -/
def SType.vars : SType → List Nat
  | .var v => [v]
  | .prim _ | .abs | .missing | .nil => []
  | .opt t => t.vars
  | .arrow a b => a.vars ++ b.vars
  | .record fs t => fs.vars ++ t.vars
  | .sig P => P.vars

def SFields.vars : SFields → List Nat
  | .nil => []
  | .cons _ f fs => f.vars ++ fs.vars

def SParams.vars : SParams → List Nat
  | .nil => []
  | .cons _ _ _ τ P => τ.vars ++ P.vars
end

/-- The bounds of each variable are ranked by `r`. -/
def StructRanked (σ : Nat → Bounds) (r : Nat → Nat) : Prop :=
  ∀ v b, (b ∈ (σ v).upper ∨ b ∈ (σ v).lower) →
    (∀ w, b = .var w → r w ≤ r v) ∧ ((∀ w, b ≠ .var w) → ∀ w ∈ b.vars, r w < r v)

/-! ## Extrusion (Fig. 7)

`extrude ty pol lvl` copies `ty` so that the copy has level at most `lvl`.
A type whose level is low enough is returned as it is. A variable whose
level is too high gets a fresh copy at level `lvl`, of the same kind, once
per polarity (the table `c`): for a positive occurrence the copy is above
the variable, so it becomes one of its upper bounds and gets the extruded
copies of its lower bounds; dually for a negative one. The parameter of a
function has the opposite polarity, the fields of a record and the
parameters of a signature the same.

There is no rule for an optional field on its own, with a level that is
too high: `Opt τ` is only a field, extruded as one (`ExtrudeFields.opt`).

The ghost log gets what a certificate needs (`lib/typer.ml` records the
first two, `lib/cert.ml` adds the others):

* the pair of each copied type and its original, in the order of the
  polarity (`polPair`);
* for a signature, the argument records of the lower one below the upper
  one and below its argument records, and their lists of positional
  arguments, suffix by suffix (`sigPairs`, the OCaml `note_sig`);
* each bound that is installed, as a constraint, when it is installed;
* for a positive copy `w` of `v`, each lower bound of `v` below `w`, which
  consistency at `v` asks for; dually for a negative copy. -/

/-- The copies made by one extrusion: the copy of a variable at a
polarity. -/
abbrev Copies := List ((Nat × Bool) × Nat)

/-- A copy and its original as a constraint: a positive copy is above the
original, a negative one below. -/
def polPair (pol : Bool) (t t' : SType) : SType × SType :=
  match pol with
  | true => (t, t')
  | false => (t', t)

/-- The lists of two argument lists, suffix by suffix (down to the last
cell). -/
def listPairs : List SType → List SType → List (SType × SType)
  | a :: as, b :: bs => (SType.list (a :: as), SType.list (b :: bs)) :: listPairs as bs
  | _, _ => []

/-- What relates a signature `lo` to a signature `hi` above it with the
same parameters, of other types: each argument record of `lo` is below
`hi`, and below the argument record of `hi` for the same number of
positional arguments, and so are their lists of positional arguments
(`note_sig`). -/
def sigPairs (lo hi : SParams) : List (SType × SType) :=
  (Param.counts lo.toList).flatMap fun k =>
    (lo.domain k, .sig hi) :: (lo.domain k, hi.domain k) ::
      listPairs (Param.pos k lo.toList) (Param.pos k hi.toList)

/-- `sigPairs`, for a signature and its copy at a polarity. -/
def sigPairsPol (pol : Bool) (P P' : SParams) : List (SType × SType) :=
  match pol with
  | true => sigPairs P P'
  | false => sigPairs P' P

mutual
inductive Extrude : State → Copies → Bool → Nat → SType → SType → State → Copies → Prop where
  /-- The level is low enough: nothing to copy. -/
  | low : t.level s.level ≤ lvl → Extrude s c pol lvl t t s c
  | arrow : lvl < (SType.arrow l r).level s.level →
      Extrude s c (!pol) lvl l l' s₁ c₁ → Extrude s₁ c₁ pol lvl r r' s₂ c₂ →
      Extrude s c pol lvl (.arrow l r) (.arrow l' r')
        (s₂.logAll [polPair pol (.arrow l r) (.arrow l' r')]) c₂
  | record : lvl < (SType.record fs t).level s.level →
      ExtrudeFields s c pol lvl fs fs' s₁ c₁ → Extrude s₁ c₁ pol lvl t t' s₂ c₂ →
      Extrude s c pol lvl (.record fs t) (.record fs' t')
        (s₂.logAll [polPair pol (.record fs t) (.record fs' t')]) c₂
  | sig : lvl < (SType.sig P).level s.level →
      ExtrudeParams s c pol lvl P P' s₁ c₁ →
      Extrude s c pol lvl (.sig P) (.sig P')
        (s₁.logAll (polPair pol (.sig P) (.sig P') :: sigPairsPol pol P P')) c₁
  /-- A variable that was copied at this polarity. -/
  | varCopied : lvl < s.level v → c.lookup (v, pol) = some w →
      Extrude s c pol lvl (.var v) (.var w) (s.logAll [polPair pol (.var v) (.var w)]) c
  /-- A positive occurrence: the copy `s.next` is an upper bound of `v`,
  installed before the lower bounds of `v` are extruded (they may reach
  `v` again), and gets their copies as its lower bounds. -/
  | varPos : lvl < s.level v → c.lookup (v, true) = none →
      s.level s.next = lvl → s.kind s.next = s.kind v →
      ExtrudeEach ((s.fresh.addUpper v (.var s.next)).logAll [(.var v, .var s.next)])
        (((v, true), s.next) :: c) true lvl (s.bounds v).lower ls s₁ c₁ →
      Extrude s c true lvl (.var v) (.var s.next)
        ((s₁.addLowers s.next ls).logAll
          (ls.map (·, .var s.next) ++ (s.bounds v).lower.map (·, .var s.next))) c₁
  /-- A negative occurrence, dually. -/
  | varNeg : lvl < s.level v → c.lookup (v, false) = none →
      s.level s.next = lvl → s.kind s.next = s.kind v →
      ExtrudeEach ((s.fresh.addLower v (.var s.next)).logAll [(.var s.next, .var v)])
        (((v, false), s.next) :: c) false lvl (s.bounds v).upper us s₁ c₁ →
      Extrude s c false lvl (.var v) (.var s.next)
        ((s₁.addUppers s.next us).logAll
          (us.map (.var s.next, ·) ++ (s.bounds v).upper.map (.var s.next, ·))) c₁

/-- The fields of a record: an optional field is not a type, only the type
in it is extruded. -/
inductive ExtrudeFields :
    State → Copies → Bool → Nat → SFields → SFields → State → Copies → Prop where
  | nil : ExtrudeFields s c pol lvl .nil .nil s c
  | opt : Extrude s c pol lvl t t' s₁ c₁ → ExtrudeFields s₁ c₁ pol lvl fs fs' s₂ c₂ →
      ExtrudeFields s c pol lvl (.cons n (.opt t) fs) (.cons n (.opt t') fs') s₂ c₂
  | cons : (∀ t, f ≠ .opt t) → Extrude s c pol lvl f f' s₁ c₁ →
      ExtrudeFields s₁ c₁ pol lvl fs fs' s₂ c₂ →
      ExtrudeFields s c pol lvl (.cons n f fs) (.cons n f' fs') s₂ c₂

/-- The parameters of a signature: they are fields of its argument
records, so they have its polarity. -/
inductive ExtrudeParams :
    State → Copies → Bool → Nat → SParams → SParams → State → Copies → Prop where
  | nil : ExtrudeParams s c pol lvl .nil .nil s c
  | cons : Extrude s c pol lvl τ τ' s₁ c₁ → ExtrudeParams s₁ c₁ pol lvl P P' s₂ c₂ →
      ExtrudeParams s c pol lvl (.cons n k o τ P) (.cons n k o τ' P') s₂ c₂

/-- The bounds of a copied variable, in order. -/
inductive ExtrudeEach :
    State → Copies → Bool → Nat → List SType → List SType → State → Copies → Prop where
  | nil : ExtrudeEach s c pol lvl [] [] s c
  | cons : Extrude s c pol lvl t t' s₁ c₁ → ExtrudeEach s₁ c₁ pol lvl ts ts' s₂ c₂ →
      ExtrudeEach s c pol lvl (t :: ts) (t' :: ts') s₂ c₂
end

/-! ## Constraining (Fig. 9, with rows) -/

mutual
inductive Constrain : State → SType → SType → State → Prop where
  | cached : (a, b) ∈ s.cache → Constrain s a b s
  | refl : Constrain s a a s
  | arrow : s.New (.arrow l₀ r₀) (.arrow l₁ r₁) →
      Constrain (s.remember (.arrow l₀ r₀) (.arrow l₁ r₁)) l₁ l₀ s₁ →
      Constrain s₁ r₀ r₁ s₂ →
      Constrain s (.arrow l₀ r₀) (.arrow l₁ r₁) s₂
  /-- `Abs` is the top field and the top row. -/
  | absR : s.New a .abs → Constrain s a .abs (s.remember a .abs)
  /-- The top row is below a row only if that row guarantees nothing. -/
  | absRecord : s.New .abs (.record fs t) →
      FieldsEach (s.remember .abs (.record fs t)) fs.absPairs s₁ →
      Constrain s₁ .abs t s₂ →
      Constrain s .abs (.record fs t) s₂
  /-- The empty row is below a row that accepts every label missing. -/
  | nilRecord : s.New .nil (.record fs t) →
      FieldsEach (s.remember .nil (.record fs t)) fs.misPairs s₁ →
      Constrain s₁ .nil t s₂ →
      Constrain s .nil (.record fs t) s₂
  /-- A row is below the empty row if it has no field at all. -/
  | recordNil : s.New (.record fa ta) .nil → rowView (.record fa ta) = (fs₀, t₀) →
      FieldsEach (s.remember (.record fa ta) .nil) fs₀.toMisPairs s₁ →
      Constrain s₁ t₀ .nil s₂ →
      Constrain s (.record fa ta) .nil s₂
  /-- Rows: common fields, then labels only on the right (from the left
  tail, expanding a row variable), then the rest into the right tail. -/
  | record : s.New (.record fa ta) (.record fb tb) →
      rowView (.record fa ta) = (fs₀, t₀) → rowView (.record fb tb) = (fs₁, t₁) →
      FieldsEach (s.remember (.record fa ta) (.record fb tb)) (fs₀.common fs₁) s₁ →
      Expand s₁ t₀ (fs₀.missing fs₁) t₀' s₂ →
      Constrain s₂ (restRow (fs₁.missing fs₀) t₀') t₁ s₃ →
      Constrain s (.record fa ta) (.record fb tb) s₃
  /-- A variable on the left: record the upper bound, then make every lower
  bound fit it (installing the bound first, as Sec. 3.2.2 requires). -/
  | varL : s.New (.var v) b → b ≠ .abs →
      ConstrainEach ((s.remember (.var v) b).addUpper v b)
        ((s.bounds v).lower.map (·, b)) s₁ →
      Constrain s (.var v) b s₁
  | varR : s.New a (.var v) → (∀ w, a ≠ .var w) →
      ConstrainEach ((s.remember a (.var v)).addLower v a)
        ((s.bounds v).upper.map (a, ·)) s₁ →
      Constrain s a (.var v) s₁
  /-- An argument record below a signature: the number `k` of positional
  arguments, the length of its `*` list, picks `Dₖ`; then it is an ordinary
  record constraint. -/
  | recordSig : s.New (.record fa ta) (.sig P) → rowView (.record fa ta) = (fs₀, t₀) →
      fs₀.lookup "*" = some pos → pos.listLen = some k → k ∈ Param.counts P.toList →
      Constrain (s.remember (.record fa ta) (.sig P)) (.record fa ta) (P.domain k) s₁ →
      Constrain s (.record fa ta) (.sig P) s₁
  /-- A signature is the union of its argument records: each is below the
  right side. -/
  | sigL : s.New (.sig P) b → b.IsRecSig →
      ConstrainEach (s.remember (.sig P) b) (P.domains.map (·, b)) s₁ →
      Constrain s (.sig P) b s₁

/-- Sequential constraining of a list of pairs. -/
inductive ConstrainEach : State → List (SType × SType) → State → Prop where
  | nil : ConstrainEach s [] s
  | cons : Constrain s a b s₁ → ConstrainEach s₁ rest s₂ → ConstrainEach s ((a, b) :: rest) s₂

/-- A field below another: `Abs` is the top; `Pre τ ≤ Opt τ` and
`Missing ≤ Opt τ`. A field that is or may be missing cannot satisfy a
present one ("missing field"), and a field that is or may be present cannot
satisfy `Missing` ("unexpected field"). -/
inductive ConstrainField : State → SType → SType → State → Prop where
  | toAbs : ConstrainField s f .abs s
  | misMis : ConstrainField s .missing .missing s
  | misOpt : ConstrainField s .missing (.opt τ) s
  | optOpt : τ₀ ≠ .abs → Constrain s τ₀ τ₁ s₁ → ConstrainField s (.opt τ₀) (.opt τ₁) s₁
  | preOpt : f₀.IsPre → Constrain s f₀ τ₁ s₁ → ConstrainField s f₀ (.opt τ₁) s₁
  | pre : f₀.IsPre → f₁.IsPre → Constrain s f₀ f₁ s₁ → ConstrainField s f₀ f₁ s₁

inductive FieldsEach : State → List (SType × SType) → State → Prop where
  | nil : FieldsEach s [] s
  | cons : ConstrainField s a b s₁ → FieldsEach s₁ rest s₂ → FieldsEach s ((a, b) :: rest) s₂

/-- Providing the labels `missing` from the left tail `t`: nothing to do;
an `Abs` tail can only provide absent fields, the empty row missing ones; a
row variable does not
represent the labels in its kind, which are absent too, and is expanded for
the others (`expansion` in `lib/typer.ml`), reusing a memoized expansion
variable. The expansion variable lacks the tail's kind and the expanded
labels. -/
inductive Expand : State → SType → SFields → SType → State → Prop where
  | none : Expand s t .nil t s
  | abs : ms ≠ .nil → FieldsEach s ms.absPairs s₁ → Expand s .abs ms .abs s₁
  | nil : ms ≠ .nil → FieldsEach s ms.misPairs s₁ → Expand s .nil ms .nil s₁
  | allAbsent : ms ≠ .nil → ms.presentIn (s.kind v) = .nil →
      FieldsEach s (ms.absentIn (s.kind v)).absPairs s₁ →
      Expand s (.var v) ms (.var v) s₁
  | memo : ms ≠ .nil → ms.presentIn (s.kind v) ≠ .nil →
      FieldsEach s (ms.absentIn (s.kind v)).absPairs s₁ →
      s₁.exps.lookup (v, (ms.presentIn (s.kind v)).labels) = some r →
      Constrain s₁ (.var v) (.record (ms.presentIn (s.kind v)) (.var r)) s₂ →
      Expand s (.var v) ms (.var r) s₂
  | fresh : ms ≠ .nil → ms.presentIn (s.kind v) ≠ .nil →
      FieldsEach s (ms.absentIn (s.kind v)).absPairs s₁ →
      s₁.exps.lookup (v, (ms.presentIn (s.kind v)).labels) = none →
      s.kind s₁.next = s.kind v ++ (ms.presentIn (s.kind v)).labels →
      Constrain
        { s₁ with next := s₁.next + 1,
                  exps := ((v, (ms.presentIn (s.kind v)).labels), s₁.next) :: s₁.exps }
        (.var v) (.record (ms.presentIn (s.kind v)) (.var s₁.next)) s₂ →
      Expand s (.var v) ms (.var s₁.next) s₂
end

/-- A top-level `constrain` call: it starts and ends with an empty cache. -/
def ConstrainTop (s : State) (a b : SType) (s' : State) : Prop :=
  ∃ s₁, Constrain { s with cache := [] } a b s₁ ∧ s' = { s₁ with cache := [] }

/-! ## Typing terms (Fig. 8, monomorphic `let`) -/

abbrev SCtx := List (String × SType)

def SCtx.lookup (Γ : SCtx) (x : String) : Option SType := (Γ.find? (·.1 = x)).map (·.2)

/-- A binding found by `List.lookup` is in the list. -/
theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {k : α} {r : β} :
    ∀ {xs : List (α × β)}, xs.lookup k = some r → (k, r) ∈ xs
  | [], h => by simp [List.lookup] at h
  | (k', r') :: xs, h => by
    simp only [List.lookup] at h
    split at h
    · next he => cases h; rw [beq_iff_eq.mp he]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- Looking a name up in a context mapped over its entries is looking it up
in the context, mapped. -/
theorem lookup_map {α β : Type} (g : α → β) (Γ : List (String × α)) (x : String) :
    ((Γ.map fun p => (p.1, g p.2)).find? (·.1 = x)).map (·.2) =
      ((Γ.find? (·.1 = x)).map (·.2)).map g := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    by_cases h : p.1 = x
    · simp [h]
    · simp only [List.map_cons, List.find?_cons, h, decide_false]; exact ih

mutual
inductive TypeTerm : SCtx → State → Term → SType → State → Prop where
  | lit : TypeTerm Γ s (.lit n) (.prim "int") s
  | var : Γ.lookup x = some st → TypeTerm Γ s (.var x) st s
  | lam : s.kind s.next = [] → TypeTerm ((x, .var s.next) :: Γ) s.fresh t st s₁ →
      TypeTerm Γ s (.lam x t) (.arrow (.var s.next) st) s₁
  /-- The result variable is allocated first, as in `lib/typer.ml`. -/
  | app : s.kind s.next = [] → TypeTerm Γ s.fresh f stf s₁ → TypeTerm Γ s₁ a sta s₂ →
      ConstrainTop s₂ stf (.arrow sta (.var s.next)) s₃ →
      TypeTerm Γ s (.app f a) (.var s.next) s₃
  /-- A record literal has exactly its fields: its row is closed. -/
  | rcd : TypeFields Γ s fs F s₁ → TypeTerm Γ s (.rcd fs) (.record F .nil) s₁
  | sel : s.kind s.next = [] → TypeTerm Γ s.fresh t st s₁ →
      ConstrainTop s₁ st (.record (.cons l (.var s.next) .nil) .abs) s₂ →
      TypeTerm Γ s (.sel t l) (.var s.next) s₂
  /-- `t.l ?? d`: the field may be missing, and `d` has its type. -/
  | selOr : s.kind s.next = [] → TypeTerm Γ s.fresh t st s₁ →
      ConstrainTop s₁ st (.record (.cons l (.opt (.var s.next)) .nil) .abs) s₂ →
      TypeTerm Γ s₂ d std s₃ →
      ConstrainTop s₃ std (.var s.next) s₄ →
      TypeTerm Γ s (.selOr t l d) (.var s.next) s₄
  /-- `t with {fs}`: `t ≤ {fs ↦ Abs | ρ}`, result `{fs | ρ}`, where `ρ`
  lacks the labels of `fs`. -/
  | ext : fs ≠ [] → TypeTerm Γ s t st s₁ → TypeFields Γ s₁ fs F s₂ →
      s₂.kind s₂.next = F.labels →
      ConstrainTop s₂.fresh st (.record F.absOf (.var s₂.next)) s₃ →
      TypeTerm Γ s (.ext t fs) (.record F (.var s₂.next)) s₃
  /-- `t with {}` is just `t`. -/
  | extNil : TypeTerm Γ s t st s₁ → TypeTerm Γ s (.ext t []) st s₁
  | letIn : TypeTerm Γ s r str s₁ → TypeTerm ((x, str) :: Γ) s₁ b stb s₂ →
      TypeTerm Γ s (.letIn false x r b) stb s₂
  /-- `let rec` binds a function (as `type_let_rhs` checks). -/
  | letRec : r.IsFun → s.kind s.next = [] → TypeTerm ((x, .var s.next) :: Γ) s.fresh r inf s₁ →
      ConstrainTop s₁ inf (.var s.next) s₂ →
      TypeTerm ((x, .var s.next) :: Γ) s₂ b stb s₃ →
      TypeTerm Γ s (.letIn true x r b) stb s₃
  /-- `if c then a else b`: the condition is a boolean, and both branches
  flow into the result variable, allocated first. -/
  | ite : s.kind s.next = [] → TypeTerm Γ s.fresh c stc s₁ →
      ConstrainTop s₁ stc (.prim "bool") s₂ →
      TypeTerm Γ s₂ a sta s₃ → ConstrainTop s₃ sta (.var s.next) s₄ →
      TypeTerm Γ s₄ b stb s₅ → ConstrainTop s₅ stb (.var s.next) s₆ →
      TypeTerm Γ s (.ite c a b) (.var s.next) s₆
  /-- `fn (…) -> t`: the parameters give the signature and the context of
  the body. The parameter list is well-formed (`Param.WF`), which the
  parser guarantees (`lib/parser.ml`); the typer does not check it. -/
  | fn : Param.WF P.toList → TypeParams Γ s ps P Γ' s₁ → TypeTerm Γ' s₁ t st s₂ →
      TypeTerm Γ s (.fn ps t) (.arrow (.sig P) st) s₂

inductive TypeFields : SCtx → State → List (String × Term) → SFields → State → Prop where
  | nil : TypeFields Γ s [] .nil s
  | cons : TypeTerm Γ s t st s₁ → TypeFields Γ s₁ fs F s₂ →
      TypeFields Γ s ((l, t) :: fs) (.cons l st F) s₂

/-- The parameters of a `fn`: each gets a fresh variable; a default is
typed in the scope of the parameters before it and flows into its
parameter's type, as an argument would. -/
inductive TypeParams :
    SCtx → State → List (String × PKind × Option Term) → SParams → SCtx → State → Prop where
  | nil : TypeParams Γ s [] .nil Γ s
  | req : s.kind s.next = [] → TypeParams ((x, .var s.next) :: Γ) s.fresh ps P Γ' s₁ →
      TypeParams Γ s ((x, k, none) :: ps) (.cons x k false (.var s.next) P) Γ' s₁
  | dflt : s.kind s.next = [] → TypeTerm Γ s.fresh d std s₁ →
      ConstrainTop s₁ std (.var s.next) s₂ →
      TypeParams ((x, .var s.next) :: Γ) s₂ ps P Γ' s₃ →
      TypeParams Γ s ((x, k, some d) :: ps) (.cons x k true (.var s.next) P) Γ' s₃
end

/-- The signature of a built-in: positional-only parameters, under names
source code cannot write, numbered from `i`. -/
def builtinSig : Nat → List SType → SParams
  | _, [] => .nil
  | i, τ :: τs => .cons s!"#{i}" .posOnly false τ (builtinSig (i + 1) τs)

/-- The built-ins. The functions take parameter lists. -/
def builtins : SCtx :=
  [ ("true", .prim "bool"), ("false", .prim "bool"),
    ("not", .arrow (.sig (builtinSig 0 [.prim "bool"])) (.prim "bool")),
    ("succ", .arrow (.sig (builtinSig 0 [.prim "int"])) (.prim "int")),
    ("add", .arrow (.sig (builtinSig 0 [.prim "int", .prim "int"])) (.prim "int")) ]

/-! ## Sanity checks -/

section Examples

/-- `fun x -> x` gets `α₀ → α₀`, with no bounds. -/
theorem typeTerm_id :
    TypeTerm builtins State.init (.lam "x" (.var "x")) (.arrow (.var 0) (.var 0)) State.init.fresh :=
  .lam rfl (.var rfl)

/-- `1 2` is rejected: there is no way to constrain `int ≤ int → α`. -/
theorem typeTerm_app_lit : ¬ ∃ st s', TypeTerm builtins State.init (.app (.lit 1) (.lit 2)) st s' := by
  rintro ⟨st, s', h⟩
  cases h with
  | app _ hf ha hc =>
    cases hf
    cases ha
    obtain ⟨s₁, hc, _⟩ := hc
    cases hc with
    | cached hm => simp at hm

/-- `(fun x -> x) 42` succeeds, and constraint propagation gives the result
variable `α₀` the lower bound `int`: `α₁ → α₁ ≤ int → α₀` gives `int ≤ α₁`,
then `α₁ ≤ α₀`, which propagates `α₁`'s lower bound to `int ≤ α₀`. -/
theorem typeTerm_app_id :
    ∃ s', TypeTerm builtins State.init (.app (.lam "x" (.var "x")) (.lit 42)) (.var 0) s' ∧
      (s'.bounds 0).lower = [.prim "int"] := by
  refine ⟨_, .app rfl (.lam rfl (.var rfl)) .lit
    ⟨_, .arrow ?n₁ (.varR ?n₂ ?nv₂ .nil) (.varL ?n₃ ?na₃ (.cons (.varR ?n₄ ?nv₄ .nil) .nil)), rfl⟩, ?b⟩
  case b => rfl
  all_goals
    first
    | (intro w h; cases h)
    | (intro h; cases h)
    | (refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp_all [State.remember, State.addLower, State.addUpper, State.init, State.initK, State.fresh])

end Examples

end BoltCore.Alg
