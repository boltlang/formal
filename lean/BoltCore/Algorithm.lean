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
  /-- The absent field and the top row. -/
  | abs

inductive SFields where
  | nil
  | cons : String → SType → SFields → SFields
end

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

namespace State

/-- The initial state, for the kinds `K` of the run. -/
def initK (K : Nat → List String) : State := ⟨fun _ => {}, 0, [], [], [], K⟩

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
  | .prim _ | .abs => []
  | .arrow a b => a.vars ++ b.vars
  | .record fs t => fs.vars ++ t.vars

def SFields.vars : SFields → List Nat
  | .nil => []
  | .cons _ f fs => f.vars ++ fs.vars
end

/-- The bounds of each variable are ranked by `r`. -/
def StructRanked (σ : Nat → Bounds) (r : Nat → Nat) : Prop :=
  ∀ v b, (b ∈ (σ v).upper ∨ b ∈ (σ v).lower) →
    (∀ w, b = .var w → r w ≤ r v) ∧ ((∀ w, b ≠ .var w) → ∀ w ∈ b.vars, r w < r v)

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

/-- Sequential constraining of a list of pairs. -/
inductive ConstrainEach : State → List (SType × SType) → State → Prop where
  | nil : ConstrainEach s [] s
  | cons : Constrain s a b s₁ → ConstrainEach s₁ rest s₂ → ConstrainEach s ((a, b) :: rest) s₂

/-- A field type below another: `Abs` is the top, and an absent field
cannot satisfy a present one ("missing field"). -/
inductive ConstrainField : State → SType → SType → State → Prop where
  | toAbs : ConstrainField s f .abs s
  | pre : f₀ ≠ .abs → f₁ ≠ .abs → Constrain s f₀ f₁ s₁ → ConstrainField s f₀ f₁ s₁

inductive FieldsEach : State → List (SType × SType) → State → Prop where
  | nil : FieldsEach s [] s
  | cons : ConstrainField s a b s₁ → FieldsEach s₁ rest s₂ → FieldsEach s ((a, b) :: rest) s₂

/-- Providing the labels `missing` from the left tail `t`: nothing to do;
an `Abs` tail can only provide absent fields; a row variable does not
represent the labels in its kind, which are absent too, and is expanded for
the others (`expansion` in `lib/typer.ml`), reusing a memoized expansion
variable. The expansion variable lacks the tail's kind and the expanded
labels. -/
inductive Expand : State → SType → SFields → SType → State → Prop where
  | none : Expand s t .nil t s
  | abs : ms ≠ .nil → FieldsEach s ms.absPairs s₁ → Expand s .abs ms .abs s₁
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
  | rcd : TypeFields Γ s fs F s₁ → TypeTerm Γ s (.rcd fs) (.record F .abs) s₁
  | sel : s.kind s.next = [] → TypeTerm Γ s.fresh t st s₁ →
      ConstrainTop s₁ st (.record (.cons l (.var s.next) .nil) .abs) s₂ →
      TypeTerm Γ s (.sel t l) (.var s.next) s₂
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

inductive TypeFields : SCtx → State → List (String × Term) → SFields → State → Prop where
  | nil : TypeFields Γ s [] .nil s
  | cons : TypeTerm Γ s t st s₁ → TypeFields Γ s₁ fs F s₂ →
      TypeFields Γ s ((l, t) :: fs) (.cons l st F) s₂
end

/-- The monomorphic built-ins (`if` is polymorphic and needs schemes, which
come with let-polymorphism). -/
def builtins : SCtx :=
  [ ("true", .prim "bool"), ("false", .prim "bool"),
    ("not", .arrow (.prim "bool") (.prim "bool")),
    ("succ", .arrow (.prim "int") (.prim "int")),
    ("add", .arrow (.prim "int") (.arrow (.prim "int") (.prim "int"))) ]

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
