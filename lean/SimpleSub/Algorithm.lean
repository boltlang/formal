import SimpleSub.Syntax
import SimpleSub.Types

/-!
# A model of the inference algorithm

The OCaml type checker (`lib/typer.ml`) and raw coalescing
(`lib/coalesce.ml`), without levels (that is, without let-polymorphism, as
in the paper's proof, Sec. 5). Following the paper (Sec. 5.2), the only
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
expansion is keyed by the label list as given rather than as a sorted set,
and labels in a `with` are assumed distinct.
-/

namespace SimpleSub.Alg

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

namespace State

def init : State := ⟨fun _ => {}, 0, [], [], []⟩

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
an `Abs` tail can only provide absent fields; a row variable is expanded
(`expansion` in `lib/typer.ml`), reusing a memoized expansion variable. -/
inductive Expand : State → SType → SFields → SType → State → Prop where
  | none : Expand s t .nil t s
  | abs : ms ≠ .nil → FieldsEach s ms.absPairs s₁ → Expand s .abs ms .abs s₁
  | memo : ms ≠ .nil → s.exps.lookup (v, ms.labels) = some r →
      Constrain s (.var v) (.record ms (.var r)) s₁ →
      Expand s (.var v) ms (.var r) s₁
  | fresh : ms ≠ .nil → s.exps.lookup (v, ms.labels) = none →
      Constrain { s with next := s.next + 1, exps := ((v, ms.labels), s.next) :: s.exps }
        (.var v) (.record ms (.var s.next)) s₁ →
      Expand s (.var v) ms (.var s.next) s₁
end

/-- A top-level `constrain` call: it starts and ends with an empty cache. -/
def ConstrainTop (s : State) (a b : SType) (s' : State) : Prop :=
  ∃ s₁, Constrain { s with cache := [] } a b s₁ ∧ s' = { s₁ with cache := [] }

/-! ## Typing terms (Fig. 8, monomorphic `let`) -/

abbrev SCtx := List (String × SType)

def SCtx.lookup (Γ : SCtx) (x : String) : Option SType := (Γ.find? (·.1 = x)).map (·.2)

mutual
inductive TypeTerm : SCtx → State → Term → SType → State → Prop where
  | lit : TypeTerm Γ s (.lit n) (.prim "int") s
  | var : Γ.lookup x = some st → TypeTerm Γ s (.var x) st s
  | lam : TypeTerm ((x, .var s.next) :: Γ) s.fresh t st s₁ →
      TypeTerm Γ s (.lam x t) (.arrow (.var s.next) st) s₁
  /-- The result variable is allocated first, as in `lib/typer.ml`. -/
  | app : TypeTerm Γ s.fresh f stf s₁ → TypeTerm Γ s₁ a sta s₂ →
      ConstrainTop s₂ stf (.arrow sta (.var s.next)) s₃ →
      TypeTerm Γ s (.app f a) (.var s.next) s₃
  | rcd : TypeFields Γ s fs F s₁ → TypeTerm Γ s (.rcd fs) (.record F .abs) s₁
  | sel : TypeTerm Γ s.fresh t st s₁ →
      ConstrainTop s₁ st (.record (.cons l (.var s.next) .nil) .abs) s₂ →
      TypeTerm Γ s (.sel t l) (.var s.next) s₂
  /-- `t with {fs}`: `t ≤ {fs ↦ Abs | ρ}`, result `{fs | ρ}`. -/
  | ext : TypeTerm Γ s t st s₁ → TypeFields Γ s₁ fs F s₂ →
      ConstrainTop s₂.fresh st (.record F.absOf (.var s₂.next)) s₃ →
      TypeTerm Γ s (.ext t fs) (.record F (.var s₂.next)) s₃
  | letIn : TypeTerm Γ s r str s₁ → TypeTerm ((x, str) :: Γ) s₁ b stb s₂ →
      TypeTerm Γ s (.letIn false x r b) stb s₂
  | letRec : TypeTerm ((x, .var s.next) :: Γ) s.fresh r inf s₁ →
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

/-! ## Coalescing (Sec. 3.3.3, contractive as in `lib/coalesce.ml`)

Positive occurrences of a variable become the union of the variable and its
lower bounds, negative ones the intersection with its upper bounds. Every
variable visit introduces a `μ` binder; meeting the same (variable,
polarity) again refers back to it (`bvar` = how many visits ago), unless no
type constructor was passed in between (`parents`), in which case the
neutral element is used, so the result is contractive. Each visit uses up
one unit of fuel; `2 * next + 1` always suffices, since a visit adds a new
(variable, polarity) pair to `inProc`. -/

def vname (v : Nat) : String := "α" ++ toString v

def indexOf (p : Nat × Bool) : List (Nat × Bool) → Option Nat
  | [] => none
  | q :: qs => if q = p then some 0 else (indexOf p qs).map (· + 1)

mutual
def coalesce (σ : Nat → Bounds) : Nat → SType → Bool → List (Nat × Bool) → List Nat → Ty
  | _, .prim n, _, _, _ => .prim n
  | _, .abs, _, _, _ => .abs
  | fuel, .arrow a b, pol, inProc, _ =>
    .arrow (coalesce σ fuel a (!pol) inProc []) (coalesce σ fuel b pol inProc [])
  | fuel, .record fs t, pol, inProc, parents =>
    .record (coalesceF σ fuel fs pol inProc) (coalesce σ fuel t pol inProc parents)
  | 0, .var v, _, _, _ => .fvar (vname v)
  | fuel + 1, .var v, pol, inProc, parents =>
    match indexOf (v, pol) inProc with
    | some i => if v ∈ parents then (if pol then .bot else .top) else .bvar i
    | none =>
      let bounds := if pol then (σ v).lower else (σ v).upper
      .mu (coalesceBounds σ fuel bounds pol ((v, pol) :: inProc) (v :: parents) (.fvar (vname v)))
termination_by fuel st _ _ _ => (fuel, sizeOf st, 0)

def coalesceF (σ : Nat → Bounds) : Nat → SFields → Bool → List (Nat × Bool) → Fields
  | _, .nil, _, _ => .nil
  | fuel, .cons n f fs, pol, inProc =>
    .cons n (coalesce σ fuel f pol inProc []) (coalesceF σ fuel fs pol inProc)
termination_by fuel fs _ _ => (fuel, sizeOf fs, 0)

/-- Fold the bounds into a union (positive) or intersection (negative). -/
def coalesceBounds (σ : Nat → Bounds) (fuel : Nat) : List SType → Bool → List (Nat × Bool) →
    List Nat → Ty → Ty
  | [], _, _, _, acc => acc
  | b :: bs, pol, inProc, parents, acc =>
    let t := coalesce σ fuel b pol inProc parents
    coalesceBounds σ fuel bs pol inProc parents (if pol then .union acc t else .inter acc t)
termination_by bs _ _ _ _ => (fuel, sizeOf bs, 1)
end

/-- Coalesce a positive type in state `s`. -/
def coalesceTop (s : State) (st : SType) : Ty :=
  coalesce s.bounds (2 * s.next + 1) st true [] []

/-! ## Sanity checks -/

section Examples

/-- `fun x -> x` gets `α₀ → α₀`, with no bounds. -/
theorem typeTerm_id :
    TypeTerm builtins State.init (.lam "x" (.var "x")) (.arrow (.var 0) (.var 0)) State.init.fresh :=
  .lam (.var rfl)

/-- Its coalesced type: `(μ. α₀) → (μ. α₀)`, where each `μ` binds nothing
(every variable visit introduces a binder). -/
example : coalesceTop State.init.fresh (.arrow (.var 0) (.var 0)) =
    .arrow (.mu (.fvar "α0")) (.mu (.fvar "α0")) := by
  simp [coalesceTop, coalesce, coalesceBounds, indexOf, State.init, State.fresh]
  decide

/-- `1 2` is rejected: there is no way to constrain `int ≤ int → α`. -/
theorem typeTerm_app_lit : ¬ ∃ st s', TypeTerm builtins State.init (.app (.lit 1) (.lit 2)) st s' := by
  rintro ⟨st, s', h⟩
  cases h with
  | app hf ha hc =>
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
  refine ⟨_, .app (.lam (.var rfl)) .lit
    ⟨_, .arrow ?n₁ (.varR ?n₂ ?nv₂ .nil) (.varL ?n₃ ?na₃ (.cons (.varR ?n₄ ?nv₄ .nil) .nil)), rfl⟩, ?b⟩
  case b => rfl
  all_goals
    first
    | (intro w h; cases h)
    | (intro h; cases h)
    | (refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp_all [State.remember, State.addLower, State.addUpper, State.init, State.fresh])

end Examples

end SimpleSub.Alg
