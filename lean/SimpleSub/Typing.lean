import SimpleSub.Syntax
import SimpleSub.Sub

/-!
# Declarative typing

The type system that inferred types are meant to be correct for (the
paper's Fig. 2, extended with integer literals and record extension), over
the minimal subtyping relation of `Sub.lean`. The context holds type
*schemes*, so that built-ins such as `if : ∀α. bool → α → α → α` can be
instantiated, and let-bound variables can be polymorphic (below). The
algorithm model is still monomorphic in `let`, as in the paper's proof
(Sec. 5).

Quantified variables are free type variables (`fvar`) listed in the scheme;
instantiation substitutes them simultaneously (`Ty.substM`).

**Let-polymorphism** is ML's: `let x = s in t` gives `x` the scheme
`∀ᾱ. σ` for a type `σ` of `s`, provided the variables `ᾱ` are free
neither in the context nor in the definitions `E` of graph variables
(`Gen`); `let rec` does the same after typing `s` with `x` monomorphic.
A monomorphic `let` is the case `ᾱ = []` (`Typ.letIn_mono`). There is no
value restriction: the language has no mutable state (Bolt will need one).

`t with {l₁ = e₁, …}` is typed like the OCaml type checker types it: `t`
must be a record whose fields `lᵢ` may be anything (`Abs`) and whose other
fields form some row `ρ`; the result has the new fields over the same `ρ`.
Labels in a `with` are assumed distinct (the OCaml checker keeps the last
binding of a repeated label). `t with {}` is just `t`.
-/

namespace SimpleSub

/-! ## Substitution of free variables -/

mutual
/-- Simultaneous substitution of free type variables. -/
def Ty.substM : Ty → (String → Option Ty) → Ty
  | .fvar x, m => (m x).getD (.fvar x)
  | .top, _ => .top
  | .bot, _ => .bot
  | .abs, _ => .abs
  | .prim n, _ => .prim n
  | .bvar i, _ => .bvar i
  | .union a b, m => .union (a.substM m) (b.substM m)
  | .inter a b, m => .inter (a.substM m) (b.substM m)
  | .arrow a b, m => .arrow (a.substM m) (b.substM m)
  | .record fs t, m => .record (fs.substM m) (t.substM m)
  | .mu a, m => .mu (a.substM m)
  | .proj l t, m => .proj l (t.substM m)
  | .gvar n, _ => .gvar n

def Fields.substM : Fields → (String → Option Ty) → Fields
  | .nil, _ => .nil
  | .cons l f fs, m => .cons l (f.substM m) (fs.substM m)
end

mutual
theorem Ty.substM_none : ∀ t : Ty, t.substM (fun _ => none) = t
  | .fvar _ | .top | .bot | .abs | .prim _ | .bvar _ | .gvar _ => rfl
  | .union a b | .inter a b | .arrow a b => by
    simp only [Ty.substM, Ty.substM_none a, Ty.substM_none b]
  | .record fs t => by simp only [Ty.substM, Fields.substM_none fs, Ty.substM_none t]
  | .mu a => by simp only [Ty.substM, Ty.substM_none a]
  | .proj _ t => by simp only [Ty.substM, Ty.substM_none t]

theorem Fields.substM_none : ∀ fs : Fields, fs.substM (fun _ => none) = fs
  | .nil => rfl
  | .cons _ f fs => by simp only [Fields.substM, Ty.substM_none f, Fields.substM_none fs]
end

/-! ## Schemes and contexts -/

/-- `∀ vars. body`. -/
structure Scheme where
  poly ::
  vars : List String
  body : Ty

/-- A monomorphic scheme. -/
def Scheme.mono (t : Ty) : Scheme := .poly [] t

/-- `τ` is an instance of `σ`: substitute types for (some of) its
quantified variables. -/
def Scheme.Instance (σ : Scheme) (τ : Ty) : Prop :=
  ∃ m : String → Option Ty, (∀ x, (m x).isSome → x ∈ σ.vars) ∧ τ = σ.body.substM m

theorem Scheme.instance_mono (t : Ty) : (Scheme.mono t).Instance t :=
  ⟨fun _ => none, by simp, (Ty.substM_none t).symm⟩

/-- Contexts: the most recent binding of a name comes first. -/
abbrev Ctx := List (String × Scheme)

def Ctx.lookup (Γ : Ctx) (x : String) : Option Scheme :=
  (Γ.find? (·.1 = x)).map (·.2)

/-! ## Free variables and generalization -/

mutual
/-- The free type variables of a type. -/
def Ty.fv : Ty → List String
  | .fvar x => [x]
  | .top | .bot | .abs | .prim _ | .bvar _ | .gvar _ => []
  | .union a b | .inter a b | .arrow a b => a.fv ++ b.fv
  | .record fs t => fs.fv ++ t.fv
  | .mu a | .proj _ a => a.fv

def Fields.fv : Fields → List String
  | .nil => []
  | .cons _ f fs => f.fv ++ fs.fv
end

/-- `a` is free in the scheme `σ`. -/
def Scheme.FreeIn (a : String) (σ : Scheme) : Prop := a ∈ σ.body.fv ∧ a ∉ σ.vars

/-- `a` is free in no scheme of `Γ`. -/
def Ctx.Avoids (Γ : Ctx) (a : String) : Prop := ∀ p ∈ Γ, ¬ p.2.FreeIn a

/-- `a` occurs in no definition of a graph variable. -/
def Defs.Avoids (E : Defs) (a : String) : Prop := ∀ n u, E n u → a ∉ u.fv

/-- The variables `vars` may be generalized in `Γ` (and `E`). -/
def Gen (E : Defs) (Γ : Ctx) (vars : List String) : Prop :=
  ∀ a ∈ vars, Γ.Avoids a ∧ Defs.Avoids E a

/-! ## Typing rules

Typing is relative to definitions `E` of type variables (see `Sub.lean`):
types may refer to defined variables, which is how inferred solutions are
expressed. -/

variable {E : Defs}

/-- The same labels, all with the absent field. -/
def Fields.absOf : Fields → Fields
  | .nil => .nil
  | .cons l _ fs => .cons l .abs fs.absOf

mutual
inductive Typ (E : Defs) : Ctx → Term → Ty → Prop where
  | lit : Typ E Γ (.lit n) (.prim "int")
  | var : Γ.lookup x = some σ → σ.Instance τ → Typ E Γ (.var x) τ
  | lam : Typ E ((x, .mono τ₁) :: Γ) t τ₂ → Typ E Γ (.lam x t) (.arrow τ₁ τ₂)
  | app : Typ E Γ f (.arrow τ₁ τ₂) → Typ E Γ a τ₁ → Typ E Γ (.app f a) τ₂
  | rcd : TypFields E Γ fs F → Typ E Γ (.rcd fs) (.record F .abs)
  | sel : Typ E Γ t (.record (.cons l τ .nil) .abs) → Typ E Γ (.sel t l) τ
  /-- `t with {fs}`: `t`'s fields `fs` may be anything, the rest is `ρ`. -/
  | ext : Typ E Γ t (.record F.absOf ρ) → TypFields E Γ fs F → Typ E Γ (.ext t fs) (.record F ρ)
  /-- `t with {}` evaluates to `t`, whatever its type (as in `lib/typer.ml`). -/
  | extNil : Typ E Γ t τ → Typ E Γ (.ext t []) τ
  /-- `let`: generalize the variables `vars` of a type of `s`. -/
  | letIn : Typ E Γ s σ → Gen E Γ vars → Typ E ((x, .poly vars σ) :: Γ) t τ →
      Typ E Γ (.letIn false x s t) τ
  /-- `let rec`: `x` is monomorphic in `s`, generalized in `t`. -/
  | letRec : Typ E ((x, .mono σ) :: Γ) s σ → Gen E Γ vars →
      Typ E ((x, .poly vars σ) :: Γ) t τ → Typ E Γ (.letIn true x s t) τ
  /-- Subsumption. -/
  | sub : Typ E Γ t τ → Sub E τ τ' → Typ E Γ t τ'

/-- Field terms and their types, label by label. -/
inductive TypFields (E : Defs) : Ctx → List (String × Term) → Fields → Prop where
  | nil : TypFields E Γ [] .nil
  | cons : Typ E Γ t τ → TypFields E Γ fs F → TypFields E Γ ((l, t) :: fs) (.cons l τ F)
end

/-! ## Built-ins (as in `lib/typer.ml`) -/

def bool : Ty := .prim "bool"
def int : Ty := .prim "int"

/-- `true`, `false`, `not`, `succ`, `add`, and `if : ∀α. bool → α → α → α`
(`if c then a else b` is parsed as `if c a b`). -/
def builtins : Ctx :=
  [ ("true", .mono bool), ("false", .mono bool),
    ("not", .mono (.arrow bool bool)),
    ("succ", .mono (.arrow int int)),
    ("add", .mono (.arrow int (.arrow int int))),
    ("if", .poly ["a"] (.arrow bool (.arrow (.fvar "a") (.arrow (.fvar "a") (.fvar "a"))))) ]

/-! ## Examples -/

section Examples

/-- A variable bound by a lambda (or a monomorphic `let`) has its type. -/
theorem Typ.var_mono {Γ : Ctx} {x : String} {τ : Ty} (h : Γ.lookup x = some (.mono τ)) : Typ E Γ (.var x) τ :=
  .var h (Scheme.instance_mono τ)

/-- A monomorphic `let`. -/
theorem Typ.letIn_mono {Γ : Ctx} (h₁ : Typ E Γ s σ) (h₂ : Typ E ((x, .mono σ) :: Γ) t τ) :
    Typ E Γ (.letIn false x s t) τ :=
  .letIn (vars := []) h₁ (fun _ h => nomatch h) h₂

/-- A monomorphic `let rec`. -/
theorem Typ.letRec_mono {Γ : Ctx} (h₁ : Typ E ((x, .mono σ) :: Γ) s σ)
    (h₂ : Typ E ((x, .mono σ) :: Γ) t τ) : Typ E Γ (.letIn true x s t) τ :=
  .letRec (vars := []) h₁ (fun _ h => nomatch h) h₂

/-- `twice = fun f -> fun x -> f (f x)` has type `(τ → τ) → τ → τ`, for any `τ`. -/
theorem typ_twice (τ : Ty) :
    Typ E builtins
      (.lam "f" (.lam "x" (.app (.var "f") (.app (.var "f") (.var "x")))))
      (.arrow (.arrow τ τ) (.arrow τ τ)) :=
  .lam (.lam (.app (.var_mono rfl) (.app (.var_mono rfl) (.var_mono rfl))))

/-- `if true then 1 else 2 : int`, instantiating `if` at `int`. -/
theorem typ_if : Typ E builtins
    (.app (.app (.app (.var "if") (.var "true")) (.lit 1)) (.lit 2)) int := by
  have hif : (builtins.lookup "if").isSome := rfl
  refine .app (.app (.app (.var rfl ⟨fun x => if x = "a" then some int else none, ?_, ?_⟩)
    (.var_mono rfl)) .lit) .lit
  · intro x hx
    by_cases h : x = "a"
    · simp [h]
    · simp [h] at hx
  · rfl

/-- The record extension example of Marques et al.:
`((fun r -> r with {y = 2}) {x = 1}).x : int`. The function is used at
`ρ = {x: int}`: its argument `{x = 1}` fits `{y: Abs | {x: int}}`, and
the result `{y: int | {x: int}}` has field `x`. -/
theorem typ_ext :
    Typ E builtins
      (.sel (.app (.lam "r" (.ext (.var "r") [("y", .lit 2)])) (.rcd [("x", .lit 1)])) "x")
      int := by
  -- the row the function is used at
  let ρ : Ty := .record (.cons "x" int .nil) .abs
  have hfun : Typ E builtins (.lam "r" (.ext (.var "r") [("y", .lit 2)]))
      (.arrow (.record (.cons "y" .abs .nil) ρ) (.record (.cons "y" int .nil) ρ)) :=
    .lam (.ext (F := .cons "y" int .nil) (.var_mono rfl) (.cons .lit .nil))
  -- {x: int} ≤ {y: Abs | {x: int}}
  have harg : Sub E (.record (.cons "x" int .nil) .abs) (.record (.cons "y" .abs .nil) ρ) := by
    refine Sub.of_step (.record fun l => ?_)
    by_cases hx : l = "x"
    · subst hx; exact Sub.of_step (show Step E (Sub E) int int from .prim)
    · have hx' : ¬ "x" = l := fun e => hx e.symm
      by_cases hy : l = "y"
      · subst hy; simp only [Ty.field, Fields.lookup, hx', ite_true]; exact Sub.abs
      · have hy' : ¬ "y" = l := fun e => hy e.symm
        simp only [ρ, Ty.field, Fields.lookup, hx', hy', ite_false]; exact Sub.abs
  -- {y: int | {x: int}} ≤ {x: int}
  have hres : Sub E (.record (.cons "y" int .nil) ρ) (.record (.cons "x" int .nil) .abs) := by
    refine Sub.of_step (.record fun l => ?_)
    by_cases hx : l = "x"
    · subst hx; exact Sub.of_step (show Step E (Sub E) int int from .prim)
    · have hx' : ¬ "x" = l := fun e => hx e.symm
      simp only [Ty.field, Fields.lookup, hx', ite_false]
      exact Sub.abs
  exact .sel (.sub (.app hfun (.sub (.rcd (.cons .lit .nil)) harg)) hres)

/-- Let-polymorphism: `let id = fun x -> x in {a = id 1; b = id true}`,
generalizing `id : α → α` and using it at `int` and at `bool`. -/
theorem typ_letPoly (hE : Defs.Avoids E "a") :
    Typ E builtins
      (.letIn false "id" (.lam "x" (.var "x"))
        (.rcd [("a", .app (.var "id") (.lit 1)), ("b", .app (.var "id") (.var "true"))]))
      (.record (.cons "a" int (.cons "b" bool .nil)) .abs) := by
  have inst : ∀ τ : Ty, (Scheme.poly ["a"] (.arrow (.fvar "a") (.fvar "a"))).Instance
      (.arrow τ τ) := fun τ =>
    ⟨fun y => if y = "a" then some τ else none,
      fun y hy => by by_cases h : y = "a" <;> simp_all, by simp [Ty.substM]⟩
  have gen : Gen E builtins ["a"] := by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    refine ⟨?_, hE⟩
    simp [Ctx.Avoids, builtins, Scheme.FreeIn, Scheme.mono, Ty.fv, bool, int]
  exact .letIn (.lam (.var_mono rfl)) gen
    (.rcd (.cons (.app (.var rfl (inst int)) .lit)
      (.cons (.app (.var rfl (inst bool)) (.var_mono rfl)) .nil)))

end Examples

end SimpleSub
