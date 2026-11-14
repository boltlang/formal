import SimpleSub.Syntax
import SimpleSub.Sub

/-!
# Declarative typing

The type system that inferred types are meant to be correct for (the
paper's Fig. 2, extended with integer literals and record extension), over
the minimal subtyping relation of `Sub.lean`. As in the paper's proof
(Sec. 5), `let` is monomorphic for now; the context nevertheless holds type
*schemes*, so that built-ins such as `if : ∀α. bool → α → α → α` can be
instantiated, and let-polymorphism later only changes the `let` rules.

Quantified variables are free type variables (`fvar`) listed in the scheme;
instantiation substitutes them simultaneously (`Ty.substM`).

`t with {l₁ = e₁, …}` is typed like the OCaml type checker types it: `t`
must be a record whose fields `lᵢ` may be anything (`Abs`) and whose other
fields form some row `ρ`; the result has the new fields over the same `ρ`.
Labels in a `with` are assumed distinct (the OCaml checker keeps the last
binding of a repeated label).
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

def Fields.substM : Fields → (String → Option Ty) → Fields
  | .nil, _ => .nil
  | .cons l f fs, m => .cons l (f.substM m) (fs.substM m)
end

mutual
theorem Ty.substM_none : ∀ t : Ty, t.substM (fun _ => none) = t
  | .fvar _ | .top | .bot | .abs | .prim _ | .bvar _ => rfl
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
  vars : List String
  body : Ty

/-- A monomorphic scheme. -/
def Scheme.mono (t : Ty) : Scheme := ⟨[], t⟩

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

/-! ## Typing rules -/

/-- The same labels, all with the absent field. -/
def Fields.absOf : Fields → Fields
  | .nil => .nil
  | .cons l _ fs => .cons l .abs fs.absOf

mutual
inductive Typ : Ctx → Term → Ty → Prop where
  | lit : Typ Γ (.lit n) (.prim "int")
  | var : Γ.lookup x = some σ → σ.Instance τ → Typ Γ (.var x) τ
  | lam : Typ ((x, .mono τ₁) :: Γ) t τ₂ → Typ Γ (.lam x t) (.arrow τ₁ τ₂)
  | app : Typ Γ f (.arrow τ₁ τ₂) → Typ Γ a τ₁ → Typ Γ (.app f a) τ₂
  | rcd : TypFields Γ fs F → Typ Γ (.rcd fs) (.record F .abs)
  | sel : Typ Γ t (.record (.cons l τ .nil) .abs) → Typ Γ (.sel t l) τ
  /-- `t with {fs}`: `t`'s fields `fs` may be anything, the rest is `ρ`. -/
  | ext : Typ Γ t (.record F.absOf ρ) → TypFields Γ fs F → Typ Γ (.ext t fs) (.record F ρ)
  | letIn : Typ Γ s σ → Typ ((x, .mono σ) :: Γ) t τ → Typ Γ (.letIn false x s t) τ
  | letRec : Typ ((x, .mono σ) :: Γ) s σ → Typ ((x, .mono σ) :: Γ) t τ →
      Typ Γ (.letIn true x s t) τ
  /-- Subsumption. -/
  | sub : Typ Γ t τ → Sub τ τ' → Typ Γ t τ'

/-- Field terms and their types, label by label. -/
inductive TypFields : Ctx → List (String × Term) → Fields → Prop where
  | nil : TypFields Γ [] .nil
  | cons : Typ Γ t τ → TypFields Γ fs F → TypFields Γ ((l, t) :: fs) (.cons l τ F)
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
    ("if", ⟨["a"], .arrow bool (.arrow (.fvar "a") (.arrow (.fvar "a") (.fvar "a")))⟩) ]

/-! ## Examples -/

section Examples

/-- A variable bound by a lambda (or a monomorphic `let`) has its type. -/
theorem Typ.var_mono (h : Γ.lookup x = some (.mono τ)) : Typ Γ (.var x) τ :=
  .var h (Scheme.instance_mono τ)

/-- `twice = fun f -> fun x -> f (f x)` has type `(τ → τ) → τ → τ`, for any `τ`. -/
theorem typ_twice (τ : Ty) :
    Typ builtins
      (.lam "f" (.lam "x" (.app (.var "f") (.app (.var "f") (.var "x")))))
      (.arrow (.arrow τ τ) (.arrow τ τ)) :=
  .lam (.lam (.app (.var_mono rfl) (.app (.var_mono rfl) (.var_mono rfl))))

/-- `if true then 1 else 2 : int`, instantiating `if` at `int`. -/
theorem typ_if : Typ builtins
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
    Typ builtins
      (.sel (.app (.lam "r" (.ext (.var "r") [("y", .lit 2)])) (.rcd [("x", .lit 1)])) "x")
      int := by
  -- the row the function is used at
  let ρ : Ty := .record (.cons "x" int .nil) .abs
  have hfun : Typ builtins (.lam "r" (.ext (.var "r") [("y", .lit 2)]))
      (.arrow (.record (.cons "y" .abs .nil) ρ) (.record (.cons "y" int .nil) ρ)) :=
    .lam (.ext (F := .cons "y" int .nil) (.var_mono rfl) (.cons .lit .nil))
  -- {x: int} ≤ {y: Abs | {x: int}}
  have harg : Sub (.record (.cons "x" int .nil) .abs) (.record (.cons "y" .abs .nil) ρ) := by
    refine Sub.of_step (.record fun l => ?_)
    by_cases hx : l = "x"
    · subst hx; exact Sub.of_step (show Step Sub int int from .prim)
    · have hx' : ¬ "x" = l := fun e => hx e.symm
      by_cases hy : l = "y"
      · subst hy; simp only [Ty.field, Fields.lookup, hx', ite_true]; exact Sub.abs
      · have hy' : ¬ "y" = l := fun e => hy e.symm
        simp only [ρ, Ty.field, Fields.lookup, hx', hy', ite_false]; exact Sub.abs
  -- {y: int | {x: int}} ≤ {x: int}
  have hres : Sub (.record (.cons "y" int .nil) ρ) (.record (.cons "x" int .nil) .abs) := by
    refine Sub.of_step (.record fun l => ?_)
    by_cases hx : l = "x"
    · subst hx; exact Sub.of_step (show Step Sub int int from .prim)
    · have hx' : ¬ "x" = l := fun e => hx e.symm
      simp only [Ty.field, Fields.lookup, hx', ite_false]
      exact Sub.abs
  exact .sel (.sub (.app hfun (.sub (.rcd (.cons .lit .nil)) harg)) hres)

end Examples

end SimpleSub
