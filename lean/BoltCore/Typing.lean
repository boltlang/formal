import BoltCore.Syntax
import BoltCore.Sub

/-!
# Declarative typing

The type system inferred types are meant to be correct for (the paper's
Fig. 2, extended with integer literals and record extension), over the
minimal subtyping relation of `Sub.lean`. With sorts:

* **Constraints** of a scheme are subtyping at their own sort: a constraint
  between rows is `Sub` at sort `row`, which compares field by field
  (`Step.fields`). There is no field-wise side condition and no flag for
  constraints that only hold field by field.
* **Scheme variables are sorted**, and an instance substitutes at each sort
  (`Subst`), so a type variable is never instantiated with `Abs`.
* **Selection** `t.l : τ` needs `t : {l : pre τ}`: the field is present by
  the shape of the rule, with no `τ ≤ ⊤` premise.

**Schemes are constrained**, as in HM(X): `∀ᾱ. D ⇒ σ`, where `D` is a list
of subtyping constraints on the quantified variables. An instance
substitutes for `ᾱ` such that the constraints hold. `let x = s in t` gives
`x` a scheme when `s` has *every* instance of it, and it has one: the
constraints are read through their instances, as HM(X) defines entailment,
instead of typing `s` under them as hypotheses, since subtyping under both
lower and upper bounds is not transitive in general (the "bad bounds" of
DOT). A monomorphic `let` is the scheme with no variables. There is no
value restriction (no mutable state). Labels in a record literal or a `with` are distinct
(the parser rejects a repeated one in a `with`).
-/

namespace BoltCore

/-! ## Substitution of free variables -/

/-- A substitution of free variables, at each sort. -/
abbrev Subst := (s : Srt) → Nat → Option (Ty s)

def Ty.substM (m : Subst) : {s : Srt} → Ty s → Ty s
  | s, .fvar x => (m s x).getD (.fvar x)
  | _, .top => .top
  | _, .bot => .bot
  | _, .union a b => .union (a.substM m) (b.substM m)
  | _, .inter a b => .inter (a.substM m) (b.substM m)
  | _, .gvar n => .gvar n
  | _, .prim n => .prim n
  | _, .arrow a b => .arrow (a.substM m) (b.substM m)
  | _, .rcd ρ => .rcd (ρ.substM m)
  | _, .cons l θ ρ => .cons l (θ.substM m) (ρ.substM m)
  | _, .pre τ => .pre (τ.substM m)
  | _, .proj l ρ => .proj l (ρ.substM m)

/-- The empty substitution. -/
def Subst.empty : Subst := fun _ _ => Option.none

theorem Ty.substM_none : {s : Srt} → (t : Ty s) → t.substM Subst.empty = t
  | _, .fvar _ | _, .top | _, .bot | _, .gvar _ | _, .prim _ => rfl
  | _, .union a b | _, .inter a b | _, .arrow a b => by
    simp only [Ty.substM, Ty.substM_none a, Ty.substM_none b]
  | _, .rcd ρ | _, .pre ρ | _, .proj _ ρ => by simp only [Ty.substM, Ty.substM_none ρ]
  | _, .cons _ θ ρ => by simp only [Ty.substM, Ty.substM_none θ, Ty.substM_none ρ]

/-! ## Schemes and contexts -/

/-- A constraint `lhs ≤ rhs` of a scheme, at some sort. -/
structure Cstr where
  {s : Srt}
  lhs : Ty s
  rhs : Ty s

/-- `∀ vars. cs ⇒ body`, with constraints `cs` on the quantified variables. -/
structure Scheme where
  poly ::
  vars : List Nat
  cs : List Cstr
  body : Ty .ty

def Scheme.mono (t : Ty .ty) : Scheme := .poly [] [] t

/-- A constraint of a scheme holds after substituting `m`. -/
def SatAfter (E : Defs) (m : Subst) (c : Cstr) : Prop := Sub E (c.lhs.substM m) (c.rhs.substM m)

/-- `τ` is an instance of `σ`: substitute for (some of) its quantified
variables, at any sorts, such that its constraints hold. -/
def Scheme.Instance (E : Defs) (σ : Scheme) (τ : Ty .ty) : Prop :=
  ∃ m : Subst, (∀ s x, (m s x).isSome → x ∈ σ.vars) ∧
    (∀ c ∈ σ.cs, SatAfter E m c) ∧ τ = σ.body.substM m

theorem Scheme.instance_mono (E : Defs) (t : Ty .ty) : (Scheme.mono t).Instance E t :=
  ⟨Subst.empty, by simp [Subst.empty], (fun _ h => nomatch h), (Ty.substM_none t).symm⟩

theorem Scheme.instance_mono_eq {E : Defs} {t τ : Ty .ty} (h : (Scheme.mono t).Instance E τ) :
    τ = t := by
  obtain ⟨m, hdom, _, rfl⟩ := h
  have : m = Subst.empty := funext fun s => funext fun x => by
    cases hx : m s x with
    | none => rfl
    | some _ => exact absurd (hdom s x (by simp [hx])) (by simp [Scheme.mono])
  subst this
  exact Ty.substM_none t

abbrev Ctx := List (String × Scheme)

def Ctx.lookup (Γ : Ctx) (x : String) : Option Scheme := (Γ.find? (·.1 = x)).map (·.2)

/-! ## Typing rules -/

variable {E : Defs}

mutual
inductive Typ (E : Defs) : Ctx → Term → Ty .ty → Prop where
  | lit : Typ E Γ (.lit n) (.prim "int")
  | var : Γ.lookup x = some σ → σ.Instance E τ → Typ E Γ (.var x) τ
  | lam : Typ E ((x, .mono τ₁) :: Γ) t τ₂ → Typ E Γ (.lam x t) (.arrow τ₁ τ₂)
  | app : Typ E Γ f (.arrow τ₁ τ₂) → Typ E Γ a τ₁ → Typ E Γ (.app f a) τ₂
  | rcd : TypFields E Γ fs F → Typ E Γ (.rcd fs) (Ty.record F)
  /-- Selection: the field is present. -/
  | sel : Typ E Γ t (.rcd (.cons l (.pre τ) .top)) → Typ E Γ (.sel t l) τ
  /-- `t with {fs}`: `t`'s fields `fs` may be anything, the rest is `ρ`. -/
  | ext : Typ E Γ t (.rcd (Ty.absFields F ρ)) → TypFields E Γ fs F →
      Typ E Γ (.ext t fs) (.rcd (Ty.ofFields F ρ))
  | extNil : Typ E Γ t τ → Typ E Γ (.ext t []) τ
  | letIn : (∀ τ', σ.Instance E τ' → Typ E Γ s τ') → σ.Instance E τ₀ →
      Typ E ((x, σ) :: Γ) t τ → Typ E Γ (.letIn false x s t) τ
  | letRec : s.IsFun → (∀ τ', σ.Instance E τ' → Typ E ((x, .mono τ') :: Γ) s τ') →
      σ.Instance E τ₀ → Typ E ((x, σ) :: Γ) t τ → Typ E Γ (.letIn true x s t) τ
  | sub : Typ E Γ t τ → Sub E τ τ' → Typ E Γ t τ'

inductive TypFields (E : Defs) : Ctx → List (String × Term) → List (String × Ty .ty) → Prop where
  | nil : TypFields E Γ [] []
  | cons : Typ E Γ t τ → TypFields E Γ fs F → TypFields E Γ ((l, t) :: fs) ((l, τ) :: F)
end

/-! ## Built-ins -/

def bool : Ty .ty := .prim "bool"
def int : Ty .ty := .prim "int"

def builtins : Ctx :=
  [ ("true", .mono bool), ("false", .mono bool),
    ("not", .mono (.arrow bool bool)),
    ("succ", .mono (.arrow int int)),
    ("add", .mono (.arrow int (.arrow int int))),
    ("if", .poly [0] [] (.arrow bool (.arrow (.fvar 0) (.arrow (.fvar 0) (.fvar 0))))) ]

/-! ## Examples -/

section Examples

theorem Typ.var_mono {Γ : Ctx} {x : String} {τ : Ty .ty} (h : Γ.lookup x = some (.mono τ)) :
    Typ E Γ (.var x) τ :=
  .var h (Scheme.instance_mono E τ)

theorem Typ.letIn_mono {Γ : Ctx} {σ τ : Ty .ty} (h₁ : Typ E Γ s σ)
    (h₂ : Typ E ((x, .mono σ) :: Γ) t τ) : Typ E Γ (.letIn false x s t) τ :=
  .letIn (fun _ h => Scheme.instance_mono_eq h ▸ h₁) (Scheme.instance_mono E σ) h₂

theorem Typ.letRec_mono {Γ : Ctx} {σ τ : Ty .ty} (hf : s.IsFun)
    (h₁ : Typ E ((x, .mono σ) :: Γ) s σ) (h₂ : Typ E ((x, .mono σ) :: Γ) t τ) :
    Typ E Γ (.letIn true x s t) τ :=
  .letRec hf (fun _ h => Scheme.instance_mono_eq h ▸ h₁) (Scheme.instance_mono E σ) h₂

theorem typ_twice (τ : Ty .ty) :
    Typ E builtins
      (.lam "f" (.lam "x" (.app (.var "f") (.app (.var "f") (.var "x")))))
      (.arrow (.arrow τ τ) (.arrow τ τ)) :=
  .lam (.lam (.app (.var_mono rfl) (.app (.var_mono rfl) (.var_mono rfl))))

/-- The substitution of one type variable. -/
def Subst.one (x : Nat) (τ : Ty .ty) : Subst := fun s y =>
  match s with
  | .ty => if y = x then some τ else none
  | _ => none

theorem Subst.one_dom {x y : Nat} {τ : Ty .ty} {s : Srt} (h : ((Subst.one x τ) s y).isSome) :
    y = x := by
  cases s <;> simp only [Subst.one] at h
  · by_cases hy : y = x
    · exact hy
    · simp [hy] at h
  all_goals simp at h

theorem typ_if : Typ E builtins
    (.app (.app (.app (.var "if") (.var "true")) (.lit 1)) (.lit 2)) int :=
  .app (.app (.app (.var rfl ⟨Subst.one 0 int, fun _ _ h => by simp [Subst.one_dom h],
    (fun _ h => nomatch h), rfl⟩) (.var_mono rfl)) .lit) .lit

/-- The record extension example of Marques et al.:
`((fun r -> r with {y = 2}) {x = 1}).x : int`, with the function used at the
row `ρ = {x: int}`. -/
theorem typ_ext :
    Typ E builtins
      (.sel (.app (.lam "r" (.ext (.var "r") [("y", .lit 2)])) (.rcd [("x", .lit 1)])) "x")
      int := by
  let ρ : Ty .row := .cons "x" (.pre int) .top
  have hfun : Typ E builtins (.lam "r" (.ext (.var "r") [("y", .lit 2)]))
      (.arrow (.rcd (.cons "y" .abs ρ)) (.rcd (.cons "y" (.pre int) ρ))) :=
    .lam (.ext (F := [("y", int)]) (ρ := ρ) (.var_mono rfl) (.cons .lit .nil))
  have harg : Sub E (Ty.record [("x", int)]) (.rcd (.cons "y" .abs ρ)) := by
    refine Sub.of_step (.rcd (Sub.row fun l => ?_))
    by_cases hx : l = "x"
    · subst hx; simp [Ty.ofFields, Ty.field, ρ]; exact Sub.refl
    · by_cases hy : l = "y"
      · subst hy; simp [Ty.field]; exact Sub.top
      · simp [Ty.ofFields, Ty.field, ρ, Ne.symm hx, Ne.symm hy]; exact Sub.refl
  have hres : Sub E (.rcd (.cons "y" (.pre int) ρ)) (.rcd (.cons "x" (.pre int) .top)) := by
    refine Sub.of_step (.rcd (Sub.row fun l => ?_))
    by_cases hx : l = "x"
    · subst hx; simp [Ty.field, ρ]; exact Sub.refl
    · simp [Ty.field, Ne.symm hx]; exact Sub.top
  exact .sel (.sub (.app hfun (.sub (.rcd (.cons .lit .nil)) harg)) hres)

theorem typ_letPoly :
    Typ E builtins
      (.letIn false "id" (.lam "x" (.var "x"))
        (.rcd [("a", .app (.var "id") (.lit 1)), ("b", .app (.var "id") (.var "true"))]))
      (Ty.record [("a", int), ("b", bool)]) := by
  have inst : ∀ τ : Ty .ty, (Scheme.poly [0] [] (.arrow (.fvar 0) (.fvar 0))).Instance E
      (.arrow τ τ) := fun τ =>
    ⟨Subst.one 0 τ, fun _ _ h => by simp [Subst.one_dom h], (fun _ h => nomatch h),
      by simp [Ty.substM, Subst.one]⟩
  refine .letIn (fun τ' ⟨m, _, _, h⟩ => ?_) (inst int)
    (.rcd (.cons (.app (.var rfl (inst int)) .lit)
      (.cons (.app (.var rfl (inst bool)) (.var_mono rfl)) .nil)))
  subst h
  exact .lam (.var_mono rfl)

/-- A constrained scheme: `inc : ∀α. α ≤ int ⇒ α → int`, used at `int`. -/
theorem typ_letConstrained :
    Typ E builtins
      (.letIn false "inc" (.lam "x" (.app (.var "succ") (.var "x")))
        (.app (.var "inc") (.lit 1)))
      int := by
  let σ : Scheme := .poly [0] [⟨.fvar 0, int⟩] (.arrow (.fvar 0) int)
  have inst : σ.Instance E (.arrow int int) :=
    ⟨Subst.one 0 int, fun _ _ h => by simp [σ, Subst.one_dom h],
      fun c hc => by
        simp only [σ, List.mem_singleton] at hc; subst hc
        simp only [SatAfter, Ty.substM, Subst.one, int]; exact Sub.refl,
      by simp [σ, Ty.substM, Subst.one, int]⟩
  refine .letIn (σ := σ) (fun τ' ⟨m, _, hcs, h⟩ => ?_) inst (.app (.var rfl inst) .lit)
  subst h
  have hc : SatAfter E m ⟨Ty.fvar 0, int⟩ := hcs _ (List.mem_singleton.mpr rfl)
  simp only [SatAfter, Ty.substM] at hc ⊢
  exact .lam (.app (.var_mono rfl) (.sub (.var_mono rfl) hc))

end Examples

/-! ## Selection needs a present field

Selecting a label that a record literal does not have is not typable: the
literal's row gives the label `Abs`, and `Abs ≰ pre τ`. -/

theorem Typ.sel_inv {t : Term} {l : String} : ∀ {Γ : Ctx} {u : Term} {τ : Ty .ty},
    Typ E Γ u τ → u = .sel t l →
    ∃ τ', Typ E Γ t (.rcd (.cons l (.pre τ') .top)) ∧ Sub E τ' τ
  | _, _, _, .sel h, e => by cases e; exact ⟨_, h, Sub.refl⟩
  | _, _, _, .sub h hs, e => let ⟨τ', h₁, h₂⟩ := Typ.sel_inv h e; ⟨τ', h₁, h₂.trans hs⟩
  | _, _, _, .lit, e | _, _, _, .var _ _, e | _, _, _, .lam _, e | _, _, _, .app _ _, e
  | _, _, _, .rcd _, e | _, _, _, .ext _ _, e | _, _, _, .extNil _, e
  | _, _, _, .letIn _ _ _, e | _, _, _, .letRec _ _ _ _, e => nomatch e

theorem Typ.rcd_inv {fs : List (String × Term)} : ∀ {Γ : Ctx} {u : Term} {τ : Ty .ty},
    Typ E Γ u τ → u = .rcd fs → ∃ F, TypFields E Γ fs F ∧ Sub E (Ty.record F) τ
  | _, _, _, .rcd h, e => by cases e; exact ⟨_, h, Sub.refl⟩
  | _, _, _, .sub h hs, e => let ⟨F, hF, hs'⟩ := Typ.rcd_inv h e; ⟨F, hF, hs'.trans hs⟩
  | _, _, _, .lit, e | _, _, _, .var _ _, e | _, _, _, .lam _, e | _, _, _, .app _ _, e
  | _, _, _, .sel _, e | _, _, _, .ext _ _, e | _, _, _, .extNil _, e
  | _, _, _, .letIn _ _ _, e | _, _, _, .letRec _ _ _ _, e => nomatch e

theorem TypFields.labels {Γ : Ctx} {l : String} :
    ∀ {fs : List (String × Term)} {F : List (String × Ty .ty)}, TypFields E Γ fs F →
      (∀ p ∈ fs, p.1 ≠ l) → ∀ p ∈ F, p.1 ≠ l
  | _, _, .nil, _ => fun _ h => nomatch h
  | _, _, .cons (l := l') (t := t) _ h, hl => by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hl (l', t) (List.mem_cons_self ..)
    · exact h.labels (fun q hq => hl q (List.mem_cons_of_mem _ hq)) p hp

/-- Selecting a label that a record literal does not have is not typable. -/
theorem not_typ_sel_missing {Γ : Ctx} {fs : List (String × Term)} {l : String} {τ : Ty .ty}
    (hl : ∀ p ∈ fs, p.1 ≠ l) : ¬ Typ E Γ (.sel (.rcd fs) l) τ := fun h => by
  obtain ⟨τ', h₁, _⟩ := Typ.sel_inv h rfl
  obtain ⟨F, hF, hs⟩ := Typ.rcd_inv h₁ rfl
  cases hs.step with
  | rcd hr =>
    have := hr.fields l
    simp only [Ty.field_ofFields_none (hF.labels hl), Ty.field, ite_true] at this
    exact not_abs_le_pre this

theorem not_typ_empty_sel {Γ : Ctx} {τ : Ty .ty} : ¬ Typ E Γ (.sel (.rcd []) "x") τ :=
  not_typ_sel_missing fun _ h => nomatch h

theorem not_typ_sel_other {Γ : Ctx} {τ : Ty .ty} :
    ¬ Typ E Γ (.sel (.rcd [("a", .lit 1)]) "b") τ :=
  not_typ_sel_missing fun p hp => by simp at hp; subst hp; decide

/-! `Abs` is a field, not a type, so no term has type `Abs`: `⊢ 1 : Abs`
cannot even be stated. -/

end BoltCore
