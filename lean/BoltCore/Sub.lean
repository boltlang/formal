import BoltCore.Types

/-!
# Declarative subtyping

`Step E R` is one layer of subtyping,
defined inductively, using the coinductive hypothesis `R` only under a
function type or a record (the paper's `▷`/`◁`), and `Sub` is its greatest
fixed point (Knaster–Tarski), with the coinduction principle `Sub.coind`.
Graph variables (`gvar`) are defined by sets of upper bounds (`Defs`):
named, possibly mutually recursive definitions without binders, which is
how solutions are expressed. With sorts:

* `⊤` is the top of every sort, with no side condition. At sort `field` it
  is `Abs`: `pre τ ≤ Abs` is an instance of the `top` rule, and nothing
  derives `Abs ≤ pre τ` (`not_abs_le_pre`). So `Abs` is strictly above every
  present field, `pre ⊤` included, by the shape of the rules.
* Rows are compared label by label, in one layer (`row`), and records
  compare their rows under the hypothesis (`rcd`). Every comparison of rows
  holds field by field (`Step.fields`), so a constraint between rows needs no
  separate field-wise reading.
* Fields: `pre τ₁ ≤ pre τ₂` when `τ₁ ≤ τ₂` (S-Pre), in the same layer.

Cut elimination splits by sort. For types and fields it is an induction on
the two finite derivations (`cut_nr`, through a *pending cut*, `Pend`):
their derivations never compare rows, since rows only occur under `rcd`,
i.e. under the hypothesis. Rows are then cut field by field. The MLsub
lattice equations are not included (`Lattice.lean`).
-/

namespace BoltCore

/-- Definitions of graph variables, by sort: `gvar n` at sort `s` stands for
the intersection of the `u` with `E s n u`. -/
abbrev Defs := (s : Srt) → Nat → Ty s → Prop

/-- Relations between terms of the same sort. -/
abbrev Rel := (s : Srt) → Ty s → Ty s → Prop

variable {E : Defs}

/-- Definitions without recursive types: definitions only mention graph
variables of strictly lower rank. -/
def Defs.Ranked (E : Defs) (r : Nat → Nat) : Prop :=
  ∀ s n (u : Ty s), E s n u → ∀ m ∈ u.gvars, r m < r n

/-- Atoms: variables, primitives, opaque fields and the missing field. -/
def Ty.IsAtom : Ty s → Prop
  | .fvar _ | .gvar _ | .prim _ | .proj _ _ | .missing => True
  | _ => False

/-- One layer of subtyping, relative to the coinductive hypothesis `R`. -/
inductive Step (E : Defs) (R : Rel) : {s : Srt} → Ty s → Ty s → Prop where
  | top : Step E R a .top
  | bot : Step E R .bot b
  | unionL : Step E R a₁ b → Step E R a₂ b → Step E R (.union a₁ a₂) b
  | unionR₁ : Step E R a b₁ → Step E R a (.union b₁ b₂)
  | unionR₂ : Step E R a b₂ → Step E R a (.union b₁ b₂)
  | interL₁ : Step E R a₁ b → Step E R (.inter a₁ a₂) b
  | interL₂ : Step E R a₂ b → Step E R (.inter a₁ a₂) b
  | interR : Step E R a b₁ → Step E R a b₂ → Step E R a (.inter b₁ b₂)
  | fvar : Step E R (.fvar x : Ty s) (.fvar x)
  /-- A graph variable is related to itself. -/
  | gvar : Step E R (.gvar n : Ty s) (.gvar n)
  /-- A graph variable is below each of its upper bounds (like `interL`). -/
  | defL : E s n u → Step E R u b → Step E R (.gvar n) b
  /-- Below all upper bounds of a graph variable is below it (like `interR`). -/
  | defR : (∀ u, E s n u → Step E R a u) → Step E R a (.gvar n)
  | prim : Step E R (.prim n) (.prim n)
  /-- Function types: the hypothesis `R` becomes usable here (◁). -/
  | arrow : R .ty b₁ a₁ → R .ty a₂ b₂ → Step E R (.arrow a₁ a₂) (.arrow b₁ b₂)
  /-- Records compare their rows under the hypothesis (◁). -/
  | rcd : R .row ρ₁ ρ₂ → Step E R (.rcd ρ₁) (.rcd ρ₂)
  /-- Rows are compared label by label. -/
  | row {ρ₁ ρ₂ : Ty .row} : (∀ l, Step E R (ρ₁.field l) (ρ₂.field l)) → Step E R ρ₁ ρ₂
  /-- S-Pre. -/
  | pre : Step E R τ₁ τ₂ → Step E R (.pre τ₁) (.pre τ₂)
  /-- A field of an opaque row is only known to be itself. -/
  | proj : Step E R (.proj l ρ) (.proj l ρ)
  /-- The field of a graph row variable, through its definitions. -/
  | projDefL {u : Ty .row} {b : Ty .field} : E .row n u → Step E R (u.field l) b →
      Step E R (.proj l (.gvar n)) b
  | projDefR {a : Ty .field} : (∀ u : Ty .row, E .row n u → Step E R a (u.field l)) →
      Step E R a (.proj l (.gvar n))
  /-- The missing field is only below itself (and `Abs`, by `top`). -/
  | missing : Step E R .missing .missing

theorem Step.mono {R R' : Rel} (hR : ∀ s x y, R s x y → R' s x y) {s : Srt} {a b : Ty s} :
    Step E R a b → Step E R' a b := by
  intro h
  induction h with
  | top => exact .top
  | bot => exact .bot
  | unionL _ _ ih₁ ih₂ => exact .unionL ih₁ ih₂
  | unionR₁ _ ih => exact .unionR₁ ih
  | unionR₂ _ ih => exact .unionR₂ ih
  | interL₁ _ ih => exact .interL₁ ih
  | interL₂ _ ih => exact .interL₂ ih
  | interR _ _ ih₁ ih₂ => exact .interR ih₁ ih₂
  | fvar => exact .fvar
  | gvar => exact .gvar
  | defL hd _ ih => exact .defL hd ih
  | defR _ ih => exact .defR ih
  | prim => exact .prim
  | arrow h₁ h₂ => exact .arrow (hR _ _ _ h₁) (hR _ _ _ h₂)
  | rcd h => exact .rcd (hR _ _ _ h)
  | row _ ih => exact .row ih
  | pre _ ih => exact .pre ih
  | proj => exact .proj
  | projDefL hd _ ih => exact .projDefL hd ih
  | projDefR _ ih => exact .projDefR ih
  | missing => exact .missing

/-- **Rows compare field by field**: every comparison of rows, by any rule,
gives one between each pair of fields. -/
theorem Step.fields {R : Rel} {s : Srt} {a b : Ty s} (h : Step E R a b) (l : String) :
    Step E R (a.field l) (b.field l) := by
  induction h with
  | top => cases ‹Srt› <;> simp only [Ty.field] <;> exact .top
  | bot => cases ‹Srt› <;> simp only [Ty.field] <;> first | exact .top | exact .bot
  | unionL _ _ ih₁ ih₂ =>
    cases ‹Srt› <;> simp only [Ty.field] at * <;> first | exact .top | exact .unionL ih₁ ih₂
  | unionR₁ _ ih =>
    cases ‹Srt› <;> simp only [Ty.field] at * <;> first | exact .top | exact .unionR₁ ih
  | unionR₂ _ ih =>
    cases ‹Srt› <;> simp only [Ty.field] at * <;> first | exact .top | exact .unionR₂ ih
  | interL₁ _ ih =>
    cases ‹Srt› <;> simp only [Ty.field] at * <;> first | exact .top | exact .interL₁ ih
  | interL₂ _ ih =>
    cases ‹Srt› <;> simp only [Ty.field] at * <;> first | exact .top | exact .interL₂ ih
  | interR _ _ ih₁ ih₂ =>
    cases ‹Srt› <;> simp only [Ty.field] at * <;> first | exact .top | exact .interR ih₁ ih₂
  | fvar => cases ‹Srt› <;> simp only [Ty.field] <;> first | exact .top | exact .proj
  | gvar => cases ‹Srt› <;> simp only [Ty.field] <;> first | exact .top | exact .proj
  | defL hd _ ih =>
    cases ‹Srt› <;> simp only [Ty.field] at * <;> first | exact .top | exact .projDefL hd ih
  | defR _ ih =>
    cases ‹Srt› <;> simp only [Ty.field] at * <;> first | exact .top | exact .projDefR ih
  | prim | arrow | rcd | pre | proj | projDefL | projDefR | missing =>
    first | exact .top | (simp only [Ty.field]; exact .top)
  | row h _ => exact h l

/-! ## The greatest fixed point -/

/-- Subtyping: the greatest fixed point of `Step`. -/
def Sub (E : Defs) {s : Srt} (a b : Ty s) : Prop :=
  ∃ R : Rel, (∀ s x y, R s x y → Step E R x y) ∧ R s a b

/-- `Sub` as a relation at every sort. -/
abbrev SubR (E : Defs) : Rel := fun _ a b => Sub E a b

theorem Sub.coind (R : Rel) (hR : ∀ s x y, R s x y → Step E R x y) {s : Srt} {a b : Ty s}
    (h : R s a b) : Sub E a b :=
  ⟨R, hR, h⟩

theorem Sub.step {s : Srt} {a b : Ty s} (h : Sub E a b) : Step E (SubR E) a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact (hR _ _ _ hab).mono (fun _ _ _ hxy => ⟨R, hR, hxy⟩)

theorem Sub.of_step {s : Srt} {a b : Ty s} (h : Step E (SubR E) a b) : Sub E a b := by
  refine ⟨fun s' x y => Sub E x y ∨ (∃ e : s' = s, e ▸ x = a ∧ e ▸ y = b), ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  have up : ∀ s' (x y : Ty s'), Sub E x y →
      Sub E x y ∨ (∃ e : s' = s, e ▸ x = a ∧ e ▸ y = b) := fun _ _ _ h => Or.inl h
  rintro s' x y (hs | ⟨rfl, rfl, rfl⟩)
  · exact hs.step.mono up
  · exact h.mono up

theorem Sub.top {s : Srt} {a : Ty s} : Sub E a .top := Sub.of_step .top
theorem Sub.bot {s : Srt} {b : Ty s} : Sub E .bot b := Sub.of_step .bot

/-- Rows related by subtyping are related field by field. -/
theorem Sub.fields {a b : Ty .row} (h : Sub E a b) (l : String) : Sub E (a.field l) (b.field l) :=
  Sub.of_step (h.step.fields l)

/-- Rows related field by field are related. -/
theorem Sub.row {a b : Ty .row} (h : ∀ l, Sub E (a.field l) (b.field l)) : Sub E a b :=
  Sub.of_step (.row fun l => (h l).step)

/-! ## Reflexivity -/

theorem step_refl : {s : Srt} → (t : Ty s) → Step E (fun _ => Eq) t t
  | _, .top => .top
  | _, .bot => .bot
  | _, .union a b => .unionL (.unionR₁ (step_refl a)) (.unionR₂ (step_refl b))
  | _, .inter a b => .interR (.interL₁ (step_refl a)) (.interL₂ (step_refl b))
  | _, .fvar _ => .fvar
  | _, .gvar _ => .gvar
  | _, .prim _ => .prim
  | _, .arrow _ _ => .arrow rfl rfl
  | _, .rcd _ => .rcd rfl
  | _, .cons l θ ρ => .row fun l' => by
      simp only [Ty.field]
      split
      · exact step_refl θ
      · exact (step_refl ρ).fields l'
  | _, .pre τ => .pre (step_refl τ)
  | _, .proj _ _ => .proj
  | _, .missing => .missing
  | _, .nil => .row fun _ => .missing

theorem Sub.refl {s : Srt} {t : Ty s} : Sub E t t :=
  Sub.coind (fun _ => Eq) (by rintro _ x y rfl; exact step_refl x) rfl

/-! ## Transitivity -/

/-- A relation, or its composition with itself. -/
def RComp (R : Rel) : Rel := fun _ x z => R _ x z ∨ ∃ y, R _ x y ∧ R _ y z

section Cut

variable {R : Rel}

theorem Step.toComp {s : Srt} {a b : Ty s} (h : Step E R a b) : Step E (RComp R) a b :=
  h.mono fun _ _ _ h => .inl h

/-- A *pending cut*: `x ≤ y` was derived by a rule that takes `y` apart (or
`y` is an atom equal to `x`, or `⊤`), with what is needed to cut it against
any derivation from `y`: the induction hypotheses for the smaller
derivations, or the guarded premises. -/
inductive Pend (E : Defs) (R : Rel) : {s : Srt} → Ty s → Ty s → Prop where
  | top : Pend E R x .top
  | atom : x.IsAtom → Pend E R x x
  | unionR₁ : (∀ z, Step E R y₁ z → Step E (RComp R) x z) → Pend E R x (.union y₁ y₂)
  | unionR₂ : (∀ z, Step E R y₂ z → Step E (RComp R) x z) → Pend E R x (.union y₁ y₂)
  | interR : (∀ z, Step E R y₁ z → Step E (RComp R) x z) →
      (∀ z, Step E R y₂ z → Step E (RComp R) x z) → Pend E R x (.inter y₁ y₂)
  | defR : (∀ u, E s n u → Step E R x u) →
      (∀ u, E s n u → ∀ z, Step E R u z → Step E (RComp R) x z) → Pend E R x (.gvar n)
  | projDefR {x : Ty .field} : (∀ u : Ty .row, E .row n u → Step E R x (u.field l)) →
      (∀ u : Ty .row, E .row n u → ∀ z, Step E R (u.field l) z → Step E (RComp R) x z) →
      Pend E R x (.proj l (.gvar n))
  | arrow : R .ty b₁ a₁ → R .ty a₂ b₂ → Pend E R (.arrow a₁ a₂) (.arrow b₁ b₂)
  | rcd : R .row ρ₁ ρ₂ → Pend E R (.rcd ρ₁) (.rcd ρ₂)
  | pre : (∀ z, Step E R τ₂ z → Step E (RComp R) τ₁ z) → Pend E R (.pre τ₁) (.pre τ₂)

/-- A pending cut against a derivation from `y`, at a sort other than `row`,
by induction on that derivation: rules that take `z` apart commute outward,
and the rule that takes `y` apart meets the matching pending rule. -/
theorem cut_right {s : Srt} {y z : Ty s} (h : Step E R y z) :
    s ≠ .row → ∀ {x}, Pend E R x y → Step E (RComp R) x z := by
  induction h with
  | top => intro _ _ _; exact .top
  | unionR₁ _ ih => intro hs _ hp; exact .unionR₁ (ih hs hp)
  | unionR₂ _ ih => intro hs _ hp; exact .unionR₂ (ih hs hp)
  | interR _ _ ih₁ ih₂ => intro hs _ hp; exact .interR (ih₁ hs hp) (ih₂ hs hp)
  | defR _ ih => intro hs _ hp; exact .defR fun u hu => ih u hu hs hp
  | projDefR _ ih => intro _ _ hp; exact .projDefR fun u hu => ih u hu (by decide) hp
  | row => intro hs; exact absurd rfl hs
  | bot => intro _ _ hp; cases hp with | atom h => simp [Ty.IsAtom] at h
  | fvar => intro _ _ hp; cases hp with | atom => exact .fvar
  | prim => intro _ _ hp; cases hp with | atom => exact .prim
  | gvar => intro _ _ hp; cases hp with
    | atom => exact .gvar
    | defR hl _ => exact (Step.defR hl).toComp
  | proj => intro _ _ hp; cases hp with
    | atom => exact .proj
    | projDefR hl _ => exact (Step.projDefR hl).toComp
  | missing => intro _ _ hp; cases hp with | atom => exact .missing
  | unionL h₁ h₂ _ _ => intro _ _ hp; cases hp with
    | atom h => simp [Ty.IsAtom] at h
    | unionR₁ ih => exact ih _ h₁
    | unionR₂ ih => exact ih _ h₂
  | interL₁ h _ => intro _ _ hp; cases hp with
    | atom h => simp [Ty.IsAtom] at h
    | interR ih _ => exact ih _ h
  | interL₂ h _ => intro _ _ hp; cases hp with
    | atom h => simp [Ty.IsAtom] at h
    | interR _ ih => exact ih _ h
  | defL hd h _ => intro _ _ hp; cases hp with
    | atom => exact (Step.defL hd h).toComp
    | defR _ ih => exact ih _ hd _ h
  | projDefL hd h _ => intro _ _ hp; cases hp with
    | atom => exact (Step.projDefL hd h).toComp
    | projDefR _ ih => exact ih _ hd _ h
  | arrow g₁ g₂ => intro _ _ hp; cases hp with
    | atom h => simp [Ty.IsAtom] at h
    | arrow h₁ h₂ => exact .arrow (.inr ⟨_, g₁, h₁⟩) (.inr ⟨_, h₂, g₂⟩)
  | rcd g => intro _ _ hp; cases hp with
    | atom h => simp [Ty.IsAtom] at h
    | rcd h => exact .rcd (.inr ⟨_, h, g⟩)
  | pre g => intro _ _ hp; cases hp with
    | atom h => simp [Ty.IsAtom] at h
    | pre ih => exact .pre (ih _ g)

/-- Cut for one layer, at the sorts of types and fields (whose derivations
never compare rows), by induction on the left derivation. -/
theorem cut_nr {s : Srt} {x y : Ty s} (hl : Step E R x y) :
    s ≠ .row → ∀ z, Step E R y z → Step E (RComp R) x z := by
  induction hl with
  | top => intro hs z hr; exact cut_right hr hs .top
  | bot => intro _ _ _; exact .bot
  | fvar => intro hs z hr; exact cut_right hr hs (.atom trivial)
  | gvar => intro hs z hr; exact cut_right hr hs (.atom trivial)
  | prim => intro hs z hr; exact cut_right hr hs (.atom trivial)
  | proj => intro hs z hr; exact cut_right hr hs (.atom trivial)
  | missing => intro hs z hr; exact cut_right hr hs (.atom trivial)
  | unionL _ _ ih₁ ih₂ => intro hs z hr; exact .unionL (ih₁ hs z hr) (ih₂ hs z hr)
  | unionR₁ _ ih => intro hs z hr; exact cut_right hr hs (.unionR₁ (ih hs))
  | unionR₂ _ ih => intro hs z hr; exact cut_right hr hs (.unionR₂ (ih hs))
  | interL₁ _ ih => intro hs z hr; exact .interL₁ (ih hs z hr)
  | interL₂ _ ih => intro hs z hr; exact .interL₂ (ih hs z hr)
  | interR _ _ ih₁ ih₂ => intro hs z hr; exact cut_right hr hs (.interR (ih₁ hs) (ih₂ hs))
  | defL hd _ ih => intro hs z hr; exact .defL hd (ih hs z hr)
  | defR hl ih => intro hs z hr; exact cut_right hr hs (.defR hl fun u hu => ih u hu hs)
  | arrow h₁ h₂ => intro hs z hr; exact cut_right hr hs (.arrow h₁ h₂)
  | rcd h => intro hs z hr; exact cut_right hr hs (.rcd h)
  | row => intro hs; exact absurd rfl hs
  | pre _ ih => intro hs z hr; exact cut_right hr hs (.pre (ih (by decide)))
  | projDefL hd _ ih => intro _ z hr; exact .projDefL hd (ih (by decide) z hr)
  | projDefR hl ih =>
    intro hs z hr; exact cut_right hr hs (.projDefR hl fun u hu => ih u hu (by decide))

/-- **Cut elimination for one layer**, at every sort: rows are cut field by
field. -/
theorem cut {s : Srt} {x y z : Ty s} (hl : Step E R x y) (hr : Step E R y z) :
    Step E (RComp R) x z := by
  cases s with
  | row => exact .row fun l => cut_nr (hl.fields l) (by decide) _ (hr.fields l)
  | ty => exact cut_nr hl (by decide) z hr
  | field => exact cut_nr hl (by decide) z hr

end Cut

/-- **Transitivity** of subtyping. -/
theorem Sub.trans {s : Srt} {a b c : Ty s} (hab : Sub E a b) (hbc : Sub E b c) : Sub E a c := by
  refine Sub.coind (RComp (SubR E)) ?_ (.inr ⟨b, hab, hbc⟩)
  rintro _ x z (h | ⟨_, hxy, hyz⟩)
  · exact h.step.toComp
  · exact cut hxy.step hyz.step

/-! ## `Abs` is strictly above every present field -/

/-- `Abs ≰ pre τ`: no rule derives it. -/
theorem not_abs_le_pre {τ : Ty .ty} : ¬ Sub E Ty.abs (.pre τ) := fun h => by
  cases h.step

/-- Nothing above `Abs` is below a present field. -/
theorem not_abs_le_of_le_pre {θ : Ty .field} {τ : Ty .ty} (h : Sub E θ (.pre τ)) :
    ¬ Sub E Ty.abs θ :=
  fun h' => not_abs_le_pre (h'.trans h)

/-! ## The field lattice: `pre τ ≤ opt τ`, `missing ≤ opt τ`, `opt τ ≤ Abs`

`missing` is the field that is definitely absent, and an optional field is
the union `opt τ = pre τ ∪ missing`, so its rules are those of unions. A
field that is or may be missing is not below a present one, a field that is
or may be present is not below `missing`, and `Abs` (no guarantee) is below
neither `missing` nor an optional field. -/

theorem pre_le_opt {τ : Ty .ty} : Sub E (.pre τ) (Ty.opt τ) :=
  Sub.of_step (.unionR₁ (Sub.refl (t := Ty.pre τ)).step)

theorem missing_le_opt {τ : Ty .ty} : Sub E .missing (Ty.opt τ) :=
  Sub.of_step (.unionR₂ .missing)

theorem opt_le_abs {τ : Ty .ty} : Sub E (Ty.opt τ) Ty.abs := Sub.top

theorem missing_le_abs : Sub E .missing Ty.abs := Sub.top

/-- `opt` is monotone. -/
theorem opt_le_opt {τ τ' : Ty .ty} (h : Sub E τ τ') : Sub E (Ty.opt τ) (Ty.opt τ') :=
  Sub.of_step (.unionL (.unionR₁ (.pre h.step)) (.unionR₂ .missing))

/-- A present field below an optional one: `pre τ ≤ opt τ'` when `τ ≤ τ'`. -/
theorem pre_le_opt_of_le {τ τ' : Ty .ty} (h : Sub E τ τ') : Sub E (.pre τ) (Ty.opt τ') :=
  Sub.of_step (.unionR₁ (.pre h.step))

/-- `missing ≰ pre τ`: a missing field does not satisfy a present one. -/
theorem not_missing_le_pre {τ : Ty .ty} : ¬ Sub E .missing (.pre τ) := fun h => by
  cases h.step

/-- `pre τ ≰ missing`: a present field is not missing. -/
theorem not_pre_le_missing {τ : Ty .ty} : ¬ Sub E (.pre τ) .missing := fun h => by
  cases h.step

/-- `opt τ ≰ pre σ`: an optional field does not satisfy a present one. -/
theorem not_opt_le_pre {τ σ : Ty .ty} : ¬ Sub E (Ty.opt τ) (.pre σ) := fun h => by
  cases h.step with
  | unionL _ h₂ => cases h₂

/-- `opt τ ≰ missing`. -/
theorem not_opt_le_missing {τ : Ty .ty} : ¬ Sub E (Ty.opt τ) .missing := fun h => by
  cases h.step with
  | unionL h₁ _ => cases h₁

/-- `Abs ≰ missing`: a field nothing is known about is not known to be
missing. -/
theorem not_abs_le_missing : ¬ Sub E Ty.abs .missing := fun h => by
  cases h.step

/-- `Abs ≰ opt τ`: a forgotten field cannot be passed as an optional one. -/
theorem not_abs_le_opt {τ : Ty .ty} : ¬ Sub E Ty.abs (Ty.opt τ) := fun h => by
  cases h.step with
  | unionR₁ h => cases h
  | unionR₂ h => cases h

/-! ## Coinduction up to transitivity -/

/-- The transitive closure of a relation, at each sort. -/
inductive TC (R : Rel) : Rel where
  | base : R s x y → TC R s x y
  | trans : TC R s x y → TC R s y z → TC R s x z

theorem TC.step {R : Rel} (hR : ∀ s x y, R s x y → Step E (TC R) x y) {s : Srt} {a b : Ty s} :
    TC R s a b → Step E (TC R) a b := by
  intro h
  induction h with
  | base h => exact hR _ _ _ h
  | trans _ _ ih₁ ih₂ =>
    refine (cut ih₁ ih₂).mono fun _ _ _ h => ?_
    rcases h with h | ⟨_, h₁, h₂⟩
    · exact h
    · exact .trans h₁ h₂

/-- **Coinduction up to transitivity.** -/
theorem Sub.coind_trans (R : Rel) (hR : ∀ s x y, R s x y → Step E (TC R) x y) {s : Srt}
    {a b : Ty s} (h : R s a b) : Sub E a b :=
  Sub.coind (TC R) (fun _ _ _ h => TC.step hR h) (.base h)

/-! ## The paper's example (Sec. 5.1.3), with graph variables -/

namespace PaperExample

def τ : Ty .ty := .prim "t"
def A : Ty .ty := .gvar 0
def B : Ty .ty := .gvar 1

/-- `A` is defined as `τ → τ → A`, `B` as `τ → B`. -/
def E₀ : Defs := fun s n t =>
  ∃ e : s = .ty, (n = 0 ∧ e ▸ t = .arrow τ (.arrow τ A)) ∨ (n = 1 ∧ e ▸ t = .arrow τ B)

theorem paper_example : Sub E₀ A B := by
  refine Sub.coind
    (fun s x y => ∃ e : s = .ty,
      (e ▸ x = A ∧ e ▸ y = B) ∨ (e ▸ x = .arrow τ A ∧ e ▸ y = B) ∨ (e ▸ x = τ ∧ e ▸ y = τ))
    ?_ ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  rintro s x y ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · refine .defR fun u hu => ?_
    obtain ⟨_, ⟨h, _⟩ | ⟨_, rfl⟩⟩ := hu
    · exact absurd h (by decide)
    · exact .defL ⟨rfl, .inl ⟨rfl, rfl⟩⟩
        (.arrow ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩)
  · refine .defR fun u hu => ?_
    obtain ⟨_, ⟨h, _⟩ | ⟨_, rfl⟩⟩ := hu
    · exact absurd h (by decide)
    · exact .arrow ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩ ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  · exact .prim

end PaperExample

/-! ## Rows -/

section Rows

private def bool : Ty .ty := .prim "bool"
private def int : Ty .ty := .prim "int"

/-- A field hidden in a compound tail: `{ | 'b ∧ {done: bool}} ≤ {done: bool}`,
the shape the simplifier produces for `count`. -/
theorem field_in_compound_tail :
    Sub E (.rcd (.inter (.fvar 0) (.cons "done" (.pre bool) .top)))
        (.rcd (.cons "done" (.pre bool) .top)) := by
  refine Sub.of_step (.rcd (Sub.row fun l => ?_))
  by_cases h : l = "done"
  · subst h
    exact Sub.of_step (.interL₂ (by simp only [Ty.field, ite_true]; exact .pre .prim))
  · have h' : ¬ "done" = l := fun e => h e.symm
    simp only [Ty.field, h', ite_false]
    exact Sub.top

/-- The bottom row gives every field `⊥`: `{ | ⊥} ≤ {x: int}`. -/
theorem bottom_tail : Sub E (.rcd .bot) (.rcd (.cons "x" (.pre int) .top)) :=
  Sub.of_step (.rcd (Sub.row fun _ => Sub.bot))

/-- `{..} ≰ {x: int, ..}`: the field `x` of the top record is `Abs`. -/
theorem not_empty_le_field : ¬ Sub E (.rcd .top) (.rcd (.cons "x" (.pre int) .top)) := by
  intro h
  cases h.step with
  | rcd hr =>
    have := hr.fields "x"
    simp only [Ty.field, ite_true] at this
    exact not_abs_le_pre this

/-- Width subtyping is kept: the empty row is below the top row, so a closed
record is below the open one with the same fields. -/
theorem nil_le_top : Sub E Ty.nil (.top : Ty .row) := Sub.top

/-- `{x: int} ≤ {x: int, y?: int}`: an optional field can be left out. -/
theorem closed_le_optional :
    Sub E (.rcd (.cons "x" (.pre int) .nil))
        (.rcd (.cons "x" (.pre int) (.cons "y" (Ty.opt int) .nil))) := by
  refine Sub.of_step (.rcd (Sub.row fun l => ?_))
  by_cases hx : l = "x"
  · subst hx; simp only [Ty.field, ite_true]; exact Sub.refl
  · by_cases hy : l = "y"
    · subst hy
      simp only [Ty.field, show ¬ "x" = "y" by decide, ite_true, ite_false]
      exact missing_le_opt
    · simp only [Ty.field, Ne.symm hx, Ne.symm hy, ite_false]; exact Sub.refl

/-- `{x: int, z: int} ≰ {x: int}`: a closed record has no other fields. -/
theorem not_extra_le_closed :
    ¬ Sub E (.rcd (.cons "x" (.pre int) (.cons "z" (.pre int) .nil)))
        (.rcd (.cons "x" (.pre int) .nil)) := by
  intro h
  cases h.step with
  | rcd hr =>
    have := hr.fields "z"
    simp only [Ty.field, show ¬ "x" = "z" by decide, ite_true, ite_false] at this
    exact not_pre_le_missing this

/-- `{..} ≰ {}`: a record that may have other fields is not closed. -/
theorem not_top_le_nil : ¬ Sub E (.rcd .top) (.rcd .nil) := by
  intro h
  cases h.step with
  | rcd hr =>
    have := hr.fields "x"
    simp only [Ty.field] at this
    exact not_abs_le_missing this

end Rows

/-! ## Unions of lists

The domain of a parameter list is a union of argument records (`Ty.sig`):
a type is below it when it is below one of them, and it is below a type
when each of them is. -/

theorem Step.unionsR {R : Rel} {s : Srt} {x a : Ty s} :
    ∀ {l : List (Ty s)}, a ∈ l → Step E R x a → Step E R x (Ty.unions l)
  | [], h, _ => nomatch h
  | [b], h, hs => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hs
    · exact nomatch h
  | b :: c :: l, h, hs => by
    rcases List.mem_cons.mp h with rfl | h
    · exact .unionR₁ hs
    · exact .unionR₂ (Step.unionsR h hs)

theorem Step.unionsL {R : Rel} {s : Srt} {y : Ty s} :
    ∀ {l : List (Ty s)}, (∀ a ∈ l, Step E R a y) → Step E R (Ty.unions l) y
  | [], _ => .bot
  | [a], h => h a (List.mem_cons_self ..)
  | a :: _ :: _, h =>
    .unionL (h a (List.mem_cons_self ..)) (Step.unionsL fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem Sub.unionsR {s : Srt} {x a : Ty s} {l : List (Ty s)} (ha : a ∈ l) (h : Sub E x a) :
    Sub E x (Ty.unions l) :=
  Sub.of_step (Step.unionsR ha h.step)

theorem Sub.unionsL {s : Srt} {y : Ty s} {l : List (Ty s)} (h : ∀ a ∈ l, Sub E a y) :
    Sub E (Ty.unions l) y :=
  Sub.of_step (Step.unionsL fun a ha => (h a ha).step)

/-- The field of a union of rows is the union of the fields. -/
theorem Ty.field_unions (l : String) : ∀ rows : List (Ty .row),
    (Ty.unions rows).field l = Ty.unions (rows.map (·.field l))
  | [] => rfl
  | [_] => rfl
  | a :: b :: rows => by
    have ih := Ty.field_unions l (b :: rows)
    simp only [Ty.unions, Ty.field, List.map_cons] at ih ⊢
    rw [ih]

end BoltCore
