import SimpleSub.Types

/-!
# Declarative subtyping with equi-recursive types

Subtyping between recursive types must be coinductive (two recursive types
are related if no finite amount of unfolding finds a difference), but only
in a *guarded* way: unfolding `mu`, splitting unions and intersections and
comparing row tails may happen only finitely often between two type
constructors, otherwise `μα. α` would be related to everything. This is the
formal content of the paper's `▷`/`◁` discipline (Fig. 10), where an
assumption only becomes usable after passing through a function or record
type.

We encode this without any coinduction support from Lean:

* `Step E R a b` is one layer of subtyping, defined *inductively*. It uses the
  relation `R` only under a function type or a record field.
* `Sub` is the greatest fixed point of `Step`: `a ≤ b` iff some relation `R`
  containing `(a, b)` is closed under `Step` (Knaster–Tarski).
  `Sub.coind` is the corresponding coinduction principle.

Records are compared as rows, i.e. total maps from labels to fields (as
in `Rows.lean`): `{fs | t} ≤ {gs | u}` holds when *every* label's field is
related, where `Ty.field` looks a label up in the explicit fields and
otherwise in the tail. The comparison of each field goes through the
coinductive hypothesis (a record field is a constructor), and tails need no
separate rule. A row variable's fields are opaque atoms `proj l ρ`, related
only to themselves (and to `⊤`/`Abs`).

Remaining gaps, all deliberate for now:

* A *recursive* row in tail position (a row variable that is recursive
  through its own fields) stays opaque instead of being unfolded.
* Row variables have no kinds yet (Rémy: the labels a row variable lacks).
  Without them, ill-kinded types such as `{| 'a} → {y: int | 'a}` (where
  `'a` is used both with and without `y`) are accepted as types and get
  conservative answers. **TODO: add kinds.**
* The MLsub lattice equations that the simplifier relies on (merging
  intersections of functions or records, distributivity) are not included.
-/

namespace SimpleSub

/-- Definitions of graph variables (`Ty.gvar`): `E n` is a set of upper
bounds, and `gvar n` stands for their intersection. This is how solutions of
constraint systems are expressed (see `Solution.lean`): named, possibly
mutually recursive definitions, without binders. Using a *set* (rather than
one type) lets the set be given by an inductive reachability predicate, so
that cycles between variables need no special treatment. -/
abbrev Defs := Nat → Ty → Prop

variable {E : Defs}

/-- One layer of subtyping, relative to the coinductive hypothesis `R`. -/
inductive Step (E : Defs) (R : Ty → Ty → Prop) : Ty → Ty → Prop where
  | top : Step E R a .top
  | bot : Step E R .bot b
  /-- `Abs` is the top field and the top row. -/
  | abs : Step E R a .abs
  | prim : Step E R (.prim n) (.prim n)
  | fvar : Step E R (.fvar x) (.fvar x)
  | unionL : Step E R a₁ b → Step E R a₂ b → Step E R (.union a₁ a₂) b
  | unionR₁ : Step E R a b₁ → Step E R a (.union b₁ b₂)
  | unionR₂ : Step E R a b₂ → Step E R a (.union b₁ b₂)
  | interL₁ : Step E R a₁ b → Step E R (.inter a₁ a₂) b
  | interL₂ : Step E R a₂ b → Step E R (.inter a₁ a₂) b
  | interR : Step E R a b₁ → Step E R a b₂ → Step E R a (.inter b₁ b₂)
  /-- Unfold a recursive type on the left (S-Rec). -/
  | muL : Step E R (a.open (.mu a)) b → Step E R (.mu a) b
  /-- Unfold a recursive type on the right (S-Rec). -/
  | muR : Step E R a (b.open (.mu b)) → Step E R a (.mu b)
  /-- Function types: the hypothesis `R` becomes usable here (◁). -/
  | arrow : R b₁ a₁ → R a₂ b₂ → Step E R (.arrow a₁ a₂) (.arrow b₁ b₂)
  /-- Records, compared as rows: every label's field, under `R` (◁). -/
  | record :
      (∀ l, R ((Ty.record fs t).field l) ((Ty.record gs u).field l)) →
      Step E R (.record fs t) (.record gs u)
  /-- A field of an opaque row is only known to be itself. -/
  | proj : Step E R (.proj l t) (.proj l t)
  /-- A graph variable is related to itself. -/
  | gvar : Step E R (.gvar n) (.gvar n)
  /-- A graph variable is below each of its upper bounds (like `interL`). -/
  | defL : E n u → Step E R u b → Step E R (.gvar n) b
  /-- Below all upper bounds of a graph variable is below it (like `interR`). -/
  | defR : (∀ u, E n u → Step E R a u) → Step E R a (.gvar n)
  /-- The same for a field of a graph row variable. -/
  | projDefL : E n u → Step E R (u.field l) b → Step E R (.proj l (.gvar n)) b
  | projDefR : (∀ u, E n u → Step E R a (u.field l)) → Step E R a (.proj l (.gvar n))

theorem Step.mono (hR : ∀ x y, R x y → R' x y) : Step E R a b → Step E R' a b := by
  intro h
  induction h with
  | top => exact .top
  | bot => exact .bot
  | abs => exact .abs
  | prim => exact .prim
  | fvar => exact .fvar
  | unionL _ _ ih₁ ih₂ => exact .unionL ih₁ ih₂
  | unionR₁ _ ih => exact .unionR₁ ih
  | unionR₂ _ ih => exact .unionR₂ ih
  | interL₁ _ ih => exact .interL₁ ih
  | interL₂ _ ih => exact .interL₂ ih
  | interR _ _ ih₁ ih₂ => exact .interR ih₁ ih₂
  | muL _ ih => exact .muL ih
  | muR _ ih => exact .muR ih
  | arrow h₁ h₂ => exact .arrow (hR _ _ h₁) (hR _ _ h₂)
  | record hf => exact .record (fun l => hR _ _ (hf l))
  | proj => exact .proj
  | gvar => exact .gvar
  | defL hd _ ih => exact .defL hd ih
  | defR _ ih => exact .defR ih
  | projDefL hd _ ih => exact .projDefL hd ih
  | projDefR _ ih => exact .projDefR ih

/-- Subtyping: the greatest fixed point of `Step`. -/
def Sub (E : Defs) (a b : Ty) : Prop :=
  ∃ R : Ty → Ty → Prop, (∀ x y, R x y → Step E R x y) ∧ R a b

/-- Coinduction: to show `a ≤ b`, give a relation containing `(a, b)` that
is closed under one layer of subtyping. -/
theorem Sub.coind (R : Ty → Ty → Prop) (hR : ∀ x y, R x y → Step E R x y) (h : R a b) :
    Sub E a b :=
  ⟨R, hR, h⟩

/-- `Sub` is a post-fixed point: every subtyping fact unfolds one layer. -/
theorem Sub.step (h : Sub E a b) : Step E (Sub E) a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact (hR _ _ hab).mono (fun _ _ hxy => ⟨R, hR, hxy⟩)

/-- `Sub` is a pre-fixed point: one layer over `Sub` is a subtyping fact. -/
theorem Sub.of_step (h : Step E (Sub E) a b) : Sub E a b := by
  refine ⟨fun x y => Sub E x y ∨ (x = a ∧ y = b), ?_, Or.inr ⟨rfl, rfl⟩⟩
  have up : ∀ x y, Sub E x y → Sub E x y ∨ (x = a ∧ y = b) := fun _ _ h => Or.inl h
  rintro x y (hs | ⟨rfl, rfl⟩)
  · exact hs.step.mono up
  · exact h.mono up

/-! ## Basic lattice facts -/

theorem Sub.top : Sub E a .top := Sub.of_step .top
theorem Sub.bot : Sub E .bot b := Sub.of_step .bot
theorem Sub.abs : Sub E a .abs := Sub.of_step .abs

/-! ## Reflexivity

Reflexivity already needs the guarded structure: `μα. a` is related to
itself by unfolding both sides, which only terminates because the
unguarded size `ug` decreases under unfolding for contractive types
(`ug_open`). -/

/-- The relation used to prove reflexivity. -/
def ReflRel (x y : Ty) : Prop := x = y ∧ Contractive x ∧ LC 0 x

theorem step_refl : (t : Ty) → Contractive t → LC 0 t → Step E ReflRel t t
  | .top, _, _ => .top
  | .bot, _, _ => .bot
  | .abs, _, _ => .abs
  | .prim _, _, _ => .prim
  | .fvar _, _, _ => .fvar
  | .bvar _, _, hlc => by cases hlc with | bvar h => exact absurd h (Nat.not_lt_zero _)
  | .union a b, hc, hlc => by
    cases hc with | union ha hb =>
    cases hlc with | union la lb =>
    exact .unionL (.unionR₁ (step_refl a ha la)) (.unionR₂ (step_refl b hb lb))
  | .inter a b, hc, hlc => by
    cases hc with | inter ha hb =>
    cases hlc with | inter la lb =>
    exact .interR (.interL₁ (step_refl a ha la)) (.interL₂ (step_refl b hb lb))
  | .arrow a b, hc, hlc => by
    cases hc with | arrow ha hb =>
    cases hlc with | arrow la lb =>
    exact .arrow ⟨rfl, ha, la⟩ ⟨rfl, hb, lb⟩
  | .record fs t, hc, hlc => .record (fun _ => ⟨rfl, hc.field, hlc.field⟩)
  | .proj _ _, _, _ => .proj
  | .gvar _, _, _ => .gvar
  | .mu a, hc, hlc => by
    have hd : (a.open (.mu a)).ug < (Ty.mu a).ug := by
      cases hc with | mu _ hg => exact ug_open a hg
    exact .muL (.muR (step_refl (a.open (.mu a)) (Contractive.open hlc hc) (LC.open hlc)))
termination_by t => t.ug
decreasing_by
  all_goals first
    | assumption
    | (simp only [Ty.ug]; omega)

/-- Every closed contractive type is a subtype of itself. -/
theorem Sub.refl (hc : Contractive t) (hlc : LC 0 t) : Sub E t t :=
  Sub.coind ReflRel (by rintro x y ⟨rfl, hc, hlc⟩; exact step_refl x hc hlc) ⟨rfl, hc, hlc⟩

/-! ## Transitivity

Transitivity is coinductive too: the composition `Comp` of `Sub` with
itself is closed under `Step`. That reduces to a cut-elimination lemma on
single layers (`cut`): from finite derivations of `x ≤ y` and `y ≤ z`, build
one of `x ≤ z` whose guarded premises are again compositions. It goes by
induction on the left derivation; when that derivation ends with a rule
that takes `y` apart (`unionR`, `interR`, `muR`, or a constructor rule),
one of the `cut_*` lemmas below does an induction on the right derivation:
rules that take `z` apart commute outward, and the rule that takes `y`
apart must be the matching one (`unionL`, `interL`, `muL`, the same
constructor), which cuts on smaller derivations. No rule takes `⊤` or `Abs`
apart on the left, so those cases are vacuous.

Contractiveness is not needed: every cut is between finite (inductive)
derivations. -/

/-- Subtyping, or the composition of subtyping with itself. Including
`Sub E` itself lets a cut against the reflexive atom rule of a *defined*
variable reuse the original derivation. -/
def Comp (E : Defs) (x z : Ty) : Prop := Sub E x z ∨ ∃ y, Sub E x y ∧ Sub E y z

section Cut

variable {x : Ty}

/- Each `cut_*` lemma handles one shape of the middle type `y`, by
induction on the right derivation. Rules that take `z` apart commute
outward; the rule that takes `y` apart must be the matching one. -/

/-- Lift a subtyping derivation into the hypothesis of the cut. -/
theorem Step.toComp (h : Step E (Sub E) a b) : Step E (Comp E) a b :=
  h.mono fun _ _ h => .inl h

theorem cut_top : ∀ y z, Step E (Sub E) y z → y = .top → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | muL | arrow | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_abs : ∀ y z, Step E (Sub E) y z → y = .abs → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | muL | arrow | record | defL | projDefL =>
    intro hy; cases hy

/-- Atoms (`prim`, `fvar`, `proj`, `gvar`): `x` is the atom itself. A graph
variable may also be unfolded by the right derivation, which is then
already a derivation from `x`. -/
theorem cut_atom
    (hatom : (∃ n, x = .prim n) ∨ (∃ v, x = .fvar v) ∨ (∃ l t, x = .proj l t) ∨
      (∃ n, x = .gvar n)) :
    ∀ y z, Step E (Sub E) y z → y = x → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | prim => intro hy; subst hy; exact .prim
  | fvar => intro hy; subst hy; exact .fvar
  | proj => intro hy; subst hy; exact .proj
  | gvar => intro hy; subst hy; exact .gvar
  | defL hd h' _ => intro hy; subst hy; exact (Step.defL hd h').toComp
  | projDefL hd h' _ => intro hy; subst hy; exact (Step.projDefL hd h').toComp
  | bot | unionL | interL₁ | interL₂ | muL | arrow | record =>
    intro hy; subst hy
    rcases hatom with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h

theorem cut_unionR₁ (ih : ∀ z, Step E (Sub E) y₁ z → Step E (Comp E) x z) :
    ∀ y z, Step E (Sub E) y z → y = .union y₁ y₂ → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | unionL h₁ _ _ _ => intro hy; cases hy; exact ih _ h₁
  | bot | prim | fvar | proj | gvar | interL₁ | interL₂ | muL | arrow | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_unionR₂ (ih : ∀ z, Step E (Sub E) y₂ z → Step E (Comp E) x z) :
    ∀ y z, Step E (Sub E) y z → y = .union y₁ y₂ → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | unionL _ h₂ _ _ => intro hy; cases hy; exact ih _ h₂
  | bot | prim | fvar | proj | gvar | interL₁ | interL₂ | muL | arrow | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_interR (ih₁ : ∀ z, Step E (Sub E) y₁ z → Step E (Comp E) x z)
    (ih₂ : ∀ z, Step E (Sub E) y₂ z → Step E (Comp E) x z) :
    ∀ y z, Step E (Sub E) y z → y = .inter y₁ y₂ → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | interL₁ h _ => intro hy; cases hy; exact ih₁ _ h
  | interL₂ h _ => intro hy; cases hy; exact ih₂ _ h
  | bot | prim | fvar | proj | gvar | unionL | muL | arrow | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_muR (ih : ∀ z, Step E (Sub E) (b.open (.mu b)) z → Step E (Comp E) x z) :
    ∀ y z, Step E (Sub E) y z → y = .mu b → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | muL h _ => intro hy; cases hy; exact ih _ h
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | arrow | record | defL | projDefL =>
    intro hy; cases hy

/-- The middle type is a graph variable, reached by `defR` on the left (so
`x` is below all its upper bounds): against the right's atom rule the left
derivation itself is the result; against `defL` (one upper bound below `z`)
the two cut on that upper bound. -/
theorem cut_defR (hl : ∀ u, E n u → Step E (Sub E) x u)
    (ih : ∀ u, E n u → ∀ z, Step E (Sub E) u z → Step E (Comp E) x z) :
    ∀ y z, Step E (Sub E) y z → y = .gvar n → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | gvar => intro hy; cases hy; exact (Step.defR hl).toComp
  | defL hd h _ => intro hy; cases hy; exact ih _ hd _ h
  | bot | prim | fvar | proj | unionL | interL₁ | interL₂ | muL | arrow | record | projDefL =>
    intro hy; cases hy

theorem cut_projDefR (hl : ∀ u, E n u → Step E (Sub E) x (u.field l))
    (ih : ∀ u, E n u → ∀ z, Step E (Sub E) (u.field l) z → Step E (Comp E) x z) :
    ∀ y z, Step E (Sub E) y z → y = .proj l (.gvar n) → Step E (Comp E) x z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | proj => intro hy; cases hy; exact (Step.projDefR hl).toComp
  | projDefL hd h _ => intro hy; cases hy; exact ih _ hd _ h
  | bot | prim | fvar | gvar | unionL | interL₁ | interL₂ | muL | arrow | record | defL =>
    intro hy; cases hy

theorem cut_arrow (h₁ : Sub E b₁ a₁) (h₂ : Sub E a₂ b₂) :
    ∀ y z, Step E (Sub E) y z → y = .arrow b₁ b₂ → Step E (Comp E) (.arrow a₁ a₂) z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | arrow g₁ g₂ => intro hy; cases hy; exact .arrow (.inr ⟨_, g₁, h₁⟩) (.inr ⟨_, h₂, g₂⟩)
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | muL | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_record
    (hf : ∀ l, Sub E ((Ty.record fs t).field l) ((Ty.record gs u).field l)) :
    ∀ y z, Step E (Sub E) y z → y = .record gs u → Step E (Comp E) (.record fs t) z := by
  intro y z h
  induction h with
  | top => intro _; exact .top
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | muR _ ih' => intro hy; exact .muR (ih' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | record hg => intro hy; cases hy; exact .record fun l => .inr ⟨_, hf l, hg l⟩
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | muL | arrow | defL | projDefL =>
    intro hy; cases hy

end Cut

/-- **Cut elimination for one layer**: `x ≤ y` and `y ≤ z` give `x ≤ z`,
with guarded premises that are subtyping facts or compositions. -/
theorem cut : Step E (Sub E) x y → ∀ z, Step E (Sub E) y z → Step E (Comp E) x z := by
  intro hl
  induction hl with
  | top => intro z hr; exact cut_top _ z hr rfl
  | abs => intro z hr; exact cut_abs _ z hr rfl
  | bot => intro _ _; exact .bot
  | prim => intro z hr; exact cut_atom (Or.inl ⟨_, rfl⟩) _ z hr rfl
  | fvar => intro z hr; exact cut_atom (Or.inr (Or.inl ⟨_, rfl⟩)) _ z hr rfl
  | proj => intro z hr; exact cut_atom (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))) _ z hr rfl
  | gvar => intro z hr; exact cut_atom (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))) _ z hr rfl
  | unionL _ _ ih₁ ih₂ => intro z hr; exact .unionL (ih₁ z hr) (ih₂ z hr)
  | unionR₁ _ ih => intro z hr; exact cut_unionR₁ ih _ z hr rfl
  | unionR₂ _ ih => intro z hr; exact cut_unionR₂ ih _ z hr rfl
  | interL₁ _ ih => intro z hr; exact .interL₁ (ih z hr)
  | interL₂ _ ih => intro z hr; exact .interL₂ (ih z hr)
  | interR _ _ ih₁ ih₂ => intro z hr; exact cut_interR ih₁ ih₂ _ z hr rfl
  | muL _ ih => intro z hr; exact .muL (ih z hr)
  | muR _ ih => intro z hr; exact cut_muR ih _ z hr rfl
  | arrow h₁ h₂ => intro z hr; exact cut_arrow h₁ h₂ _ z hr rfl
  | record hf => intro z hr; exact cut_record hf _ z hr rfl
  | defL hd _ ih => intro z hr; exact .defL hd (ih z hr)
  | defR hl ih => intro z hr; exact cut_defR hl ih _ z hr rfl
  | projDefL hd _ ih => intro z hr; exact .projDefL hd (ih z hr)
  | projDefR hl ih => intro z hr; exact cut_projDefR hl ih _ z hr rfl

/-- **Transitivity** of subtyping. -/
theorem Sub.trans (hab : Sub E a b) (hbc : Sub E b c) : Sub E a c := by
  refine Sub.coind (Comp E) ?_ (.inr ⟨b, hab, hbc⟩)
  rintro x z (h | ⟨_, hxy, hyz⟩)
  · exact h.step.toComp
  · exact cut hxy.step z hyz.step

/-! ## Recursive types equal their unfolding (S-Rec) -/

theorem Sub.unfold (hc : Contractive (.mu a)) (hlc : LC 0 (.mu a)) :
    Sub E (.mu a) (a.open (.mu a)) :=
  Sub.of_step (.muL (Sub.refl (Contractive.open hlc hc) (LC.open hlc)).step)

theorem Sub.fold (hc : Contractive (.mu a)) (hlc : LC 0 (.mu a)) :
    Sub E (a.open (.mu a)) (.mu a) :=
  Sub.of_step (.muR (Sub.refl (Contractive.open hlc hc) (LC.open hlc)).step)

/-! ## The paper's example (Sec. 5.1.3)

`μα₀. τ → τ → α₀ ≤ μα₁. τ → α₁`: these types never unfold to the same
syntax, so the proof needs a genuine coinductive hypothesis. -/

namespace PaperExample

def τ : Ty := .prim "t"
def A : Ty := .mu (.arrow τ (.arrow τ (.bvar 0)))
def B : Ty := .mu (.arrow τ (.bvar 0))

theorem paper_example : Sub E A B := by
  refine Sub.coind
    (fun x y => (x = A ∧ y = B) ∨ (x = .arrow τ A ∧ y = B) ∨ (x = τ ∧ y = τ))
    ?_ (Or.inl ⟨rfl, rfl⟩)
  rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · -- unfold both sides: τ → (τ → A) ≤ τ → B
    refine .muL (.muR ?_)
    show Step E _ (.arrow τ (.arrow τ A)) (.arrow τ B)
    exact .arrow (Or.inr (Or.inr ⟨rfl, rfl⟩)) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · -- unfold the right: τ → A ≤ τ → B
    refine .muR ?_
    show Step E _ (.arrow τ A) (.arrow τ B)
    exact .arrow (Or.inr (Or.inr ⟨rfl, rfl⟩)) (Or.inl ⟨rfl, rfl⟩)
  · exact .prim

end PaperExample

/-! ## Rows: facts the previous record rule could not derive

The first version of the record rule looked only at explicit fields,
treating a label missing on the left as `Abs`, and only let extra fields
into the right tail when it was a top row. These three true facts were
not derivable with it; comparing rows as maps makes them so. -/

section Rows

private def bool : Ty := .prim "bool"
private def int : Ty := .prim "int"

/-- A field hidden in a compound tail: `{ | 'b ∧ {done: bool}} ≤ {done: bool}`.
This is the shape the simplifier produces for `count`. -/
theorem field_in_compound_tail :
    Sub E (.record .nil (.inter (.fvar "b") (.record (.cons "done" bool .nil) .abs)))
        (.record (.cons "done" bool .nil) .abs) := by
  refine Sub.of_step (.record fun l => ?_)
  by_cases h : l = "done"
  · subst h
    exact Sub.of_step (show Step E (Sub E) (.inter (.proj "done" (.fvar "b")) bool) bool from
      .interL₂ .prim)
  · have h' : ¬ "done" = l := fun e => h e.symm
    simp only [Ty.field, Fields.lookup, h']
    exact Sub.abs

/-- The bottom row gives every field `⊥`: `{ | ⊥} ≤ {x: int}`. -/
theorem bottom_tail : Sub E (.record .nil .bot) (.record (.cons "x" int .nil) .abs) := by
  refine Sub.of_step (.record fun l => ?_)
  by_cases h : l = "x"
  · subst h; exact Sub.bot
  · have h' : ¬ "x" = l := fun e => h e.symm
    simp only [Ty.field, Fields.lookup, h']
    exact Sub.abs

/-- A flat row and the same row nested in a tail:
`{x: int | ρ} ≤ { | {x: int | ρ}}`. -/
theorem nested_tail :
    Sub E (.record (.cons "x" int .nil) (.fvar "ρ"))
        (.record .nil (.record (.cons "x" int .nil) (.fvar "ρ"))) := by
  refine Sub.of_step (.record fun l => ?_)
  by_cases h : l = "x"
  · subst h; exact Sub.of_step (show Step E (Sub E) int int from .prim)
  · have h' : ¬ "x" = l := fun e => h e.symm
    simp only [Ty.field, Fields.lookup, h']
    exact Sub.of_step .proj

/-- And soundness in the other direction: `{ } ≰ {x: int}`, since the
absent field is not an `int`. -/
theorem not_empty_le_field : ¬ Sub E (.record .nil .abs) (.record (.cons "x" int .nil) .abs) := by
  intro h
  have hs := h.step
  cases hs with
  | record hf =>
    have := (hf "x").step
    simp only [Ty.field, Fields.lookup] at this
    cases this

end Rows

/-! ## Why non-contractive types are excluded

The paper's coalescing produces `μα. int ∧ α` for a variable cycle. Under
these rules it is *strictly below* `int`: `int ≤ μα. int ∧ α` would need
infinitely many unfoldings without passing a constructor, which the
inductive `Step` cannot do. The simplifier, however, treats such a cycle as
`int`. Hence `lib/coalesce.ml` only emits contractive types. -/

namespace NonContractive

def M : Ty := .mu (.inter (.prim "int") (.bvar 0))

theorem M_le_int : Sub E M (.prim "int") :=
  Sub.of_step (.muL (show Step E (Sub E) (.inter (.prim "int") M) (.prim "int") from .interL₁ .prim))

theorem not_int_le_M : ¬ Sub E (.prim "int") M := by
  rintro ⟨R, hR, h⟩
  suffices ∀ x y, Step E R x y → x = .prim "int" →
      (y = M ∨ y = .inter (.prim "int") M) → False from
    this _ _ (hR _ _ h) rfl (Or.inl rfl)
  intro x y hs
  induction hs with
  | top | abs | prim | unionR₁ | unionR₂ | defR | projDefR =>
    intro _ hy; rcases hy with hy | hy <;> simp [M] at hy
  | bot | fvar | unionL | interL₁ | interL₂ | muL | arrow | record | proj | gvar | defL | projDefL =>
    intro hx; simp at hx
  | interR _ _ _ ih₂ =>
    intro hx hy
    rcases hy with hy | hy
    · simp [M] at hy
    · cases hy; exact ih₂ hx (Or.inl rfl)
  | muR _ ih =>
    intro hx hy
    rcases hy with hy | hy
    · simp only [M, Ty.mu.injEq] at hy
      subst hy
      exact ih hx (Or.inr rfl)
    · simp [M] at hy

end NonContractive

end SimpleSub
