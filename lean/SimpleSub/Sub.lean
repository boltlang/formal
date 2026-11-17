import SimpleSub.Types

/-!
# Declarative subtyping

Subtyping between graph variables, whose definitions may be cyclic, must be
coinductive, but only in a *guarded* way: splitting unions and
intersections, unfolding graph variables and comparing row tails may
happen only finitely often between two type constructors. This is the
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
only to themselves (and to `Abs`), or through a graph variable's
definitions.

`Abs` is *strictly above* `⊤`. `Abs` is the top of everything: it promises
nothing about a field, not even that it is there. `⊤` is the top of types:
some value. So `Abs ≤ ⊤` fails (`not_abs_le_top`), `{} ≤ {x : ⊤}` fails, and
"`τ ≤ ⊤`" says that a field of type `τ` is present, which is what the
typing rule for selection asks (`Typing.lean`).

There are no structural recursive types (`Types.lean`); a recursive type
can only arise through graph-variable definitions, which the model only
allows without a cycle through a type constructor. The MLsub lattice
equations that the simplifier relies on (merging intersections of
functions or records, distributivity) are not included.
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

mutual
/-- The graph variables occurring in a type. -/
def Ty.gvars : Ty → List Nat
  | .gvar n => [n]
  | .top | .bot | .abs | .prim _ | .fvar _ => []
  | .union a b | .inter a b | .arrow a b => a.gvars ++ b.gvars
  | .record fs t => fs.gvars ++ t.gvars
  | .proj _ t => t.gvars

def Fields.gvars : Fields → List Nat
  | .nil => []
  | .cons _ f fs => f.gvars ++ fs.gvars
end

/-- Definitions without recursive types: a graph variable's definitions
only mention graph variables of strictly lower rank. -/
def Defs.Ranked (E : Defs) (r : Nat → Nat) : Prop := ∀ n u, E n u → ∀ m ∈ u.gvars, r m < r n

/-- Syntactically a type: not `Abs`, a field of an opaque row, or
something whose meaning depends on its parts or its definitions. Only these
are below `⊤` outright; unions, intersections and graph variables are below
`⊤` through their own rules. So `Abs` (any value, *or no field at all*) is
strictly above `⊤` (any value). -/
def Ty.IsType : Ty → Prop
  | .top | .prim _ | .arrow _ _ | .record _ _ | .fvar _ => True
  | _ => False

/-- One layer of subtyping, relative to the coinductive hypothesis `R`. -/
inductive Step (E : Defs) (R : Ty → Ty → Prop) : Ty → Ty → Prop where
  /-- Every type is below `⊤`; `Abs` is not. -/
  | top : a.IsType → Step E R a .top
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
  | top h => exact .top h
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

theorem Sub.top (h : a.IsType) : Sub E a .top := Sub.of_step (.top h)
theorem Sub.bot : Sub E .bot b := Sub.of_step .bot
theorem Sub.abs : Sub E a .abs := Sub.of_step .abs

/-! ## Reflexivity -/

theorem step_refl : (t : Ty) → Step E Eq t t
  | .top => .top trivial
  | .bot => .bot
  | .abs => .abs
  | .prim _ => .prim
  | .fvar _ => .fvar
  | .union a b => .unionL (.unionR₁ (step_refl a)) (.unionR₂ (step_refl b))
  | .inter a b => .interR (.interL₁ (step_refl a)) (.interL₂ (step_refl b))
  | .arrow _ _ => .arrow rfl rfl
  | .record _ _ => .record fun _ => rfl
  | .proj _ _ => .proj
  | .gvar _ => .gvar

/-- Every type is a subtype of itself. -/
theorem Sub.refl : Sub E t t :=
  Sub.coind Eq (by rintro x y rfl; exact step_refl x) rfl

/-! ## Transitivity

Transitivity is coinductive too: the composition `Comp` of `Sub` with
itself is closed under `Step`. That reduces to a cut-elimination lemma on
single layers (`cut`): from finite derivations of `x ≤ y` and `y ≤ z`, build
one of `x ≤ z` whose guarded premises are again compositions. It goes by
induction on the left derivation; when that derivation ends with a rule
that takes `y` apart (`unionR`, `interR`, or a constructor rule),
one of the `cut_*` lemmas below does an induction on the right derivation:
rules that take `z` apart commute outward, and the rule that takes `y`
apart must be the matching one (`unionL`, `interL`, the same
constructor), which cuts on smaller derivations. No rule takes `⊤` or `Abs`
apart on the left, so those cases are vacuous. When the right derivation
ends with the `⊤` rule, `y` is syntactically a type, and so is `x`, since
the left derivation ended with the rule for `y`'s constructor. -/

/-- A relation, or its composition with itself. Including `R` itself lets
a cut against the reflexive atom rule of a *defined* variable reuse the
original derivation. The cut works for any relation `R` in the guarded
premises; transitivity of `Sub` is the case `R = Sub E`. -/
def RComp (R : Ty → Ty → Prop) (x z : Ty) : Prop := R x z ∨ ∃ y, R x y ∧ R y z

/-- Subtyping, or the composition of subtyping with itself. -/
abbrev Comp (E : Defs) : Ty → Ty → Prop := RComp (Sub E)

section Cut

variable {x : Ty} {R : Ty → Ty → Prop}

/- Each `cut_*` lemma handles one shape of the middle type `y`, by
induction on the right derivation. Rules that take `z` apart commute
outward; the rule that takes `y` apart must be the matching one. -/

/-- Lift a subtyping derivation into the hypothesis of the cut. -/
theorem Step.toComp (h : Step E R a b) : Step E (RComp R) a b :=
  h.mono fun _ _ h => .inl h

theorem cut_top (hx : x.IsType) : ∀ y z, Step E R y z → y = .top → Step E (RComp R) x z := by
  intro y z h
  induction h with
  | top _ => intro _; exact .top hx
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | arrow | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_abs : ∀ y z, Step E R y z → y = .abs → Step E (RComp R) x z := by
  intro y z h
  induction h with
  | top ht => intro hy; subst hy; exact ht.elim
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | arrow | record | defL | projDefL =>
    intro hy; cases hy

/-- Atoms (`prim`, `fvar`, `proj`, `gvar`): `x` is the atom itself. A graph
variable may also be unfolded by the right derivation, which is then
already a derivation from `x`. -/
theorem cut_atom
    (hatom : (∃ n, x = .prim n) ∨ (∃ v, x = .fvar v) ∨ (∃ l t, x = .proj l t) ∨
      (∃ n, x = .gvar n)) :
    ∀ y z, Step E R y z → y = x → Step E (RComp R) x z := by
  intro y z h
  induction h with
  | top ht => intro hy; subst hy; exact .top ht
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | prim => intro hy; subst hy; exact .prim
  | fvar => intro hy; subst hy; exact .fvar
  | proj => intro hy; subst hy; exact .proj
  | gvar => intro hy; subst hy; exact .gvar
  | defL hd h' _ => intro hy; subst hy; exact (Step.defL hd h').toComp
  | projDefL hd h' _ => intro hy; subst hy; exact (Step.projDefL hd h').toComp
  | bot | unionL | interL₁ | interL₂ | arrow | record =>
    intro hy; subst hy
    rcases hatom with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h

theorem cut_unionR₁ (ih : ∀ z, Step E R y₁ z → Step E (RComp R) x z) :
    ∀ y z, Step E R y z → y = .union y₁ y₂ → Step E (RComp R) x z := by
  intro y z h
  induction h with
  | top ht => intro hy; subst hy; exact ht.elim
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | unionL h₁ _ _ _ => intro hy; cases hy; exact ih _ h₁
  | bot | prim | fvar | proj | gvar | interL₁ | interL₂ | arrow | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_unionR₂ (ih : ∀ z, Step E R y₂ z → Step E (RComp R) x z) :
    ∀ y z, Step E R y z → y = .union y₁ y₂ → Step E (RComp R) x z := by
  intro y z h
  induction h with
  | top ht => intro hy; subst hy; exact ht.elim
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | unionL _ h₂ _ _ => intro hy; cases hy; exact ih _ h₂
  | bot | prim | fvar | proj | gvar | interL₁ | interL₂ | arrow | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_interR (ih₁ : ∀ z, Step E R y₁ z → Step E (RComp R) x z)
    (ih₂ : ∀ z, Step E R y₂ z → Step E (RComp R) x z) :
    ∀ y z, Step E R y z → y = .inter y₁ y₂ → Step E (RComp R) x z := by
  intro y z h
  induction h with
  | top ht => intro hy; subst hy; exact ht.elim
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | interL₁ h _ => intro hy; cases hy; exact ih₁ _ h
  | interL₂ h _ => intro hy; cases hy; exact ih₂ _ h
  | bot | prim | fvar | proj | gvar | unionL | arrow | record | defL | projDefL =>
    intro hy; cases hy

/-- The middle type is a graph variable, reached by `defR` on the left (so
`x` is below all its upper bounds): against the right's atom rule the left
derivation itself is the result; against `defL` (one upper bound below `z`)
the two cut on that upper bound. -/
theorem cut_defR (hl : ∀ u, E n u → Step E R x u)
    (ih : ∀ u, E n u → ∀ z, Step E R u z → Step E (RComp R) x z) :
    ∀ y z, Step E R y z → y = .gvar n → Step E (RComp R) x z := by
  intro y z h
  induction h with
  | top ht => intro hy; subst hy; exact ht.elim
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | gvar => intro hy; cases hy; exact (Step.defR hl).toComp
  | defL hd h _ => intro hy; cases hy; exact ih _ hd _ h
  | bot | prim | fvar | proj | unionL | interL₁ | interL₂ | arrow | record | projDefL =>
    intro hy; cases hy

theorem cut_projDefR (hl : ∀ u, E n u → Step E R x (u.field l))
    (ih : ∀ u, E n u → ∀ z, Step E R (u.field l) z → Step E (RComp R) x z) :
    ∀ y z, Step E R y z → y = .proj l (.gvar n) → Step E (RComp R) x z := by
  intro y z h
  induction h with
  | top ht => intro hy; subst hy; exact ht.elim
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | proj => intro hy; cases hy; exact (Step.projDefR hl).toComp
  | projDefL hd h _ => intro hy; cases hy; exact ih _ hd _ h
  | bot | prim | fvar | gvar | unionL | interL₁ | interL₂ | arrow | record | defL =>
    intro hy; cases hy

theorem cut_arrow (h₁ : R b₁ a₁) (h₂ : R a₂ b₂) :
    ∀ y z, Step E R y z → y = .arrow b₁ b₂ → Step E (RComp R) (.arrow a₁ a₂) z := by
  intro y z h
  induction h with
  | top _ => intro _; exact .top trivial
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | arrow g₁ g₂ => intro hy; cases hy; exact .arrow (.inr ⟨_, g₁, h₁⟩) (.inr ⟨_, h₂, g₂⟩)
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | record | defL | projDefL =>
    intro hy; cases hy

theorem cut_record
    (hf : ∀ l, R ((Ty.record fs t).field l) ((Ty.record gs u).field l)) :
    ∀ y z, Step E R y z → y = .record gs u → Step E (RComp R) (.record fs t) z := by
  intro y z h
  induction h with
  | top _ => intro _; exact .top trivial
  | abs => intro _; exact .abs
  | unionR₁ _ ih' => intro hy; exact .unionR₁ (ih' hy)
  | unionR₂ _ ih' => intro hy; exact .unionR₂ (ih' hy)
  | interR _ _ ih₁' ih₂' => intro hy; exact .interR (ih₁' hy) (ih₂' hy)
  | defR _ ih' => intro hy; exact .defR fun u hu => ih' u hu hy
  | projDefR _ ih' => intro hy; exact .projDefR fun u hu => ih' u hu hy
  | record hg => intro hy; cases hy; exact .record fun l => .inr ⟨_, hf l, hg l⟩
  | bot | prim | fvar | proj | gvar | unionL | interL₁ | interL₂ | arrow | defL | projDefL =>
    intro hy; cases hy

end Cut

/-- **Cut elimination for one layer**: `x ≤ y` and `y ≤ z` give `x ≤ z`,
with guarded premises that are subtyping facts or compositions. -/
theorem cut : Step E R x y → ∀ z, Step E R y z → Step E (RComp R) x z := by
  intro hl
  induction hl with
  | top hx => intro z hr; exact cut_top hx _ z hr rfl
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

/-! ## `Abs` is strictly above `⊤`

`Abs` says nothing about a field, not even that it is there; `⊤` says it
holds some value. So a type that is below `⊤` is a *present* field, and
nothing above `Abs` is one. This is what makes selecting a field safe. -/

theorem not_abs_le_top : ¬ Sub E .abs .top := fun h => by
  cases h.step with | top ht => exact ht

/-- Nothing above `Abs` is a type. -/
theorem not_abs_le_of_le_top (h : Sub E τ .top) : ¬ Sub E .abs τ :=
  fun h' => not_abs_le_top (h'.trans h)

/-! ## Coinduction up to transitivity -/

/-- The transitive closure of a relation. -/
inductive TC (R : Ty → Ty → Prop) : Ty → Ty → Prop where
  | base : R x y → TC R x y
  | trans : TC R x y → TC R y z → TC R x z

theorem TC.step {R : Ty → Ty → Prop} (hR : ∀ x y, R x y → Step E (TC R) x y) :
    TC R a b → Step E (TC R) a b := by
  intro h
  induction h with
  | base h => exact hR _ _ h
  | trans _ _ ih₁ ih₂ =>
    refine (cut ih₁ _ ih₂).mono fun _ _ h => ?_
    rcases h with h | ⟨_, h₁, h₂⟩
    · exact h
    · exact .trans h₁ h₂

/-- **Coinduction up to transitivity**: if every pair of `R` takes a step
whose guarded premises are chains of `R`, then `R` is contained in
subtyping. -/
theorem Sub.coind_trans (R : Ty → Ty → Prop) (hR : ∀ x y, R x y → Step E (TC R) x y)
    (h : R a b) : Sub E a b :=
  Sub.coind (TC R) (fun _ _ h => TC.step hR h) (.base h)

/-! ## The paper's example (Sec. 5.1.3), with graph variables

`A = τ → τ → A ≤ B = τ → B`: the two recursive types never unfold to the
same syntax, so the proof needs a genuine coinductive hypothesis. They are
written as graph variables `0` and `1`, defined by their unfoldings. -/

namespace PaperExample

def τ : Ty := .prim "t"
def A : Ty := .gvar 0
def B : Ty := .gvar 1

/-- `A` is defined as `τ → τ → A`, `B` as `τ → B`. -/
def E₀ : Defs := fun n t =>
  (n = 0 ∧ t = .arrow τ (.arrow τ A)) ∨ (n = 1 ∧ t = .arrow τ B)

theorem paper_example : Sub E₀ A B := by
  refine Sub.coind
    (fun x y => (x = A ∧ y = B) ∨ (x = .arrow τ A ∧ y = B) ∨ (x = τ ∧ y = τ))
    ?_ (Or.inl ⟨rfl, rfl⟩)
  rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · -- B's only definition is `τ → B`; use A's: τ → (τ → A) ≤ τ → B
    refine .defR fun u hu => ?_
    rcases hu with ⟨h, _⟩ | ⟨_, rfl⟩
    · exact absurd h (by decide)
    · exact .defL (Or.inl ⟨rfl, rfl⟩)
        (.arrow (Or.inr (Or.inr ⟨rfl, rfl⟩)) (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · -- τ → A ≤ τ → B
    refine .defR fun u hu => ?_
    rcases hu with ⟨h, _⟩ | ⟨_, rfl⟩
    · exact absurd h (by decide)
    · exact .arrow (Or.inr (Or.inr ⟨rfl, rfl⟩)) (Or.inl ⟨rfl, rfl⟩)
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
    Sub E (.record .nil (.inter (.fvar 0) (.record (.cons "done" bool .nil) .abs)))
        (.record (.cons "done" bool .nil) .abs) := by
  refine Sub.of_step (.record fun l => ?_)
  by_cases h : l = "done"
  · subst h
    exact Sub.of_step (show Step E (Sub E) (.inter (.proj "done" (.fvar 0)) bool) bool from
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
    Sub E (.record (.cons "x" int .nil) (.fvar 0))
        (.record .nil (.record (.cons "x" int .nil) (.fvar 0))) := by
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

end SimpleSub
