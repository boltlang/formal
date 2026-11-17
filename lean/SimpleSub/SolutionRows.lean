import SimpleSub.Solution
import SimpleSub.Sorts

/-!
# A solution of the inferred constraints, with rows

Extends `Solution.lean` from the record-free fragment to all simple types.
The declarative record rule compares two records *field by field* (as
total maps from labels to fields, via `Ty.field`), so the coinductive
relation also contains the field projections of accepted constraints
(`SolR.fld`). Proving one layer for such a field pair (`stepField`) follows
the algorithm's record case: common fields, labels supplied by the left
tail (through row expansion), extra left fields flowing into the right
tail, and labels in neither.

At the level of types, `Abs` must never appear on the left: it is the top
of `Sub`, so `Abs ≤ {…}` is (rightly) false, although row variables can
have `Abs` as a lower bound and records as upper bounds. Such constraints
are only ever compared field by field; the type-level pairs of the relation
carry the side condition that their left side is not `Abs` (or that they
are reflexive), which `Sorts.lean` makes available: `Abs` is never the
parameter or result of a function type.

When the right side of a field pair is a row variable `ρ`, the proof has
to look at each of `ρ`'s upper bounds, and recurses through *their* tails
without passing a type constructor. This terminates if chains of row
variables through upper bounds' tails are acyclic, which the theorem takes
as a hypothesis (`TailRanked`). Kinds for row variables make it hold
(`Kinds.lean`): each step along such a chain adds labels the new row
variable lacks.
-/

namespace SimpleSub.Alg

open State

/-! ## Fields of translated simple types -/

theorem SFields.toFields_lookup : ∀ (fs : SFields) (l : String),
    fs.toFields.lookup l = (fs.lookup l).map SType.toTy
  | .nil, _ => rfl
  | .cons n f fs, l => by
    simp only [SFields.toFields, Fields.lookup, SFields.lookup]
    by_cases h : n = l
    · simp [h]
    · simp [h, SFields.toFields_lookup fs l]

theorem field_record (l : String) (fs : SFields) (t : SType) :
    (SType.record fs t).toTy.field l =
      match fs.lookup l with
      | some f => f.toTy
      | none => t.toTy.field l := by
  simp only [SType.toTy, Ty.field, SFields.toFields_lookup]
  cases fs.lookup l <;> rfl

theorem SFields.lookup_append (l : String) : ∀ (fs gs : SFields),
    (fs.append gs).lookup l = match fs.lookup l with
      | some f => some f
      | none => gs.lookup l
  | .nil, _ => rfl
  | .cons n f fs, gs => by
    simp only [SFields.append, SFields.lookup]
    by_cases h : n = l
    · simp [h]
    · simp [h, SFields.lookup_append l fs gs]

/-- A row is the record of its flattened fields over its flattened tail. -/
theorem field_rowView (l : String) : ∀ x : SType,
    x.toTy.field l = (SType.record (rowView x).1 (rowView x).2).toTy.field l
  | .record fs t => by
    have ih := field_rowView l t
    simp only [rowView]
    rw [field_record, field_record, SFields.lookup_append]
    cases fs.lookup l with
    | some f => rfl
    | none => rw [ih, field_record]
  | .var _ | .prim _ | .arrow _ _ | .abs => by
    simp [rowView, field_record, SFields.lookup]

theorem field_restRow (l : String) (ex : SFields) (t : SType) :
    (restRow ex t).toTy.field l =
      match ex.lookup l with
      | some f => f.toTy
      | none => t.toTy.field l := by
  cases ex with
  | nil => simp [restRow, SFields.lookup]
  | cons => simp only [restRow]; exact field_record ..

theorem SFields.common_mem {f₀ f₁ : SType} {l : String} {fs₀ : SFields} :
    ∀ fs₁ : SFields, fs₁.lookup l = some f₁ → fs₀.lookup l = some f₀ →
      (f₀, f₁) ∈ fs₀.common fs₁
  | .nil, h, _ => by simp [SFields.lookup] at h
  | .cons n g rest, h₁, h₀ => by
    simp only [SFields.lookup] at h₁
    simp only [SFields.common]
    by_cases hn : n = l
    · subst hn
      simp at h₁
      subst h₁
      rw [h₀]
      exact List.mem_cons_self ..
    · simp only [hn, ite_false] at h₁
      have := SFields.common_mem rest h₁ h₀
      split
      · exact List.mem_cons_of_mem _ this
      · exact this

theorem SFields.missing_lookup (fs₀ : SFields) (l : String) : ∀ fs₁ : SFields,
    (fs₀.missing fs₁).lookup l =
      if (fs₀.lookup l).isSome then none else fs₁.lookup l
  | .nil => by simp [SFields.missing, SFields.lookup]
  | .cons n g rest => by
    have ih := SFields.missing_lookup fs₀ l rest
    simp only [SFields.missing, SFields.lookup]
    by_cases hn : n = l
    · subst hn
      cases h : fs₀.lookup n with
      | some _ => simp [ih, h]
      | none => simp [SFields.lookup]
    · cases h : fs₀.lookup n with
      | some _ => simp [ih, hn]
      | none => simp [SFields.lookup, hn, ih]

theorem SFields.absPairs_mem {l : String} {f : SType} : ∀ fs : SFields,
    fs.lookup l = some f → (SType.abs, f) ∈ fs.absPairs
  | .nil, h => by simp [SFields.lookup] at h
  | .cons n g rest, h => by
    simp only [SFields.lookup] at h
    simp only [SFields.absPairs]
    split at h
    · cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (SFields.absPairs_mem rest h)

theorem SFields.absentIn_lookup (K : List String) (l : String) : ∀ fs : SFields,
    (fs.absentIn K).lookup l = if l ∈ K then fs.lookup l else none
  | .nil => by simp [SFields.absentIn, SFields.lookup]
  | .cons n g rest => by
    have ih := SFields.absentIn_lookup K l rest
    by_cases hn : n = l
    · subst hn; by_cases hk : n ∈ K <;> simp [SFields.absentIn, SFields.lookup, hk, ih]
    · by_cases hk : n ∈ K <;> simp [SFields.absentIn, SFields.lookup, hk, hn, ih]

theorem SFields.presentIn_lookup (K : List String) (l : String) : ∀ fs : SFields,
    (fs.presentIn K).lookup l = if l ∈ K then none else fs.lookup l
  | .nil => by simp [SFields.presentIn, SFields.lookup]
  | .cons n g rest => by
    have ih := SFields.presentIn_lookup K l rest
    by_cases hn : n = l
    · subst hn; by_cases hk : n ∈ K <;> simp [SFields.presentIn, SFields.lookup, hk, ih]
    · by_cases hk : n ∈ K <;> simp [SFields.presentIn, SFields.lookup, hk, hn, ih]

/-! ## Flattened tails -/

theorem rowView_tail_ne_record : ∀ x : SType, ∀ fs t, (rowView x).2 ≠ .record fs t
  | .record _ t, fs, t' => by simp only [rowView]; exact rowView_tail_ne_record t fs t'
  | .var _, _, _ | .prim _, _, _ | .arrow _ _, _, _ | .abs, _, _ => by simp [rowView]

theorem rowView_of_ne_record : ∀ y : SType, (∀ fs t, y ≠ .record fs t) → rowView y = (.nil, y)
  | .record fs t, h => absurd rfl (h fs t)
  | .var _, _ | .prim _, _ | .arrow _ _, _ | .abs, _ => rfl

theorem rowView_tail_le : ∀ x : SType, sizeOf (rowView x).2 ≤ sizeOf x
  | .record fs t => by
    simp only [rowView]
    have := rowView_tail_le t
    simp only [SType.record.sizeOf_spec]
    omega
  | .var _ | .prim _ | .arrow _ _ | .abs => by simp [rowView]

theorem rowView_tail_lt (fs : SFields) (t : SType) :
    sizeOf (rowView (.record fs t)).2 < sizeOf (SType.record fs t) := by
  simp only [rowView]
  have := rowView_tail_le t
  simp only [SType.record.sizeOf_spec]
  omega

/-! ## Ranking row-variable tails -/

/-- The rank of the flattened tail of a row, when it is a row variable. -/
def tailRank (rank : Nat → Nat) (b : SType) : Nat :=
  match (rowView b).2 with
  | .var ρ => 2 * rank ρ + 1
  | _ => 0

/-- Chains of row variables through tails are acyclic, as kinds guarantee
(`kinds_tailRanked` in `Kinds.lean`): the tail variable of a reachable
upper bound of `v`, or of a non-variable lower bound of `v`, ranks below
`v`, and a variable upper bound of `v` does not rank above it. -/
structure TailRanked (s : State) (rank : Nat → Nat) : Prop where
  clo : ∀ v u ρ, Clo s.bounds v u → (rowView u).2 = .var ρ → rank ρ < rank v
  upVar : ∀ v m, SType.var m ∈ (s.bounds v).upper → rank m ≤ rank v
  lower : ∀ v x ρ, x ∈ (s.bounds v).lower → (∀ w, x ≠ .var w) → (rowView x).2 = .var ρ →
    rank ρ < rank v

theorem tailRank_tail (rank : Nat → Nat) (x : SType) :
    tailRank rank (rowView x).2 = tailRank rank x := by
  simp only [tailRank]
  rw [rowView_of_ne_record _ (rowView_tail_ne_record x)]

theorem tailRank_var (rank : Nat → Nat) (v : Nat) : tailRank rank (.var v) = 2 * rank v + 1 := by
  simp [tailRank, rowView]

theorem tailRank_var_lt {s : State} {rank : Nat → Nat} (hr : TailRanked s rank)
    (hc : Clo s.bounds v u) : tailRank rank u < tailRank rank (.var v) := by
  rw [tailRank_var]
  simp only [tailRank]
  split
  · next ρ h => have := hr.clo v u ρ hc h; omega
  · omega

theorem tailRank_lower_lt {s : State} {rank : Nat → Nat} (hr : TailRanked s rank)
    (hx : x ∈ (s.bounds v).lower) (hnv : ∀ w, x ≠ .var w) :
    tailRank rank x < tailRank rank (.var v) := by
  rw [tailRank_var]
  simp only [tailRank]
  split
  · next ρ h => have := hr.lower v x ρ hx hnv h; omega
  · omega

theorem tailRank_upVar_le {s : State} {rank : Nat → Nat} (hr : TailRanked s rank)
    (hm : SType.var m ∈ (s.bounds v).upper) : tailRank rank (.var m) ≤ tailRank rank (.var v) := by
  rw [tailRank_var, tailRank_var]; have := hr.upVar v m hm; omega

theorem SFields.Rel.lookup {Q : SType → SType → Prop} {l : String} {g : SType} :
    ∀ {P' P : SFields}, SFields.Rel Q P' P → P.lookup l = some g →
      ∃ f, P'.lookup l = some f ∧ Q f g
  | _, _, .nil, h => by simp [SFields.lookup] at h
  | _, _, @SFields.Rel.cons _ f g' _ _ n hq r, h => by
    simp only [SFields.lookup] at h ⊢
    by_cases hn : n = l
    · simp only [hn, ite_true] at h ⊢; cases h; exact ⟨f, rfl, hq⟩
    · simp only [hn, ite_false] at h ⊢; exact r.lookup h

theorem SFields.Rel.lookup_none {Q : SType → SType → Prop} {l : String} :
    ∀ {P' P : SFields}, SFields.Rel Q P' P → P.lookup l = none → P'.lookup l = none
  | _, _, .nil, _ => rfl
  | _, _, @SFields.Rel.cons _ _ _ _ _ n _ r, h => by
    simp only [SFields.lookup] at h ⊢
    by_cases hn : n = l
    · simp [hn] at h
    · simp only [hn, ite_false] at h ⊢; exact r.lookup_none h

/-! ## One layer

The coinduction is up to transitivity (`Sub.coind_trans`): a constraint
justified through an extruded bound (`viaR`) only holds through a chain of
accepted constraints, whose one-layer steps compose by cut elimination. -/

/-- The relation used for the coinduction: accepted constraints, and the
field projections of accepted constraints. -/
inductive SolR (s : State) : Ty → Ty → Prop where
  | ty : Logged s a b → (a ≠ .abs ∨ a = b) → SolR s a.toTy b.toTy
  | fld : Logged s a b → SolR s (a.toTy.field l) (b.toTy.field l)

section Steps

variable {s : State}

/-- One layer, with chains of the coinductive relation as hypotheses. -/
abbrev St (s : State) (x y : Ty) : Prop := Step (defsOf s) (TC (SolR s)) x y

/-- One-layer steps compose (cut elimination). -/
theorem St.comp (h₁ : St s x y) (h₂ : St s y z) : St s x z :=
  (cut h₁ _ h₂).mono fun _ _ h => match h with
    | .inl h => h
    | .inr ⟨_, h₁, h₂⟩ => .trans h₁ h₂

theorem stepRefl : ∀ a : SType, St s a.toTy a.toTy
  | .var _ => .gvar
  | .prim _ => .prim
  | .arrow _ _ => .arrow (.base (.ty (.inl rfl) (.inr rfl))) (.base (.ty (.inl rfl) (.inr rfl)))
  | .record fs t => .record fun l =>
    .base (SolR.fld (a := .record fs t) (b := .record fs t) (l := l) (.inl rfl))
  | .abs => .abs

theorem stepReflField (l : String) : ∀ a : SType, St s (a.toTy.field l) (a.toTy.field l)
  | .record fs t => by
    rw [field_record]
    cases fs.lookup l with
    | some f => exact stepRefl f
    | none => exact stepReflField l t
  | .var _ => .proj
  | .prim _ | .arrow _ _ | .abs => .abs

/-- A logged arrow constraint has non-`Abs` components. -/
theorem arrow_comps (hn : LogNAC s) (hl : (SType.arrow l₀ r₀, SType.arrow l₁ r₁) ∈ s.log) :
    l₁ ≠ .abs ∧ r₀ ≠ .abs := ⟨(hn _ hl).2.1, (hn _ hl).1.2.1⟩

/-- One layer for an accepted constraint between non-variable types. -/
theorem stepNonvar (hi : Inv s) (hn : LogNAC s) (hl : Logged s a b) (ha : a ≠ .abs)
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w) : St s a.toTy b.toTy := by
  rcases hl with rfl | hl
  · exact stepRefl a
  · cases hi.just.step hl with
    | absR => exact .abs
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => exact absurd rfl ha
    | @record fa ta _ _ fb tb =>
      exact .record fun l => .base (SolR.fld (a := .record fa ta) (b := .record fb tb) (l := l) (.inr hl))
    | varL => exact absurd rfl (hav _)
    | varR => exact absurd rfl (hbv _)
    | viaL => exact absurd rfl (hav _)
    | viaR => exact absurd rfl (hbv _)

/-- A type other than `Abs` and a variable is below `⊤`. -/
theorem stepTop : ∀ {a : SType}, a ≠ .abs → (∀ w, a ≠ .var w) → St s a.toTy .top
  | .prim _, _, _ | .arrow _ _, _, _ | .record _ _, _, _ => .top trivial
  | .abs, h, _ => absurd rfl h
  | .var w, _, h => absurd rfl (h w)

/-- A chain of accepted constraints between non-variable types, whose right
sides satisfy `P` (a bound on their tail ranks, for fields). -/
inductive Chain (s : State) (P : SType → Prop) : SType → SType → Prop where
  | one : Logged s a b → (∀ w, a ≠ .var w) → (∀ w, b ≠ .var w) → P b → Chain s P a b
  | cons : Logged s a b → (∀ w, a ≠ .var w) → (∀ w, b ≠ .var w) → b ≠ .abs → P b →
      Chain s P b c → Chain s P a c

theorem Chain.step (hi : Inv s) (hn : LogNAC s) {P : SType → Prop} :
    Chain s P a u → a ≠ .abs → St s a.toTy u.toTy
  | .one hl hav hbv _, ha => stepNonvar hi hn hl ha hav hbv
  | .cons hl hav hbv hba _ c, ha => (stepNonvar hi hn hl ha hav hbv).comp (c.step hi hn hba)

theorem Chain.fieldStep {P : SType → Prop} {l : String}
    (ih : ∀ x y, Logged s x y → P y → St s (x.toTy.field l) (y.toTy.field l)) :
    Chain s P a u → St s (a.toTy.field l) (u.toTy.field l)
  | .one hl _ _ hp => ih _ _ hl hp
  | .cons hl _ _ _ hp c => (ih _ _ hl hp).comp (c.fieldStep ih)

/-- **Chains through lower bounds**: a non-variable lower bound `x` of `m`
is below every upper bound `u` reachable from `m`, through a chain of
accepted constraints. Consistency gives `x ≤ m'` for each variable upper
bound `m'` on the way; that constraint installed `x` as a lower bound of
`m'`, or (`viaR`) the extrusion `x'` of `x`, with `x ≤ x'` accepted. -/
theorem lower_chain (hi : Inv s) {rank : Nat → Nat} (hr : TailRanked s rank)
    (hc : Clo s.bounds m u) : ∀ x, x ∈ (s.bounds m).lower → (∀ w, x ≠ .var w) →
      ∀ B, tailRank rank (.var m) ≤ B → Chain s (fun y => tailRank rank y < B) x u := by
  induction hc with
  | @here n u hu hnv =>
    intro x hx hxv B hB
    rcases hi.cons n x u hx hu with h | h
    · exact .one h hxv hnv (Nat.lt_of_lt_of_le (tailRank_var_lt hr (.here hu hnv)) hB)
    · exact nomatch h
  | @step n m' u hm _ ih =>
    intro x hx hxv B hB
    have hB' := Nat.le_trans (tailRank_upVar_le hr hm) hB
    rcases hi.cons n x (.var m') hx hm with h | h
    · rcases h with h | h
      · exact absurd h (hxv _)
      · cases hi.just.step h with
        | varR hl => exact ih x hl hxv B hB'
        | viaR hl h₁ h₂ _ _ hR =>
          exact .cons hR hxv h₁ h₂ (Nat.lt_of_lt_of_le (tailRank_lower_lt hr hl h₁) hB')
            (ih _ hl h₁ B hB')
        | varL => exact absurd rfl (hxv _)
        | viaL => exact absurd rfl (hxv _)
    · exact nomatch h

/-- A variable below a non-variable, one layer. -/
theorem stepVarNonvar (hi : Inv s) (hn : LogNAC s) (hl : Logged s (.var w) u)
    (hnv : ∀ x, u ≠ .var x) : St s (.gvar w) u.toTy := by
  rcases hl with h | h
  · exact absurd h.symm (hnv w)
  · cases hi.just.step h with
    | absR => exact .abs
    | varL hu => exact .defL (defsOf.clo (.here hu hnv)) (stepRefl u)
    | viaL hb hbv hba _ hR => exact .defL (defsOf.clo (.here hb hbv)) (stepNonvar hi hn hR hba hbv hnv)
    | varR => exact absurd rfl (hnv _)
    | viaR => exact absurd rfl (hnv _)

/-- **Variable lower bounds**: a variable lower bound `w` of `m` is below
every upper bound reachable from `m`, one layer. -/
theorem stepVarLower (hi : Inv s) (hn : LogNAC s) (hc : Clo s.bounds m u) :
    ∀ w, SType.var w ∈ (s.bounds m).lower → St s (.gvar w) u.toTy := by
  induction hc with
  | @here n u hu hnv =>
    intro w hw
    rcases hi.cons n (.var w) u hw hu with h | h
    · exact stepVarNonvar hi hn h hnv
    · exact nomatch h
  | @step n m' u hm hc ih =>
    intro w hw
    rcases hi.cons n (.var w) (.var m') hw hm with h | h
    · rcases h with h | h
      · cases h; exact .defL (defsOf.clo (hc)) (stepRefl u)
      · cases hi.just.step h with
        | varL hu' => exact .defL (defsOf.clo (.step hu' hc)) (stepRefl u)
        | varR hl => exact ih w hl
        | viaL _ _ _ hbv => exact absurd rfl (hbv _)
        | viaR _ _ _ hav => exact absurd rfl (hav _)
    · exact nomatch h

/-- One layer for any accepted constraint between types whose left side is
not `Abs` (or which is reflexive). -/
theorem stepTy (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat} (hr : TailRanked s rank)
    (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) : St s a.toTy b.toTy := by
  rcases hl with rfl | hl
  · exact stepRefl a
  · cases hi.just.step hl with
    | absR => exact .abs
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | @record fa ta _ _ fb tb =>
      exact .record fun l => .base (SolR.fld (a := .record fa ta) (b := .record fb tb) (l := l) (.inr hl))
    | varL hub =>
      match b with
      | .var w =>
        exact .defR fun τ hτ => by
          rcases hτ with ⟨u, hc, rfl⟩ | ⟨ht, rfl⟩
          · exact .defL (defsOf.clo (.step hub hc)) (stepRefl u)
          · exact (TyVar.under hl ht).le_top
      | .prim _ => exact .defL (defsOf.clo (.here hub (fun _ h => nomatch h))) (stepRefl _)
      | .arrow _ _ => exact .defL (defsOf.clo (.here hub (fun _ h => nomatch h))) (stepRefl _)
      | .record _ _ => exact .defL (defsOf.clo (.here hub (fun _ h => nomatch h))) (stepRefl _)
      | .abs => exact .defL (defsOf.clo (.here hub (fun _ h => nomatch h))) (stepRefl _)
    | @varR v _ hlb =>
      refine .defR fun τ hτ => ?_
      rcases hτ with ⟨u, hc, rfl⟩ | ⟨ht, rfl⟩
      · cases a with
        | var w => exact stepVarLower hi hn hc w hlb
        | prim _ | arrow _ _ | record _ _ =>
          exact (lower_chain hi hr hc _ hlb (fun _ h => nomatch h) _ (Nat.le_refl _)).step hi hn
            (fun h => nomatch h)
        | abs => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
      · -- `v` stands for a type, so what flows into it is below `⊤`
        cases a with
        | var w => exact (TyVar.under hl ht).le_top
        | prim _ | arrow _ _ | record _ _ => exact .top trivial
        | abs => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | viaL hb hbv hba hnv hR =>
      exact .defL (defsOf.clo (.here hb hbv)) (stepNonvar hi hn hR hba hbv hnv)
    | viaR hl' h₁ h₂ hav haa hR =>
      refine .defR fun τ hτ => ?_
      rcases hτ with ⟨u, hc, rfl⟩ | ⟨_, rfl⟩
      · exact (stepNonvar hi hn hR haa hav h₁).comp
          ((lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _)).step hi hn h₂)
      · exact stepTop haa hav

/-- The field version of `stepVarLower`, given field steps for accepted
constraints into right sides of smaller tail rank. -/
theorem fieldVarLower (hi : Inv s) {rank : Nat → Nat} (hr : TailRanked s rank) {l : String}
    {B : Nat} (ih : ∀ x y, Logged s x y → tailRank rank y < B →
      St s (x.toTy.field l) (y.toTy.field l))
    (hc : Clo s.bounds m u) : ∀ w, SType.var w ∈ (s.bounds m).lower →
      tailRank rank (.var m) ≤ B → St s ((SType.var w).toTy.field l) (u.toTy.field l) := by
  induction hc with
  | @here n u hu hnv =>
    intro w hw hB
    rcases hi.cons n (.var w) u hw hu with h | h
    · rcases h with h | h
      · exact absurd h.symm (hnv w)
      · cases hi.just.step h with
        | absR => exact .abs
        | varL hu' => exact .projDefL (defsOf.clo (.here hu' hnv)) (stepReflField l u)
        | viaL hb hbv _ _ hR =>
          exact .projDefL (defsOf.clo (.here hb hbv))
            (ih _ _ hR (Nat.lt_of_lt_of_le (tailRank_var_lt hr (.here hu hnv)) hB))
        | varR => exact absurd rfl (hnv _)
        | viaR => exact absurd rfl (hnv _)
    · exact nomatch h
  | @step n m' u hm hc ih' =>
    intro w hw hB
    rcases hi.cons n (.var w) (.var m') hw hm with h | h
    · rcases h with h | h
      · cases h; exact .projDefL (defsOf.clo (hc)) (stepReflField l u)
      · cases hi.just.step h with
        | varL hu' => exact .projDefL (defsOf.clo (.step hu' hc)) (stepReflField l u)
        | varR hl => exact ih' w hl (Nat.le_trans (tailRank_upVar_le hr hm) hB)
        | viaL _ _ _ hbv => exact absurd rfl (hbv _)
        | viaR _ _ _ hav => exact absurd rfl (hav _)
    · exact nomatch h

/-- One layer for a field pair of an accepted constraint with a non-variable
left side, given the result for constraints whose right side has a smaller
tail rank (`ihRank`), or the same tail rank and a smaller size (`ihSize`). -/
theorem stepFieldNV (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat}
    (hr : TailRanked s rank) (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      St s (a.toTy.field l) (u.toTy.field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → St s (a.toTy.field l) (b'.toTy.field l))
    (a : SType) (hav : ∀ w, a ≠ .var w) (l : String) (hl : Logged s a b) :
    St s (a.toTy.field l) (b.toTy.field l) := by
  rcases hl with rfl | hl
  · exact stepReflField l a
  · cases hi.just.step hl with
    | absR => exact .abs
    | arrow => exact .abs
    | @absRecord t fs hf ht =>
      rw [field_record]
      cases hfl : fs.lookup l with
      | some f =>
        cases hf _ (SFields.absPairs_mem fs hfl) with
        | toAbs => exact .abs
        | pre h₀ => exact absurd rfl h₀
      | none =>
        exact ihSize t .abs l (by simp [tailRank, rowView])
          (by simp only [SType.record.sizeOf_spec]; omega) ht
    | @record fa ta fs₀ t₀ fb tb fs₁ t₁ t₀' e₀ e₁ hcom hexp hrest =>
      rw [field_rowView l (.record fa ta), field_rowView l (.record fb tb), e₀, e₁,
        field_record, field_record]
      dsimp only
      have hrest_field := field_restRow l (fs₁.missing fs₀) t₀'
      rw [SFields.missing_lookup] at hrest_field
      have hmiss := SFields.missing_lookup fs₀ l fs₁
      -- the recursive call on the rest constraint, into the right tail `t₁`
      have hrec : Step (defsOf s) (TC (SolR s)) ((restRow (fs₁.missing fs₀) t₀').toTy.field l)
          (t₁.toTy.field l) := by
        have ht : t₁ = (rowView (.record fb tb)).2 := by rw [e₁]
        refine ihSize t₁ _ l ?_ ?_ hrest
        · rw [ht, tailRank_tail]
        · rw [ht]; exact rowView_tail_lt fb tb
      generalize hm : fs₀.missing fs₁ = ms at hexp hmiss
      cases h₁ : fs₁.lookup l with
      | some f₁ =>
        cases h₀ : fs₀.lookup l with
        | some f₀ =>
          dsimp only
          cases hcom _ (SFields.common_mem fs₁ h₁ h₀) with
          | toAbs => exact .abs
          | pre h₀' _ h => exact stepTy hi hn hr h (.inl h₀')
        | none =>
          dsimp only
          simp only [h₀, h₁, Option.isSome, Bool.false_eq_true, ite_false] at hmiss
          cases hexp with
          | none => simp [SFields.lookup] at hmiss
          | abs _ hab =>
            cases hab _ (SFields.absPairs_mem _ hmiss) with
            | toAbs => exact .abs
            | pre h₀' => exact absurd rfl h₀'
          | varAbsent K hab hp =>
            -- `l` is not present, so it is absent: checked against `Abs`
            have hk : l ∈ K := by
              by_cases hk : l ∈ K
              · exact hk
              · have := SFields.presentIn_lookup K l ms
                rw [hp, hmiss] at this; simp [hk, SFields.lookup] at this
            have hal : (ms.absentIn K).lookup l = some f₁ := by
              rw [SFields.absentIn_lookup]; simp [hk, hmiss]
            cases hab _ (SFields.absPairs_mem _ hal) with
            | toAbs => exact .abs
            | pre h₀' => exact absurd rfl h₀'
          | var K _ hab _ hu hrel =>
            by_cases hk : l ∈ K
            · have hal : (ms.absentIn K).lookup l = some f₁ := by
                rw [SFields.absentIn_lookup]; simp [hk, hmiss]
              cases hab _ (SFields.absPairs_mem _ hal) with
              | toAbs => exact .abs
              | pre h₀' => exact absurd rfl h₀'
            · -- the expansion's upper bound provides `l`, below the expanded field
              have hp : (ms.presentIn K).lookup l = some f₁ := by
                rw [SFields.presentIn_lookup]; simp [hk, hmiss]
              obtain ⟨f', hf', hq⟩ := hrel.lookup hp
              refine .projDefL (defsOf.clo (.here hu (fun _ h => nomatch h))) ?_
              rw [field_record, hf']
              cases hq with
              | toAbs => exact .abs
              | pre h₀' _ h => exact stepTy hi hn hr h (.inl h₀')
      | none =>
        simp only [h₁, Option.isSome, Bool.false_eq_true, ite_false] at hrest_field
        cases h₀ : fs₀.lookup l with
        | some f₀ =>
          dsimp only
          rw [h₀] at hrest_field
          dsimp only at hrest_field
          rw [← hrest_field]
          exact hrec
        | none =>
          dsimp only
          rw [h₀] at hrest_field
          dsimp only at hrest_field
          simp only [h₀, h₁, Option.isSome, Bool.false_eq_true, ite_false] at hmiss
          cases hexp with
          | none => rw [← hrest_field]; exact hrec
          | abs => rw [← hrest_field]; exact hrec
          | varAbsent => rw [← hrest_field]; exact hrec
          | var K _ _ _ hu hrel =>
            refine .projDefL (defsOf.clo (.here hu (fun _ h => nomatch h))) ?_
            have hp : (ms.presentIn K).lookup l = none := by
              rw [SFields.presentIn_lookup]; simp [hmiss]
            rw [field_record, hrel.lookup_none hp]
            dsimp only
            rw [← hrest_field]
            exact hrec
    | varL => exact absurd rfl (hav _)
    | viaL => exact absurd rfl (hav _)
    | @varR v _ hlb =>
      exact .projDefR fun τ hτ => by
        rcases hτ with ⟨u, hc, rfl⟩ | ⟨_, rfl⟩
        · exact (lower_chain hi hr hc a hlb hav _ (Nat.le_refl _)).fieldStep
            fun x y hxy hy => ihRank y x l hy hxy
        · exact .abs
    | viaR hl' h₁ h₂ _ _ hR =>
      exact .projDefR fun τ hτ => by
        rcases hτ with ⟨u, hc, rfl⟩ | ⟨_, rfl⟩
        · exact (Chain.cons hR hav h₁ h₂ (tailRank_lower_lt hr hl' h₁)
            (lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _))).fieldStep
              fun x y hxy hy => ihRank y x l hy hxy
        · exact .abs

/-- One layer for a field pair of an accepted constraint (see `stepFieldNV`;
a variable on the left goes through its bounds). -/
theorem stepFieldCore (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat}
    (hr : TailRanked s rank) (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      St s (a.toTy.field l) (u.toTy.field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → St s (a.toTy.field l) (b'.toTy.field l))
    (a : SType) (l : String) (hl : Logged s a b) :
    St s (a.toTy.field l) (b.toTy.field l) := by
  cases a with
  | prim _ => exact stepFieldNV hi hn hr b ihRank ihSize (.prim _) (fun _ h => nomatch h) l hl
  | arrow _ _ => exact stepFieldNV hi hn hr b ihRank ihSize (.arrow _ _) (fun _ h => nomatch h) l hl
  | record _ _ => exact stepFieldNV hi hn hr b ihRank ihSize (.record _ _) (fun _ h => nomatch h) l hl
  | abs => exact stepFieldNV hi hn hr b ihRank ihSize .abs (fun _ h => nomatch h) l hl
  | var w =>
    rcases hl with rfl | hl
    · exact stepReflField l _
    · cases hi.just.step hl with
      | absR => exact .abs
      | varL hub =>
        cases b with
        | var w =>
          exact .projDefR fun τ hτ => by
            rcases hτ with ⟨u, hc, rfl⟩ | ⟨_, rfl⟩
            · exact .projDefL (defsOf.clo (.step hub hc)) (stepReflField l u)
            · exact .abs
        | prim _ => exact .projDefL (defsOf.clo (.here hub (fun _ h => nomatch h))) (stepReflField l _)
        | arrow _ _ => exact .projDefL (defsOf.clo (.here hub (fun _ h => nomatch h))) (stepReflField l _)
        | record _ _ => exact .projDefL (defsOf.clo (.here hub (fun _ h => nomatch h))) (stepReflField l _)
        | abs => exact .projDefL (defsOf.clo (.here hub (fun _ h => nomatch h))) (stepReflField l _)
      | @varR v _ hlb =>
        exact .projDefR fun τ hτ => by
          rcases hτ with ⟨u, hc, rfl⟩ | ⟨_, rfl⟩
          · exact fieldVarLower hi hr (fun x y hxy hy => ihRank y x l hy hxy) hc w hlb (Nat.le_refl _)
          · exact .abs
      | viaL hb hbv _ _ hR =>
        exact .projDefL (defsOf.clo (.here hb hbv)) (stepFieldNV hi hn hr b ihRank ihSize _ hbv l hR)
      | viaR _ _ _ hav => exact absurd rfl (hav _)

/-- One layer for a field pair of an accepted constraint, by nested
induction: on a bound for the tail rank of the right side, then on a bound
for its size. -/
theorem stepField (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat}
    (hr : TailRanked s rank) (b a : SType) (l : String) (hl : Logged s a b) :
    St s (a.toTy.field l) (b.toTy.field l) := by
  suffices h : ∀ n, ∀ b, tailRank rank b < n → ∀ m, sizeOf b < m → ∀ a l, Logged s a b →
      St s (a.toTy.field l) (b.toTy.field l) from
    h _ b (Nat.lt_succ_self _) _ (Nat.lt_succ_self _) a l hl
  intro n
  induction n with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ihn =>
    intro b hb m
    induction m generalizing b with
    | zero => intro h; exact absurd h (Nat.not_lt_zero _)
    | succ m ihm =>
      intro hm
      exact stepFieldCore hi hn hr b
        (fun u a l hu hl => ihn u (by omega) _ (Nat.lt_succ_self _) a l hl)
        (fun b' a l hb' hs hl => ihm b' (by omega) (by omega) a l hl)

end Steps

/-! ## The solution theorem -/

/-- Every pair of the coinductive relation holds, field pairs included. -/
theorem SolR.sub {s : State} {rank : Nat → Nat} (hi : Inv s) (hn : LogNAC s)
    (hr : TailRanked s rank) (h : SolR s x y) : Sub (defsOf s) x y :=
  Sub.coind_trans (SolR s)
    (fun _ _ h => match h with
      | .ty h ha => stepTy hi hn hr h ha
      | .fld h => stepField hi hn hr _ _ _ h)
    h


/-- **Solution theorem**: in a state satisfying the invariants, every
accepted constraint `a ≤ b` whose left side is not `Abs` holds of the
solution: `θ(a) ≤ θ(b)`, where each type variable is the intersection of
its reachable upper bounds, provided chains of row-variable tails are
acyclic. (Constraints with `Abs` on the left are row constraints; their
fields are related instead, see `stepField`.) -/
theorem solution_rows {s : State} {rank : Nat → Nat} (hi : Inv s)
    (hn : LogNAC s) (hr : TailRanked s rank) (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) :
    Sub (defsOf s) a.toTy b.toTy :=
  SolR.sub hi hn hr (.ty hl ha)

end SimpleSub.Alg
