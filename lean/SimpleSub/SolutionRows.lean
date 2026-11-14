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

/-- Chains of row variables through the tails of upper bounds are acyclic:
the tail variable of every (reachable) upper bound of `v` ranks below `v`.
Kinds guarantee this (`kinds_tailRanked` in `Kinds.lean`). -/
def TailRanked (s : State) (rank : Nat → Nat) : Prop :=
  ∀ v u ρ, Clo s.bounds v u → (rowView u).2 = .var ρ → rank ρ < rank v

theorem tailRank_tail (rank : Nat → Nat) (x : SType) :
    tailRank rank (rowView x).2 = tailRank rank x := by
  simp only [tailRank]
  rw [rowView_of_ne_record _ (rowView_tail_ne_record x)]

theorem tailRank_var_lt {s : State} {rank : Nat → Nat} (hr : TailRanked s rank)
    (hc : Clo s.bounds v u) : tailRank rank u < tailRank rank (.var v) := by
  simp only [tailRank, rowView]
  split
  · next ρ h => have := hr v u ρ hc h; omega
  · omega

/-! ## One layer -/

/-- The relation used for the coinduction: accepted constraints, and the
field projections of accepted constraints. -/
inductive SolR (s : State) : Ty → Ty → Prop where
  | ty : Logged s a b → (a ≠ .abs ∨ a = b) → SolR s a.toTy b.toTy
  | fld : Logged s a b → SolR s (a.toTy.field l) (b.toTy.field l)

section Steps

variable {s : State}

theorem stepRefl : ∀ a : SType, Step (defsOf s) (SolR s) a.toTy a.toTy
  | .var _ => .gvar
  | .prim _ => .prim
  | .arrow _ _ => .arrow (.ty (.inl rfl) (.inr rfl)) (.ty (.inl rfl) (.inr rfl))
  | .record fs t => .record fun l =>
    SolR.fld (a := .record fs t) (b := .record fs t) (l := l) (.inl rfl)
  | .abs => .abs

theorem stepReflField (l : String) : ∀ a : SType,
    Step (defsOf s) (SolR s) (a.toTy.field l) (a.toTy.field l)
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
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w) :
    Step (defsOf s) (SolR s) a.toTy b.toTy := by
  rcases hl with rfl | hl
  · exact stepRefl a
  · cases hi.just.step hl with
    | absR => exact .abs
    | arrow h₁ h₂ =>
      exact .arrow (.ty h₁ (.inl (arrow_comps hn hl).1)) (.ty h₂ (.inl (arrow_comps hn hl).2))
    | absRecord => exact absurd rfl ha
    | @record fa ta _ _ fb tb => exact .record (fun l => SolR.fld (a := .record fa ta) (b := .record fb tb) (l := l) (.inr hl))
    | varL => exact absurd rfl (hav _)
    | varR => exact absurd rfl (hbv _)

/-- One layer for any accepted constraint between types whose left side is
not `Abs` (or which is reflexive). -/
theorem stepTy (hi : Inv s) (h₂ : Inv₂ s) (hn : LogNAC s) (hl : Logged s a b)
    (ha : a ≠ .abs ∨ a = b) : Step (defsOf s) (SolR s) a.toTy b.toTy := by
  rcases hl with rfl | hl
  · exact stepRefl a
  · cases hi.just.step hl with
    | absR => exact .abs
    | arrow h₁ h₂ =>
      exact .arrow (.ty h₁ (.inl (arrow_comps hn hl).1)) (.ty h₂ (.inl (arrow_comps hn hl).2))
    | absRecord => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | @record fa ta _ _ fb tb => exact .record (fun l => SolR.fld (a := .record fa ta) (b := .record fb tb) (l := l) (.inr hl))
    | varL hub =>
      match b with
      | .var w =>
        exact .defR fun τ ⟨u, hc, hτ⟩ => by
          subst hτ; exact .defL ⟨u, .step hub hc, rfl⟩ (stepRefl u)
      | .prim _ => exact .defL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (stepRefl _)
      | .arrow _ _ => exact .defL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (stepRefl _)
      | .record _ _ => exact .defL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (stepRefl _)
      | .abs => exact .defL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (stepRefl _)
    | varR hlb =>
      have hnv := h₂.lbNonVar _ a hlb
      have ha' : a ≠ .abs := by
        rcases ha with ha | ha
        · exact ha
        · exact absurd ha (hnv _)
      exact .defR fun τ ⟨u, hc, hτ⟩ => by
        subst hτ
        exact stepNonvar hi hn (clo_logged hi h₂ hc a hlb) ha' hnv hc.nonvar

/-- The row variable `v` is below a record it was expanded against. -/
theorem expansion_bound (hi : Inv s) (hv : Logged s (.var v) (.record ms t)) :
    SType.record ms t ∈ (s.bounds v).upper := by
  rcases hv with h | hv
  · exact nomatch h
  · cases hi.just.step hv with
    | varL hub => exact hub

/-- One layer for a field pair of an accepted constraint, given the result
for constraints whose right side has a smaller tail rank (`ihRank`), or the
same tail rank and a smaller size (`ihSize`). -/
theorem stepFieldCore (hi : Inv s) (h₂ : Inv₂ s) (hn : LogNAC s) {rank : Nat → Nat}
    (hr : TailRanked s rank) (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      Step (defsOf s) (SolR s) (a.toTy.field l) (u.toTy.field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → Step (defsOf s) (SolR s) (a.toTy.field l) (b'.toTy.field l))
    (a : SType) (l : String) (hl : Logged s a b) :
    Step (defsOf s) (SolR s) (a.toTy.field l) (b.toTy.field l) := by
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
      have hrec : Step (defsOf s) (SolR s) ((restRow (fs₁.missing fs₀) t₀').toTy.field l)
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
          | pre h₀' _ h => exact stepTy hi h₂ hn h (.inl h₀')
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
          | var K _ hab _ hv =>
            by_cases hk : l ∈ K
            · have hal : (ms.absentIn K).lookup l = some f₁ := by
                rw [SFields.absentIn_lookup]; simp [hk, hmiss]
              cases hab _ (SFields.absPairs_mem _ hal) with
              | toAbs => exact .abs
              | pre h₀' => exact absurd rfl h₀'
            · refine .projDefL ⟨_, .here (expansion_bound hi hv) (fun _ h => nomatch h), rfl⟩ ?_
              rw [field_record, SFields.presentIn_lookup]
              simp only [hk, hmiss, ite_false]
              exact stepRefl f₁
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
          | var K _ _ _ hv =>
            refine .projDefL ⟨_, .here (expansion_bound hi hv) (fun _ h => nomatch h), rfl⟩ ?_
            rw [field_record, SFields.presentIn_lookup]
            simp only [hmiss, ite_self]
            rw [← hrest_field]
            exact hrec
    | @varL v _ hub =>
      cases b with
      | var w =>
        exact .projDefR fun τ ⟨u, hc, hτ⟩ => by
          subst hτ; exact .projDefL ⟨u, .step hub hc, rfl⟩ (stepReflField l u)
      | prim _ => exact .projDefL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (stepReflField l _)
      | arrow _ _ => exact .projDefL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (stepReflField l _)
      | record _ _ => exact .projDefL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (stepReflField l _)
      | abs => exact .projDefL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (stepReflField l _)
    | @varR v _ hlb =>
      exact .projDefR fun τ ⟨u, hc, hτ⟩ => by
        subst hτ
        exact ihRank u a l (tailRank_var_lt hr hc) (clo_logged hi h₂ hc a hlb)

/-- One layer for a field pair of an accepted constraint, by nested
induction: on a bound for the tail rank of the right side, then on a bound
for its size. -/
theorem stepField (hi : Inv s) (h₂ : Inv₂ s) (hn : LogNAC s) {rank : Nat → Nat}
    (hr : TailRanked s rank) (b a : SType) (l : String) (hl : Logged s a b) :
    Step (defsOf s) (SolR s) (a.toTy.field l) (b.toTy.field l) := by
  suffices h : ∀ n, ∀ b, tailRank rank b < n → ∀ m, sizeOf b < m → ∀ a l, Logged s a b →
      Step (defsOf s) (SolR s) (a.toTy.field l) (b.toTy.field l) from
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
      exact stepFieldCore hi h₂ hn hr b
        (fun u a l hu hl => ihn u (by omega) _ (Nat.lt_succ_self _) a l hl)
        (fun b' a l hb' hs hl => ihm b' (by omega) (by omega) a l hl)

end Steps

/-! ## The solution theorem -/

/-- **Solution theorem**: in a state reached by the algorithm, every
accepted constraint `a ≤ b` whose left side is not `Abs` holds of the
solution: `θ(a) ≤ θ(b)`, where each type variable is the intersection of
its reachable upper bounds, provided chains of row-variable tails are
acyclic. (Constraints with `Abs` on the left are row constraints; their
fields are related instead, see `stepField`.) -/
theorem solution_rows {s : State} {rank : Nat → Nat} (hi : Inv s) (h₂ : Inv₂ s)
    (hn : LogNAC s) (hr : TailRanked s rank) (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) :
    Sub (defsOf s) a.toTy b.toTy :=
  Sub.coind (SolR s)
    (fun _ _ h => match h with
      | .ty h ha => stepTy hi h₂ hn h ha
      | .fld h => stepField hi h₂ hn hr _ _ _ h)
    (.ty hl ha)

end SimpleSub.Alg
