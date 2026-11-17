import SimpleSub.Certificate

/-!
# The solution under a generalization

Generalizing a `let` reads its generalized variables `A` as arbitrary
types: an *instance* `I α` for each `α ∈ A`, required only to satisfy
`α`'s bounds (`GenHyp`). Every other variable keeps its graph variable.
This file proves that every accepted constraint still holds under such an
interpretation (`solution_gen`), which is what typing the right-hand side
of a `let` at each instance of its scheme needs.

The proof reuses the solution theorem. Variables outside `A` have bounds
that do not mention `A`, so a constraint that does not mention `A` is read
as before, and everything the old proof relates holds (`SolR.sub`). A
constraint that mentions `A` decomposes structurally; where it reaches a
variable of `A`, that variable's bounds give the subtyping fact directly,
so no graph definition of it is needed.
-/

namespace SimpleSub.Alg

open State

/-! ## Interpretations that agree with the solution outside `A` -/

/-- `t` does not mention the variables `A`. -/
def Av (A : List Nat) (t : SType) : Prop := ∀ w ∈ t.vars, w ∉ A

instance (A : List Nat) (t : SType) : Decidable (Av A t) := by
  unfold Av; infer_instance

/-- What generalizing the variables `A` of the state `s` needs of the
instance `I`: it is the solution outside `A`, bounds outside `A` do not
mention `A`, and inside `A` it satisfies the bounds, as subtyping and
field by field, and reads ordinary type variables as types (below `⊤`). -/
structure GenHyp (s : State) (A : List Nat) (I : Nat → Ty) : Prop where
  out : ∀ v, v ∉ A → I v = .gvar v
  avoid : ∀ v, v ∉ A → ∀ b, (b ∈ (s.bounds v).upper ∨ b ∈ (s.bounds v).lower) → Av A b
  up : ∀ α ∈ A, ∀ u ∈ (s.bounds α).upper, Holds (defsOf s) (I α) (u.interp I)
  low : ∀ α ∈ A, ∀ l ∈ (s.bounds α).lower,
    (l ≠ .abs → Sub (defsOf s) (l.interp I) (I α)) ∧
      ∀ f, Sub (defsOf s) ((l.interp I).field f) ((I α).field f)
  top : ∀ α ∈ A, s.kind α = [] → Sub (defsOf s) (I α) .top

/-- An instance reads every ordinary type variable as a type. -/
theorem GenHyp.le_top {s : State} {A : List Nat} {I : Nat → Ty} (hg : GenHyp s A I) {v : Nat}
    (hk : s.kind v = []) : Sub (defsOf s) (I v) .top := by
  by_cases hv : v ∈ A
  · exact hg.top v hv hk
  · rw [hg.out v hv]; exact Sub.of_step (TyVar.here hk).le_top

section
variable {s : State} {A : List Nat} {I : Nat → Ty}

theorem Av.var {v : Nat} : Av A (.var v) ↔ v ∉ A := by simp [Av, SType.vars]

mutual
theorem SType.interp_avoid (hg : GenHyp s A I) : ∀ t : SType, Av A t → t.interp I = t.toTy
  | .var v, h => hg.out v (Av.var.1 h)
  | .prim _, _ | .abs, _ => rfl
  | .arrow a b, h => by
    simp only [SType.interp, SType.toTy]
    rw [SType.interp_avoid hg a fun w hw => h w (by simp [SType.vars, hw]),
      SType.interp_avoid hg b fun w hw => h w (by simp [SType.vars, hw])]
  | .record fs t, h => by
    simp only [SType.interp, SType.toTy]
    rw [SFields.interp_avoid hg fs fun w hw => h w (by simp [SType.vars, hw]),
      SType.interp_avoid hg t fun w hw => h w (by simp [SType.vars, hw])]

theorem SFields.interp_avoid (hg : GenHyp s A I) :
    ∀ fs : SFields, (∀ w ∈ fs.vars, w ∉ A) → fs.interp I = fs.toFields
  | .nil, _ => rfl
  | .cons _ f fs, h => by
    simp only [SFields.interp, SFields.toFields]
    rw [SType.interp_avoid hg f fun w hw => h w (by simp [SFields.vars, hw]),
      SFields.interp_avoid hg fs fun w hw => h w (by simp [SFields.vars, hw])]
end

/-! ## Fields under an interpretation -/

theorem SFields.interp_lookup (I : Nat → Ty) : ∀ (fs : SFields) (l : String),
    (fs.interp I).lookup l = (fs.lookup l).map (SType.interp I)
  | .nil, _ => rfl
  | .cons n f fs, l => by
    simp only [SFields.interp, Fields.lookup, SFields.lookup]
    by_cases h : n = l
    · simp [h]
    · simp [h, SFields.interp_lookup I fs l]

theorem field_recordI (I : Nat → Ty) (l : String) (fs : SFields) (t : SType) :
    ((SType.record fs t).interp I).field l =
      match fs.lookup l with
      | some f => f.interp I
      | none => (t.interp I).field l := by
  simp only [SType.interp, Ty.field, SFields.interp_lookup]
  cases fs.lookup l <;> rfl

theorem field_rowViewI (I : Nat → Ty) (l : String) : ∀ x : SType,
    (x.interp I).field l = ((SType.record (rowView x).1 (rowView x).2).interp I).field l
  | .record fs t => by
    have ih := field_rowViewI I l t
    simp only [rowView]
    rw [field_recordI, field_recordI, SFields.lookup_append]
    cases fs.lookup l with
    | some f => rfl
    | none => rw [ih, field_recordI]
  | .var _ | .prim _ | .arrow _ _ | .abs => by
    simp [rowView, field_recordI, SFields.lookup]

theorem field_restRowI (I : Nat → Ty) (l : String) (ex : SFields) (t : SType) :
    ((restRow ex t).interp I).field l =
      match ex.lookup l with
      | some f => f.interp I
      | none => (t.interp I).field l := by
  cases ex with
  | nil => simp [restRow, SFields.lookup]
  | cons => simp only [restRow]; exact field_recordI ..

end

/-! ## One layer -/

/-- The coinductive relation: accepted constraints and their field
projections, read through `I`, and every subtyping fact. -/
inductive SolG (s : State) (I : Nat → Ty) : Ty → Ty → Prop where
  | ty : Logged s a b → (a ≠ .abs ∨ a = b) → SolG s I (a.interp I) (b.interp I)
  | fld : Logged s a b → SolG s I ((a.interp I).field l) ((b.interp I).field l)
  | sub : Sub (defsOf s) x y → SolG s I x y

abbrev StG (s : State) (I : Nat → Ty) (x y : Ty) : Prop :=
  Step (defsOf s) (TC (SolG s I)) x y

section Steps

variable {s : State} {A : List Nat} {I : Nat → Ty} {rank : Nat → Nat}

theorem StG.comp (h₁ : StG s I x y) (h₂ : StG s I y z) : StG s I x z :=
  (cut h₁ _ h₂).mono fun _ _ h => match h with
    | .inl h => h
    | .inr ⟨_, h₁, h₂⟩ => .trans h₁ h₂

theorem _root_.SimpleSub.TC.map {R R' : Ty → Ty → Prop} (hR : ∀ x y, R x y → R' x y) : TC R x y → TC R' x y
  | .base h => .base (hR _ _ h)
  | .trans h₁ h₂ => .trans (h₁.map hR) (h₂.map hR)

/-- A subtyping fact, as one layer. -/
theorem StG.of_sub (h : Sub (defsOf s) x y) : StG s I x y :=
  h.step.mono fun _ _ h => .base (.sub h)

/-- A layer of the old proof is a layer here: its pairs all hold. -/
theorem St.toG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (h : St s x y) :
    StG s I x y :=
  h.mono fun _ _ h => h.map fun _ _ h => .sub (SolR.sub hi hn hr h)

/-- A type other than `Abs` and a variable is below `⊤`, however read. -/
theorem stepTopG : ∀ {a : SType}, a ≠ .abs → (∀ w, a ≠ .var w) → StG s I (a.interp I) .top
  | .prim _, _, _ | .arrow _ _, _, _ | .record _ _, _, _ => .top trivial
  | .abs, h, _ => absurd rfl h
  | .var w, _, h => absurd rfl (h w)

/-- One layer for an accepted constraint between non-variable types. -/
theorem stepNonvarG (hi : Inv s) (hn : LogNAC s) (hl : Logged s a b) (ha : a ≠ .abs)
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w) : StG s I (a.interp I) (b.interp I) := by
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .abs
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => exact absurd rfl ha
    | @record fa ta _ _ fb tb =>
      exact .record fun l => .base (SolG.fld (a := .record fa ta) (b := .record fb tb) (l := l) (.inr hl))
    | varL => exact absurd rfl (hav _)
    | varR => exact absurd rfl (hbv _)
    | viaL => exact absurd rfl (hav _)
    | viaR => exact absurd rfl (hbv _)

/-- One layer for an accepted constraint, read through a generalization. -/
theorem stepTyG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) : StG s I (a.interp I) (b.interp I) := by
  by_cases hav : Av A a ∧ Av A b
  · rw [SType.interp_avoid hg a hav.1, SType.interp_avoid hg b hav.2]
    exact (stepTy hi hn hr hl ha).toG hi hn hr
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .abs
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | @record fa ta _ _ fb tb =>
      exact .record fun l => .base (SolG.fld (a := .record fa ta) (b := .record fb tb) (l := l) (.inr hl))
    | @varL v _ hub =>
      by_cases hv : v ∈ A
      · exact .of_sub (hg.up v hv _ hub).1
      · exact absurd ⟨Av.var.2 hv, hg.avoid v hv _ (.inl hub)⟩ hav
    | @varR v _ hlb =>
      by_cases hv : v ∈ A
      · have ha' : a ≠ .abs := by
          rcases ha with ha | ha
          · exact ha
          · subst ha; exact fun h => nomatch h
        exact .of_sub ((hg.low v hv _ hlb).1 ha')
      · exact absurd ⟨hg.avoid v hv _ (.inr hlb), Av.var.2 hv⟩ hav
    | @viaL v b' _ hb hbv hba hnv hR =>
      by_cases hv : v ∈ A
      · exact (StG.of_sub (hg.up v hv _ hb).1).comp (stepNonvarG hi hn hR hba hbv hnv)
      · have h := stepNonvarG (I := I) hi hn hR hba hbv hnv
        rw [SType.interp_avoid hg b' (hg.avoid v hv _ (.inl hb))] at h
        show StG s I (I v) _
        rw [hg.out v hv]
        exact .defL (defsOf.clo (.here hb hbv)) h
    | @viaR v a' _ hl' h₁ h₂ hav' haa hR =>
      by_cases hv : v ∈ A
      · exact (stepNonvarG hi hn hR haa hav' h₁).comp (StG.of_sub ((hg.low v hv _ hl').1 h₂))
      · show StG s I _ (I v)
        rw [hg.out v hv]
        refine .defR fun τ hτ => ?_
        rcases hτ with ⟨u, hc, rfl⟩ | ⟨_, rfl⟩
        · have h := stepNonvarG (I := I) hi hn hR haa hav' h₁
          rw [SType.interp_avoid hg a' (hg.avoid v hv _ (.inr hl'))] at h
          exact h.comp
            (((lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _)).step hi hn h₂).toG hi hn hr)
        · exact stepTopG haa hav'

/-- From a variable to one of its non-variable upper bounds, at a field:
through the graph definition outside `A`, through the bound inside. -/
theorem boundField (hg : GenHyp s A I) {ρ : Nat} {x : SType} {l : String} {τ : Ty}
    (hu : x ∈ (s.bounds ρ).upper) (hx : ∀ w, x ≠ .var w)
    (h : StG s I ((x.interp I).field l) τ) : StG s I (((SType.var ρ).interp I).field l) τ := by
  by_cases hρ : ρ ∈ A
  · exact (StG.of_sub ((hg.up ρ hρ x hu).2 l)).comp h
  · show StG s I ((I ρ).field l) τ
    rw [hg.out ρ hρ, SType.interp_avoid hg x (hg.avoid ρ hρ _ (.inl hu))] at *
    exact .projDefL (defsOf.clo (.here hu hx)) h

/-- One layer for a field pair of an accepted constraint with a non-variable
left side, read through a generalization (see `stepFieldNV`). -/
theorem stepFieldNVG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      StG s I ((a.interp I).field l) ((u.interp I).field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → StG s I ((a.interp I).field l) ((b'.interp I).field l))
    (a : SType) (hav : ∀ w, a ≠ .var w) (l : String) (hl : Logged s a b) :
    StG s I ((a.interp I).field l) ((b.interp I).field l) := by
  by_cases hA : Av A a ∧ Av A b
  · rw [SType.interp_avoid hg a hA.1, SType.interp_avoid hg b hA.2]
    exact (stepField hi hn hr b a l hl).toG hi hn hr
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .abs
    | arrow => exact .abs
    | @absRecord t fs hf ht =>
      rw [field_recordI]
      cases hfl : fs.lookup l with
      | some f =>
        cases hf _ (SFields.absPairs_mem fs hfl) with
        | toAbs => exact .abs
        | pre h₀ => exact absurd rfl h₀
      | none =>
        exact ihSize t .abs l (by simp [tailRank, rowView])
          (by simp only [SType.record.sizeOf_spec]; omega) ht
    | @record fa ta fs₀ t₀ fb tb fs₁ t₁ t₀' e₀ e₁ hcom hexp hrest =>
      rw [field_rowViewI I l (.record fa ta), field_rowViewI I l (.record fb tb), e₀, e₁,
        field_recordI, field_recordI]
      dsimp only
      have hrest_field := field_restRowI I l (fs₁.missing fs₀) t₀'
      rw [SFields.missing_lookup] at hrest_field
      have hmiss := SFields.missing_lookup fs₀ l fs₁
      have hrec : StG s I (((restRow (fs₁.missing fs₀) t₀').interp I).field l)
          ((t₁.interp I).field l) := by
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
          | pre h₀' _ h => exact stepTyG hi hn hr hg h (.inl h₀')
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
            · have hp : (ms.presentIn K).lookup l = some f₁ := by
                rw [SFields.presentIn_lookup]; simp [hk, hmiss]
              obtain ⟨f', hf', hq⟩ := hrel.lookup hp
              refine boundField hg hu (fun _ h => nomatch h) ?_
              rw [field_recordI, hf']
              cases hq with
              | toAbs => exact .abs
              | pre h₀' _ h => exact stepTyG hi hn hr hg h (.inl h₀')
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
            refine boundField hg hu (fun _ h => nomatch h) ?_
            have hp : (ms.presentIn K).lookup l = none := by
              rw [SFields.presentIn_lookup]; simp [hmiss]
            rw [field_recordI, hrel.lookup_none hp]
            dsimp only
            rw [← hrest_field]
            exact hrec
    | varL => exact absurd rfl (hav _)
    | viaL => exact absurd rfl (hav _)
    | @varR v _ hlb =>
      by_cases hv : v ∈ A
      · exact .of_sub ((hg.low v hv _ hlb).2 l)
      · exact absurd ⟨hg.avoid v hv _ (.inr hlb), Av.var.2 hv⟩ hA
    | @viaR v a' _ hl' h₁ h₂ _ _ hR =>
      have hlt := tailRank_lower_lt hr hl' h₁
      by_cases hv : v ∈ A
      · exact (ihRank a' a l hlt hR).comp (.of_sub ((hg.low v hv _ hl').2 l))
      · show StG s I _ ((I v).field l)
        rw [hg.out v hv]
        refine .projDefR fun τ hτ => ?_
        rcases hτ with ⟨u, hc, rfl⟩ | ⟨_, rfl⟩
        · have h := ihRank a' a l hlt hR
          rw [SType.interp_avoid hg a' (hg.avoid v hv _ (.inr hl'))] at h
          exact h.comp
            (((lower_chain hi hr hc a' hl' h₁ _ (Nat.le_refl _)).fieldStep
              fun x y hxy _ => stepField hi hn hr y x l hxy).toG hi hn hr)
        · exact .abs

/-- One layer for a field pair of an accepted constraint, read through a
generalization (see `stepFieldCore`). -/
theorem stepFieldCoreG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      StG s I ((a.interp I).field l) ((u.interp I).field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → StG s I ((a.interp I).field l) ((b'.interp I).field l))
    (a : SType) (l : String) (hl : Logged s a b) :
    StG s I ((a.interp I).field l) ((b.interp I).field l) := by
  cases a with
  | prim _ => exact stepFieldNVG hi hn hr hg b ihRank ihSize (.prim _) (fun _ h => nomatch h) l hl
  | arrow _ _ =>
    exact stepFieldNVG hi hn hr hg b ihRank ihSize (.arrow _ _) (fun _ h => nomatch h) l hl
  | record _ _ =>
    exact stepFieldNVG hi hn hr hg b ihRank ihSize (.record _ _) (fun _ h => nomatch h) l hl
  | abs => exact stepFieldNVG hi hn hr hg b ihRank ihSize .abs (fun _ h => nomatch h) l hl
  | var w =>
    by_cases hA : Av A (.var w) ∧ Av A b
    · rw [SType.interp_avoid hg _ hA.1, SType.interp_avoid hg b hA.2]
      exact (stepField hi hn hr b _ l hl).toG hi hn hr
    rcases hl with rfl | hl
    · exact .of_sub Sub.refl
    · cases hi.just.step hl with
      | absR => exact .abs
      | varL hub =>
        by_cases hw : w ∈ A
        · exact .of_sub ((hg.up w hw _ hub).2 l)
        · exact absurd ⟨Av.var.2 hw, hg.avoid w hw _ (.inl hub)⟩ hA
      | @varR v _ hlb =>
        by_cases hv : v ∈ A
        · exact .of_sub ((hg.low v hv _ hlb).2 l)
        · exact absurd ⟨hg.avoid v hv _ (.inr hlb), Av.var.2 hv⟩ hA
      | viaL hb hbv _ _ hR =>
        exact boundField hg hb hbv (stepFieldNVG hi hn hr hg b ihRank ihSize _ hbv l hR)
      | viaR _ _ _ hav => exact absurd rfl (hav _)

/-- One layer for a field pair, by nested induction on the tail rank and the
size of the right side (as `stepField`). -/
theorem stepFieldG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (b a : SType) (l : String) (hl : Logged s a b) :
    StG s I ((a.interp I).field l) ((b.interp I).field l) := by
  suffices h : ∀ n, ∀ b, tailRank rank b < n → ∀ m, sizeOf b < m → ∀ a l, Logged s a b →
      StG s I ((a.interp I).field l) ((b.interp I).field l) from
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
      exact stepFieldCoreG hi hn hr hg b
        (fun u a l hu hl => ihn u (by omega) _ (Nat.lt_succ_self _) a l hl)
        (fun b' a l hb' hs hl => ihm b' (by omega) (by omega) a l hl)

end Steps

/-! ## The theorem -/

section
variable {s : State} {A : List Nat} {I : Nat → Ty} {rank : Nat → Nat}

theorem SolG.holds (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (h : SolG s I x y) : Sub (defsOf s) x y :=
  Sub.coind_trans (SolG s I)
    (fun _ _ h => match h with
      | .ty h ha => stepTyG hi hn hr hg h ha
      | .fld h => stepFieldG hi hn hr hg _ _ _ h
      | .sub h => StG.of_sub h)
    h

/-- **The solution under a generalization**: if the instance `I` satisfies
the bounds of the generalized variables (and agrees with the solution
elsewhere), every accepted constraint whose left side is not `Abs` holds
under `I`, as subtyping and field by field. -/
theorem solution_gen (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (hl : Logged s a b) (ha : a ≠ .abs) : Holds (defsOf s) (a.interp I) (b.interp I) :=
  ⟨SolG.holds hi hn hr hg (.ty hl (.inl ha)), fun _ => SolG.holds hi hn hr hg (.fld hl)⟩

end

end SimpleSub.Alg
