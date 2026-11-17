import BoltCore.Certificate

/-!
# The solution under a generalization

Generalizing a `let` reads its generalized variables `A` through an
*interpretation*, which gives each variable a type and a row (`SInterp`):
a generalized variable may be read at either sort, depending on where it
occurs. What generalizing needs of an interpretation (`GenHyp`): outside
`A` it is the solution, bounds outside `A` do not mention `A`, and inside
`A` it satisfies the bounds at the type sort (when the smaller side is not
`Abs`) and at the row sort. Every accepted constraint then still holds
under it (`solution_gen`), which is what typing the right-hand side of a
`let` at each instance of its scheme needs.

The proof reuses the solution theorem. A constraint that does not mention
`A` is read as before (`SolR.sub`). A constraint that mentions `A`
decomposes structurally; where it reaches a variable of `A`, that
variable's bounds give the subtyping fact directly, so no graph definition
of it is needed.
-/

namespace BoltCore.Alg

open State

/-! ## Variables avoided -/

/-- `t` does not mention the variables `A`. -/
def Av (A : List Nat) (t : SType) : Prop := ∀ w ∈ t.vars, w ∉ A

instance (A : List Nat) (t : SType) : Decidable (Av A t) := by
  unfold Av; infer_instance

theorem Av.var {A : List Nat} {v : Nat} : Av A (.var v) ↔ v ∉ A := by simp [Av, SType.vars]

/-! ## Translations under an interpretation -/

/-- An interpretation of the variables, at the type and row sorts. -/
abbrev SInterp := (srt : Srt) → Nat → Ty srt

/-- The solution's interpretation: every variable is its graph variable. -/
def SInterp.gv : SInterp := fun _ v => .gvar v

mutual
def SType.toTyI (I : SInterp) : SType → Ty .ty
  | .var v => I .ty v
  | .prim n => .prim n
  | .arrow a b => .arrow (a.toTyI I) (b.toTyI I)
  | .record fs t => .rcd (fs.toRowOnI I (t.toRowI I))
  | .abs => .top

def SType.toRowI (I : SInterp) : SType → Ty .row
  | .var v => I .row v
  | .record fs t => fs.toRowOnI I (t.toRowI I)
  | .prim _ | .arrow _ _ | .abs => .top

def SFields.toRowOnI (I : SInterp) : SFields → Ty .row → Ty .row
  | .nil, ρ => ρ
  | .cons n f fs, ρ =>
    .cons n (match f with
      | .abs => .top
      | f => .pre (f.toTyI I)) (fs.toRowOnI I ρ)
end

def SType.toFieldI (I : SInterp) : SType → Ty .field
  | .abs => .top
  | f => .pre (f.toTyI I)

theorem SFields.toRowOnI_cons (I : SInterp) (n : String) (f : SType) (fs : SFields)
    (ρ : Ty .row) : (SFields.cons n f fs).toRowOnI I ρ = .cons n (f.toFieldI I) (fs.toRowOnI I ρ) := by
  cases f <;> rfl

theorem SType.toFieldI_of_ne {I : SInterp} {f : SType} (h : f ≠ .abs) : f.toFieldI I = .pre (f.toTyI I) := by
  cases f <;> first | rfl | exact absurd rfl h

mutual
/-- The translations of `Solution.lean` are those under the solution's
interpretation. -/
theorem SType.toTyI_gv_aux : ∀ t : SType, t.toTyI .gv = t.toTy ∧ t.toRowI .gv = t.toRow
  | .var _ | .prim _ | .abs => ⟨rfl, rfl⟩
  | .arrow a b => ⟨by simp only [SType.toTyI, SType.toTy, (SType.toTyI_gv_aux a).1,
      (SType.toTyI_gv_aux b).1], rfl⟩
  | .record fs t => by
    have h := SFields.toRowOnI_gv fs (SType.toTyI_gv_aux t).2
    exact ⟨by simp only [SType.toTyI, SType.toTy, h], by simp only [SType.toRowI, SType.toRow, h]⟩

theorem SFields.toRowOnI_gv : ∀ (fs : SFields) {ρ ρ' : Ty .row}, ρ = ρ' →
    fs.toRowOnI .gv ρ = fs.toRowOn ρ'
  | .nil, _, _, h => h
  | .cons n f fs, _, _, h => by
    rw [SFields.toRowOnI_cons, SFields.toRowOn_cons, SFields.toRowOnI_gv fs h]
    cases f with
    | abs => rfl
    | _ => simp only [SType.toFieldI, SType.toField, (SType.toTyI_gv_aux _).1]
end

theorem SType.toTyI_gv (t : SType) : t.toTyI .gv = t.toTy := (SType.toTyI_gv_aux t).1
theorem SType.toRowI_gv (t : SType) : t.toRowI .gv = t.toRow := (SType.toTyI_gv_aux t).2

/-! ## What generalizing needs -/

/-- What generalizing the variables `A` of `s` needs of the interpretation
`I`: the solution outside `A`, bounds outside `A` that do not mention `A`,
and the bounds of `A` at the type and row sorts. -/
structure GenHyp (s : State) (A : List Nat) (I : SInterp) : Prop where
  out : ∀ srt v, v ∉ A → I srt v = .gvar v
  avoid : ∀ v, v ∉ A → ∀ b, (b ∈ (s.bounds v).upper ∨ b ∈ (s.bounds v).lower) → Av A b
  up : ∀ α ∈ A, ∀ u ∈ (s.bounds α).upper,
    Sub (defsOf s) (I .ty α) (u.toTyI I) ∧ Sub (defsOf s) (I .row α) (u.toRowI I)
  low : ∀ α ∈ A, ∀ l ∈ (s.bounds α).lower,
    (l ≠ .abs → Sub (defsOf s) (l.toTyI I) (I .ty α)) ∧
      Sub (defsOf s) (l.toRowI I) (I .row α)

section
variable {s : State} {A : List Nat} {I : SInterp}

mutual
theorem SType.interp_avoid (hg : GenHyp s A I) :
    ∀ t : SType, Av A t → t.toTyI I = t.toTy ∧ t.toRowI I = t.toRow
  | .var v, h => ⟨hg.out .ty v (Av.var.1 h), hg.out .row v (Av.var.1 h)⟩
  | .prim _, _ | .abs, _ => ⟨rfl, rfl⟩
  | .arrow a b, h => by
    have ha := SType.interp_avoid hg a fun w hw => h w (by simp [SType.vars, hw])
    have hb := SType.interp_avoid hg b fun w hw => h w (by simp [SType.vars, hw])
    exact ⟨by simp only [SType.toTyI, SType.toTy, ha.1, hb.1], rfl⟩
  | .record fs t, h => by
    have ht := SType.interp_avoid hg t fun w hw => h w (by simp [SType.vars, hw])
    have hf := SFields.interp_avoid hg fs (fun w hw => h w (by simp [SType.vars, hw])) ht.2
    exact ⟨by simp only [SType.toTyI, SType.toTy, hf], by simp only [SType.toRowI, SType.toRow, hf]⟩

theorem SFields.interp_avoid (hg : GenHyp s A I) :
    ∀ fs : SFields, (∀ w ∈ fs.vars, w ∉ A) → ∀ {ρ ρ' : Ty .row}, ρ = ρ' →
      fs.toRowOnI I ρ = fs.toRowOn ρ'
  | .nil, _, _, _, h => h
  | .cons n f fs, h, _, _, hρ => by
    rw [SFields.toRowOnI_cons, SFields.toRowOn_cons,
      SFields.interp_avoid hg fs (fun w hw => h w (by simp [SFields.vars, hw])) hρ]
    have hf := SType.interp_avoid hg f fun w hw => h w (by simp [SFields.vars, hw])
    cases f with
    | abs => rfl
    | _ => simp only [SType.toFieldI, SType.toField, hf.1]
end

/-! ## Fields under an interpretation -/

theorem field_toRowOnI (I : SInterp) (l : String) (ρ : Ty .row) : ∀ fs : SFields,
    (fs.toRowOnI I ρ).field l = match fs.lookup l with
      | some f => f.toFieldI I
      | none => ρ.field l
  | .nil => rfl
  | .cons n f fs => by
    rw [SFields.toRowOnI_cons]
    simp only [Ty.field, SFields.lookup]
    by_cases h : n = l
    · simp [h]
    · simp [h, field_toRowOnI I l ρ fs]

theorem field_recordI (I : SInterp) (l : String) (fs : SFields) (t : SType) :
    ((SType.record fs t).toRowI I).field l = match fs.lookup l with
      | some f => f.toFieldI I
      | none => (t.toRowI I).field l :=
  field_toRowOnI I l _ fs

theorem SFields.toRowOnI_append (I : SInterp) (ρ : Ty .row) : ∀ fs gs : SFields,
    (fs.append gs).toRowOnI I ρ = fs.toRowOnI I (gs.toRowOnI I ρ)
  | .nil, _ => rfl
  | .cons n f fs, gs => by
    simp only [SFields.append, SFields.toRowOnI_cons]
    rw [SFields.toRowOnI_append I ρ fs gs]

theorem toRowI_rowView (I : SInterp) : ∀ x : SType,
    x.toRowI I = (SType.record (rowView x).1 (rowView x).2).toRowI I
  | .record fs t => by
    simp only [rowView, SType.toRowI]
    rw [SFields.toRowOnI_append, toRowI_rowView I t]; rfl
  | .var _ | .prim _ | .arrow _ _ | .abs => rfl

theorem field_restRowI (I : SInterp) (l : String) (ex : SFields) (t : SType) :
    ((restRow ex t).toRowI I).field l = match ex.lookup l with
      | some f => f.toFieldI I
      | none => (t.toRowI I).field l := by
  cases ex with
  | nil => simp [restRow, SFields.lookup]
  | cons => simp only [restRow]; exact field_recordI ..

end

/-! ## One layer -/

/-- The coinductive relation: accepted constraints read through `I` at the
type and row sorts, and every subtyping fact. -/
inductive SolG (s : State) (I : SInterp) : Rel where
  | ty : Logged s a b → (a ≠ .abs ∨ a = b) → SolG s I .ty (a.toTyI I) (b.toTyI I)
  | row : Logged s a b → SolG s I .row (a.toRowI I) (b.toRowI I)
  | sub {srt : Srt} {x y : Ty srt} : Sub (defsOf s) x y → SolG s I srt x y

abbrev StG (s : State) (I : SInterp) {srt : Srt} (x y : Ty srt) : Prop :=
  Step (defsOf s) (TC (SolG s I)) x y

theorem _root_.BoltCore.TC.map {R R' : Rel} (hR : ∀ srt x y, R srt x y → R' srt x y)
    {srt : Srt} {x y : Ty srt} : TC R srt x y → TC R' srt x y
  | .base h => .base (hR _ _ _ h)
  | .trans h₁ h₂ => .trans (h₁.map hR) (h₂.map hR)

section Steps

variable {s : State} {A : List Nat} {I : SInterp} {rank : Nat → Nat}

theorem StG.comp {srt : Srt} {x y z : Ty srt} (h₁ : StG s I x y) (h₂ : StG s I y z) :
    StG s I x z :=
  (cut h₁ h₂).mono fun _ _ _ h => match h with
    | .inl h => h
    | .inr ⟨_, h₁, h₂⟩ => .trans h₁ h₂

theorem StG.of_sub {srt : Srt} {x y : Ty srt} (h : Sub (defsOf s) x y) :
    StG s I x y :=
  h.step.mono fun _ _ _ h => .base (.sub h)

theorem St.toG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) {srt : Srt}
    {x y : Ty srt} (h : St s x y) : StG s I x y :=
  h.mono fun _ _ _ h => h.map fun _ _ _ h => .sub (SolR.sub hi hn hr h)

theorem stepNonvarG (hi : Inv s) (hn : LogNAC s) (hl : Logged s a b) (ha : a ≠ .abs)
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w) : StG s I (a.toTyI I) (b.toTyI I) := by
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => exact absurd rfl ha
    | @record fa ta _ _ fb tb =>
      exact .rcd (.base (SolG.row (a := .record fa ta) (b := .record fb tb) (.inr hl)))
    | varL => exact absurd rfl (hav _)
    | varR => exact absurd rfl (hbv _)
    | viaL => exact absurd rfl (hav _)
    | viaR => exact absurd rfl (hbv _)

theorem stepTyG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) : StG s I (a.toTyI I) (b.toTyI I) := by
  by_cases hav : Av A a ∧ Av A b
  · rw [(SType.interp_avoid hg a hav.1).1, (SType.interp_avoid hg b hav.2).1]
    exact (stepTy hi hn hr hl ha).toG hi hn hr
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | @record fa ta _ _ fb tb =>
      exact .rcd (.base (SolG.row (a := .record fa ta) (b := .record fb tb) (.inr hl)))
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
        rw [(SType.interp_avoid hg b' (hg.avoid v hv _ (.inl hb))).1] at h
        show StG s I (I .ty v) _
        rw [hg.out .ty v hv]
        exact .defL (defsOf.clo .ty (.here hb hbv)) h
    | @viaR v a' _ hl' h₁ h₂ hav' haa hR =>
      by_cases hv : v ∈ A
      · exact (stepNonvarG hi hn hR haa hav' h₁).comp (StG.of_sub ((hg.low v hv _ hl').1 h₂))
      · show StG s I _ (I .ty v)
        rw [hg.out .ty v hv]
        refine .defR fun τ ⟨u, hc, e⟩ => ?_
        subst e
        have h := stepNonvarG (I := I) hi hn hR haa hav' h₁
        rw [(SType.interp_avoid hg a' (hg.avoid v hv _ (.inr hl'))).1] at h
        exact h.comp
          (((lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _)).step hi hn h₂).toG hi hn hr)

theorem stepFieldRG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    {f₀ f₁ : SType} : FieldR (Logged s) f₀ f₁ → StG s I (f₀.toFieldI I) (f₁.toFieldI I)
  | .toAbs => .top
  | .pre h₀ h₁ h => by
    rw [SType.toFieldI_of_ne h₀, SType.toFieldI_of_ne h₁]
    exact .pre (stepTyG hi hn hr hg h (.inl h₀))

/-- From a row variable to one of its non-variable upper bounds, at a field:
through the graph definition outside `A`, through the bound inside. -/
theorem boundField (hg : GenHyp s A I) {ρ : Nat} {x : SType} {l : String}
    {τ : Ty .field} (hu : x ∈ (s.bounds ρ).upper) (hx : ∀ w, x ≠ .var w)
    (h : StG s I ((x.toRowI I).field l) τ) : StG s I (((SType.var ρ).toRowI I).field l) τ := by
  by_cases hρ : ρ ∈ A
  · exact (StG.of_sub ((hg.up ρ hρ x hu).2.fields l)).comp h
  · show StG s I ((I .row ρ).field l) τ
    rw [(SType.interp_avoid hg x (hg.avoid ρ hρ _ (.inl hu))).2] at h
    rw [hg.out .row ρ hρ]
    exact .projDefL (defsOf.clo .row (.here hu hx)) h

theorem stepFieldNVG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      StG s I ((a.toRowI I).field l) ((u.toRowI I).field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → StG s I ((a.toRowI I).field l) ((b'.toRowI I).field l))
    (a : SType) (hav : ∀ w, a ≠ .var w) (l : String) (hl : Logged s a b) :
    StG s I ((a.toRowI I).field l) ((b.toRowI I).field l) := by
  by_cases hA : Av A a ∧ Av A b
  · rw [(SType.interp_avoid hg a hA.1).2, (SType.interp_avoid hg b hA.2).2]
    exact (stepField hi hn hr b a l hl).toG hi hn hr
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow => exact .top
    | @absRecord t fs hf ht =>
      rw [field_recordI]
      cases hfl : fs.lookup l with
      | some f =>
        cases hf _ (SFields.absPairs_mem fs hfl) with
        | toAbs => exact .top
        | pre h₀ => exact absurd rfl h₀
      | none =>
        exact ihSize t .abs l (by simp [tailRank, rowView])
          (by simp only [SType.record.sizeOf_spec]; omega) ht
    | @record fa ta fs₀ t₀ fb tb fs₁ t₁ t₀' e₀ e₁ hcom hexp hrest =>
      rw [toRowI_rowView I (.record fa ta), toRowI_rowView I (.record fb tb), e₀, e₁,
        field_recordI, field_recordI]
      dsimp only
      have hrest_field := field_restRowI I l (fs₁.missing fs₀) t₀'
      rw [SFields.missing_lookup] at hrest_field
      have hmiss := SFields.missing_lookup fs₀ l fs₁
      have hrec : StG s I (((restRow (fs₁.missing fs₀) t₀').toRowI I).field l)
          ((t₁.toRowI I).field l) := by
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
          exact stepFieldRG hi hn hr hg (hcom _ (SFields.common_mem fs₁ h₁ h₀))
        | none =>
          dsimp only
          simp only [h₀, h₁, Option.isSome, Bool.false_eq_true, ite_false] at hmiss
          cases hexp with
          | none => simp [SFields.lookup] at hmiss
          | abs _ hab =>
            cases hab _ (SFields.absPairs_mem _ hmiss) with
            | toAbs => exact .top
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
            | toAbs => exact .top
            | pre h₀' => exact absurd rfl h₀'
          | var K _ hab _ hu hrel =>
            by_cases hk : l ∈ K
            · have hal : (ms.absentIn K).lookup l = some f₁ := by
                rw [SFields.absentIn_lookup]; simp [hk, hmiss]
              cases hab _ (SFields.absPairs_mem _ hal) with
              | toAbs => exact .top
              | pre h₀' => exact absurd rfl h₀'
            · have hp : (ms.presentIn K).lookup l = some f₁ := by
                rw [SFields.presentIn_lookup]; simp [hk, hmiss]
              obtain ⟨f', hf', hq⟩ := hrel.lookup hp
              refine boundField hg hu (fun _ h => nomatch h) ?_
              rw [field_recordI, hf']
              exact stepFieldRG hi hn hr hg hq
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
      · exact .of_sub ((hg.low v hv _ hlb).2.fields l)
      · exact absurd ⟨hg.avoid v hv _ (.inr hlb), Av.var.2 hv⟩ hA
    | @viaR v a' _ hl' h₁ h₂ _ _ hR =>
      have hlt := tailRank_lower_lt hr hl' h₁
      by_cases hv : v ∈ A
      · exact (ihRank a' a l hlt hR).comp (.of_sub ((hg.low v hv _ hl').2.fields l))
      · show StG s I _ ((I .row v).field l)
        rw [hg.out .row v hv]
        refine .projDefR fun τ ⟨u, hc, e⟩ => ?_
        subst e
        have h := ihRank a' a l hlt hR
        rw [(SType.interp_avoid hg a' (hg.avoid v hv _ (.inr hl'))).2] at h
        exact h.comp
          (((lower_chain hi hr hc a' hl' h₁ _ (Nat.le_refl _)).fieldStep
            fun x y hxy _ => stepField hi hn hr y x l hxy).toG hi hn hr)

theorem stepFieldCoreG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      StG s I ((a.toRowI I).field l) ((u.toRowI I).field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → StG s I ((a.toRowI I).field l) ((b'.toRowI I).field l))
    (a : SType) (l : String) (hl : Logged s a b) :
    StG s I ((a.toRowI I).field l) ((b.toRowI I).field l) := by
  cases a with
  | prim _ => exact stepFieldNVG hi hn hr hg b ihRank ihSize (.prim _) (fun _ h => nomatch h) l hl
  | arrow _ _ =>
    exact stepFieldNVG hi hn hr hg b ihRank ihSize (.arrow _ _) (fun _ h => nomatch h) l hl
  | record _ _ =>
    exact stepFieldNVG hi hn hr hg b ihRank ihSize (.record _ _) (fun _ h => nomatch h) l hl
  | abs => exact stepFieldNVG hi hn hr hg b ihRank ihSize .abs (fun _ h => nomatch h) l hl
  | var w =>
    by_cases hA : Av A (.var w) ∧ Av A b
    · rw [(SType.interp_avoid hg _ hA.1).2, (SType.interp_avoid hg b hA.2).2]
      exact (stepField hi hn hr b _ l hl).toG hi hn hr
    rcases hl with rfl | hl
    · exact .of_sub Sub.refl
    · cases hi.just.step hl with
      | absR => exact .top
      | varL hub =>
        by_cases hw : w ∈ A
        · exact .of_sub ((hg.up w hw _ hub).2.fields l)
        · exact absurd ⟨Av.var.2 hw, hg.avoid w hw _ (.inl hub)⟩ hA
      | @varR v _ hlb =>
        by_cases hv : v ∈ A
        · exact .of_sub ((hg.low v hv _ hlb).2.fields l)
        · exact absurd ⟨hg.avoid v hv _ (.inr hlb), Av.var.2 hv⟩ hA
      | viaL hb hbv _ _ hR =>
        exact boundField hg hb hbv (stepFieldNVG hi hn hr hg b ihRank ihSize _ hbv l hR)
      | viaR _ _ _ hav => exact absurd rfl (hav _)

theorem stepFieldG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (b a : SType) (l : String) (hl : Logged s a b) :
    StG s I ((a.toRowI I).field l) ((b.toRowI I).field l) := by
  suffices h : ∀ n, ∀ b, tailRank rank b < n → ∀ m, sizeOf b < m → ∀ a l, Logged s a b →
      StG s I ((a.toRowI I).field l) ((b.toRowI I).field l) from
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
variable {s : State} {A : List Nat} {I : SInterp} {rank : Nat → Nat}

theorem SolG.holds (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    {srt : Srt} {x y : Ty srt} (h : SolG s I srt x y) : Sub (defsOf s) x y :=
  Sub.coind_trans (SolG s I)
    (fun _ _ _ h => match h with
      | .ty h ha => stepTyG hi hn hr hg h ha
      | .row h => .row fun l => stepFieldG hi hn hr hg _ _ l h
      | .sub h => StG.of_sub h)
    h

/-- **The solution under a generalization**: every accepted
constraint holds under `I` at the row sort, and at the type sort when its
left side is not `Abs`. -/
theorem solution_gen (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (hl : Logged s a b) :
    (a ≠ .abs → Sub (defsOf s) (a.toTyI I) (b.toTyI I)) ∧
      Sub (defsOf s) (a.toRowI I) (b.toRowI I) :=
  ⟨fun ha => SolG.holds hi hn hr hg (.ty hl (.inl ha)), SolG.holds hi hn hr hg (.row hl)⟩

end

end BoltCore.Alg
