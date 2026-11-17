import BoltCore.Sorted.Solution
import BoltCore.SolutionGen

/-!
# The solution under a generalization, sorted (step 3)

`SolutionGen.lean` over the sorted core. An *interpretation* gives each
variable a type and a row (`SInterp`): a generalized variable may be read
at either sort, depending on where it occurs. What generalizing the
variables `A` needs of an interpretation (`SGenHyp`): outside `A` it is the
solution, and inside `A` it satisfies the bounds at the type sort (when the
smaller side is not `Abs`) and at the row sort.

Compared with the unsorted version, the field-by-field obligations are
bounds at the row sort, and there is no requirement that type variables be
read below `⊤`: `⊤` has no side condition, and a selected field is present
by the shape of the typing rule.
-/

namespace BoltCore.Alg

open State
open BoltCore.Sorted (Srt)

/-! ## Translations under an interpretation -/

/-- An interpretation of the variables, at the type and row sorts. -/
abbrev SInterp := (srt : Srt) → Nat → Sorted.Ty srt

/-- The solution's interpretation: every variable is its graph variable. -/
def SInterp.gv : SInterp := fun _ v => .gvar v

mutual
def SType.sTyI (I : SInterp) : SType → Sorted.Ty .ty
  | .var v => I .ty v
  | .prim n => .prim n
  | .arrow a b => .arrow (a.sTyI I) (b.sTyI I)
  | .record fs t => .rcd (fs.sRowOnI I (t.sRowI I))
  | .abs => .top

def SType.sRowI (I : SInterp) : SType → Sorted.Ty .row
  | .var v => I .row v
  | .record fs t => fs.sRowOnI I (t.sRowI I)
  | .prim _ | .arrow _ _ | .abs => .top

def SFields.sRowOnI (I : SInterp) : SFields → Sorted.Ty .row → Sorted.Ty .row
  | .nil, ρ => ρ
  | .cons n f fs, ρ =>
    .cons n (match f with
      | .abs => .top
      | f => .pre (f.sTyI I)) (fs.sRowOnI I ρ)
end

def SType.sFieldI (I : SInterp) : SType → Sorted.Ty .field
  | .abs => .top
  | f => .pre (f.sTyI I)

theorem SFields.sRowOnI_cons (I : SInterp) (n : String) (f : SType) (fs : SFields)
    (ρ : Sorted.Ty .row) : (SFields.cons n f fs).sRowOnI I ρ = .cons n (f.sFieldI I) (fs.sRowOnI I ρ) := by
  cases f <;> rfl

theorem SType.sFieldI_of_ne {I : SInterp} {f : SType} (h : f ≠ .abs) : f.sFieldI I = .pre (f.sTyI I) := by
  cases f <;> first | rfl | exact absurd rfl h

mutual
/-- The translations of `Solution.lean` are those under the solution's
interpretation. -/
theorem SType.sTyI_gv_aux : ∀ t : SType, t.sTyI .gv = t.sTy ∧ t.sRowI .gv = t.sRow
  | .var _ | .prim _ | .abs => ⟨rfl, rfl⟩
  | .arrow a b => ⟨by simp only [SType.sTyI, SType.sTy, (SType.sTyI_gv_aux a).1,
      (SType.sTyI_gv_aux b).1], rfl⟩
  | .record fs t => by
    have h := SFields.sRowOnI_gv fs (SType.sTyI_gv_aux t).2
    exact ⟨by simp only [SType.sTyI, SType.sTy, h], by simp only [SType.sRowI, SType.sRow, h]⟩

theorem SFields.sRowOnI_gv : ∀ (fs : SFields) {ρ ρ' : Sorted.Ty .row}, ρ = ρ' →
    fs.sRowOnI .gv ρ = fs.sRowOn ρ'
  | .nil, _, _, h => h
  | .cons n f fs, _, _, h => by
    rw [SFields.sRowOnI_cons, SFields.sRowOn_cons, SFields.sRowOnI_gv fs h]
    cases f with
    | abs => rfl
    | _ => simp only [SType.sFieldI, SType.sField, (SType.sTyI_gv_aux _).1]
end

theorem SType.sTyI_gv (t : SType) : t.sTyI .gv = t.sTy := (SType.sTyI_gv_aux t).1
theorem SType.sRowI_gv (t : SType) : t.sRowI .gv = t.sRow := (SType.sTyI_gv_aux t).2

/-! ## What generalizing needs -/

/-- What generalizing the variables `A` of `s` needs of the interpretation
`I`: the solution outside `A`, bounds outside `A` that do not mention `A`,
and the bounds of `A` at the type and row sorts. -/
structure SGenHyp (s : State) (A : List Nat) (I : SInterp) : Prop where
  out : ∀ srt v, v ∉ A → I srt v = .gvar v
  avoid : ∀ v, v ∉ A → ∀ b, (b ∈ (s.bounds v).upper ∨ b ∈ (s.bounds v).lower) → Av A b
  up : ∀ α ∈ A, ∀ u ∈ (s.bounds α).upper,
    Sorted.Sub (sdefsOf s) (I .ty α) (u.sTyI I) ∧ Sorted.Sub (sdefsOf s) (I .row α) (u.sRowI I)
  low : ∀ α ∈ A, ∀ l ∈ (s.bounds α).lower,
    (l ≠ .abs → Sorted.Sub (sdefsOf s) (l.sTyI I) (I .ty α)) ∧
      Sorted.Sub (sdefsOf s) (l.sRowI I) (I .row α)

section
variable {s : State} {A : List Nat} {I : SInterp}

mutual
theorem SType.sI_avoid (hg : SGenHyp s A I) :
    ∀ t : SType, Av A t → t.sTyI I = t.sTy ∧ t.sRowI I = t.sRow
  | .var v, h => ⟨hg.out .ty v (Av.var.1 h), hg.out .row v (Av.var.1 h)⟩
  | .prim _, _ | .abs, _ => ⟨rfl, rfl⟩
  | .arrow a b, h => by
    have ha := SType.sI_avoid hg a fun w hw => h w (by simp [SType.vars, hw])
    have hb := SType.sI_avoid hg b fun w hw => h w (by simp [SType.vars, hw])
    exact ⟨by simp only [SType.sTyI, SType.sTy, ha.1, hb.1], rfl⟩
  | .record fs t, h => by
    have ht := SType.sI_avoid hg t fun w hw => h w (by simp [SType.vars, hw])
    have hf := SFields.sI_avoid hg fs (fun w hw => h w (by simp [SType.vars, hw])) ht.2
    exact ⟨by simp only [SType.sTyI, SType.sTy, hf], by simp only [SType.sRowI, SType.sRow, hf]⟩

theorem SFields.sI_avoid (hg : SGenHyp s A I) :
    ∀ fs : SFields, (∀ w ∈ fs.vars, w ∉ A) → ∀ {ρ ρ' : Sorted.Ty .row}, ρ = ρ' →
      fs.sRowOnI I ρ = fs.sRowOn ρ'
  | .nil, _, _, _, h => h
  | .cons n f fs, h, _, _, hρ => by
    rw [SFields.sRowOnI_cons, SFields.sRowOn_cons,
      SFields.sI_avoid hg fs (fun w hw => h w (by simp [SFields.vars, hw])) hρ]
    have hf := SType.sI_avoid hg f fun w hw => h w (by simp [SFields.vars, hw])
    cases f with
    | abs => rfl
    | _ => simp only [SType.sFieldI, SType.sField, hf.1]
end

/-! ## Fields under an interpretation -/

theorem field_sRowOnI (I : SInterp) (l : String) (ρ : Sorted.Ty .row) : ∀ fs : SFields,
    (fs.sRowOnI I ρ).field l = match fs.lookup l with
      | some f => f.sFieldI I
      | none => ρ.field l
  | .nil => rfl
  | .cons n f fs => by
    rw [SFields.sRowOnI_cons]
    simp only [Sorted.Ty.field, SFields.lookup]
    by_cases h : n = l
    · simp [h]
    · simp [h, field_sRowOnI I l ρ fs]

theorem sfield_recordI (I : SInterp) (l : String) (fs : SFields) (t : SType) :
    ((SType.record fs t).sRowI I).field l = match fs.lookup l with
      | some f => f.sFieldI I
      | none => (t.sRowI I).field l :=
  field_sRowOnI I l _ fs

theorem SFields.sRowOnI_append (I : SInterp) (ρ : Sorted.Ty .row) : ∀ fs gs : SFields,
    (fs.append gs).sRowOnI I ρ = fs.sRowOnI I (gs.sRowOnI I ρ)
  | .nil, _ => rfl
  | .cons n f fs, gs => by
    simp only [SFields.append, SFields.sRowOnI_cons]
    rw [SFields.sRowOnI_append I ρ fs gs]

theorem sRowI_rowView (I : SInterp) : ∀ x : SType,
    x.sRowI I = (SType.record (rowView x).1 (rowView x).2).sRowI I
  | .record fs t => by
    simp only [rowView, SType.sRowI]
    rw [SFields.sRowOnI_append, sRowI_rowView I t]; rfl
  | .var _ | .prim _ | .arrow _ _ | .abs => rfl

theorem sfield_restRowI (I : SInterp) (l : String) (ex : SFields) (t : SType) :
    ((restRow ex t).sRowI I).field l = match ex.lookup l with
      | some f => f.sFieldI I
      | none => (t.sRowI I).field l := by
  cases ex with
  | nil => simp [restRow, SFields.lookup]
  | cons => simp only [restRow]; exact sfield_recordI ..

end

/-! ## One layer -/

/-- The coinductive relation: accepted constraints read through `I` at the
type and row sorts, and every subtyping fact. -/
inductive SSolG (s : State) (I : SInterp) : Sorted.Rel where
  | ty : Logged s a b → (a ≠ .abs ∨ a = b) → SSolG s I .ty (a.sTyI I) (b.sTyI I)
  | row : Logged s a b → SSolG s I .row (a.sRowI I) (b.sRowI I)
  | sub {srt : Srt} {x y : Sorted.Ty srt} : Sorted.Sub (sdefsOf s) x y → SSolG s I srt x y

abbrev SStG (s : State) (I : SInterp) {srt : Srt} (x y : Sorted.Ty srt) : Prop :=
  Sorted.Step (sdefsOf s) (Sorted.TC (SSolG s I)) x y

theorem _root_.BoltCore.Sorted.TC.map {R R' : Sorted.Rel} (hR : ∀ srt x y, R srt x y → R' srt x y)
    {srt : Srt} {x y : Sorted.Ty srt} : Sorted.TC R srt x y → Sorted.TC R' srt x y
  | .base h => .base (hR _ _ _ h)
  | .trans h₁ h₂ => .trans (h₁.map hR) (h₂.map hR)

section Steps

variable {s : State} {A : List Nat} {I : SInterp} {rank : Nat → Nat}

theorem SStG.comp {srt : Srt} {x y z : Sorted.Ty srt} (h₁ : SStG s I x y) (h₂ : SStG s I y z) :
    SStG s I x z :=
  (Sorted.cut h₁ h₂).mono fun _ _ _ h => match h with
    | .inl h => h
    | .inr ⟨_, h₁, h₂⟩ => .trans h₁ h₂

theorem SStG.of_sub {srt : Srt} {x y : Sorted.Ty srt} (h : Sorted.Sub (sdefsOf s) x y) :
    SStG s I x y :=
  h.step.mono fun _ _ _ h => .base (.sub h)

theorem SSt.toG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) {srt : Srt}
    {x y : Sorted.Ty srt} (h : SSt s x y) : SStG s I x y :=
  h.mono fun _ _ _ h => h.map fun _ _ _ h => .sub (SSolR.sub hi hn hr h)

theorem sstepNonvarG (hi : Inv s) (hn : LogNAC s) (hl : Logged s a b) (ha : a ≠ .abs)
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w) : SStG s I (a.sTyI I) (b.sTyI I) := by
  rcases hl with rfl | hl
  · exact .of_sub Sorted.Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => exact absurd rfl ha
    | @record fa ta _ _ fb tb =>
      exact .rcd (.base (SSolG.row (a := .record fa ta) (b := .record fb tb) (.inr hl)))
    | varL => exact absurd rfl (hav _)
    | varR => exact absurd rfl (hbv _)
    | viaL => exact absurd rfl (hav _)
    | viaR => exact absurd rfl (hbv _)

theorem sstepTyG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : SGenHyp s A I)
    (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) : SStG s I (a.sTyI I) (b.sTyI I) := by
  by_cases hav : Av A a ∧ Av A b
  · rw [(SType.sI_avoid hg a hav.1).1, (SType.sI_avoid hg b hav.2).1]
    exact (sstepTy hi hn hr hl ha).toG hi hn hr
  rcases hl with rfl | hl
  · exact .of_sub Sorted.Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | @record fa ta _ _ fb tb =>
      exact .rcd (.base (SSolG.row (a := .record fa ta) (b := .record fb tb) (.inr hl)))
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
      · exact (SStG.of_sub (hg.up v hv _ hb).1).comp (sstepNonvarG hi hn hR hba hbv hnv)
      · have h := sstepNonvarG (I := I) hi hn hR hba hbv hnv
        rw [(SType.sI_avoid hg b' (hg.avoid v hv _ (.inl hb))).1] at h
        show SStG s I (I .ty v) _
        rw [hg.out .ty v hv]
        exact .defL (sdefsOf.clo .ty (.here hb hbv)) h
    | @viaR v a' _ hl' h₁ h₂ hav' haa hR =>
      by_cases hv : v ∈ A
      · exact (sstepNonvarG hi hn hR haa hav' h₁).comp (SStG.of_sub ((hg.low v hv _ hl').1 h₂))
      · show SStG s I _ (I .ty v)
        rw [hg.out .ty v hv]
        refine .defR fun τ ⟨u, hc, e⟩ => ?_
        subst e
        have h := sstepNonvarG (I := I) hi hn hR haa hav' h₁
        rw [(SType.sI_avoid hg a' (hg.avoid v hv _ (.inr hl'))).1] at h
        exact h.comp
          (((lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _)).sstep hi hn h₂).toG hi hn hr)

theorem sstepFieldRG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : SGenHyp s A I)
    {f₀ f₁ : SType} : FieldR (Logged s) f₀ f₁ → SStG s I (f₀.sFieldI I) (f₁.sFieldI I)
  | .toAbs => .top
  | .pre h₀ h₁ h => by
    rw [SType.sFieldI_of_ne h₀, SType.sFieldI_of_ne h₁]
    exact .pre (sstepTyG hi hn hr hg h (.inl h₀))

/-- From a row variable to one of its non-variable upper bounds, at a field:
through the graph definition outside `A`, through the bound inside. -/
theorem sboundField (hg : SGenHyp s A I) {ρ : Nat} {x : SType} {l : String}
    {τ : Sorted.Ty .field} (hu : x ∈ (s.bounds ρ).upper) (hx : ∀ w, x ≠ .var w)
    (h : SStG s I ((x.sRowI I).field l) τ) : SStG s I (((SType.var ρ).sRowI I).field l) τ := by
  by_cases hρ : ρ ∈ A
  · exact (SStG.of_sub ((hg.up ρ hρ x hu).2.fields l)).comp h
  · show SStG s I ((I .row ρ).field l) τ
    rw [(SType.sI_avoid hg x (hg.avoid ρ hρ _ (.inl hu))).2] at h
    rw [hg.out .row ρ hρ]
    exact .projDefL (sdefsOf.clo .row (.here hu hx)) h

theorem sstepFieldNVG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : SGenHyp s A I)
    (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      SStG s I ((a.sRowI I).field l) ((u.sRowI I).field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → SStG s I ((a.sRowI I).field l) ((b'.sRowI I).field l))
    (a : SType) (hav : ∀ w, a ≠ .var w) (l : String) (hl : Logged s a b) :
    SStG s I ((a.sRowI I).field l) ((b.sRowI I).field l) := by
  by_cases hA : Av A a ∧ Av A b
  · rw [(SType.sI_avoid hg a hA.1).2, (SType.sI_avoid hg b hA.2).2]
    exact (sstepField hi hn hr b a l hl).toG hi hn hr
  rcases hl with rfl | hl
  · exact .of_sub Sorted.Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow => exact .top
    | @absRecord t fs hf ht =>
      rw [sfield_recordI]
      cases hfl : fs.lookup l with
      | some f =>
        cases hf _ (SFields.absPairs_mem fs hfl) with
        | toAbs => exact .top
        | pre h₀ => exact absurd rfl h₀
      | none =>
        exact ihSize t .abs l (by simp [tailRank, rowView])
          (by simp only [SType.record.sizeOf_spec]; omega) ht
    | @record fa ta fs₀ t₀ fb tb fs₁ t₁ t₀' e₀ e₁ hcom hexp hrest =>
      rw [sRowI_rowView I (.record fa ta), sRowI_rowView I (.record fb tb), e₀, e₁,
        sfield_recordI, sfield_recordI]
      dsimp only
      have hrest_field := sfield_restRowI I l (fs₁.missing fs₀) t₀'
      rw [SFields.missing_lookup] at hrest_field
      have hmiss := SFields.missing_lookup fs₀ l fs₁
      have hrec : SStG s I (((restRow (fs₁.missing fs₀) t₀').sRowI I).field l)
          ((t₁.sRowI I).field l) := by
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
          exact sstepFieldRG hi hn hr hg (hcom _ (SFields.common_mem fs₁ h₁ h₀))
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
              refine sboundField hg hu (fun _ h => nomatch h) ?_
              rw [sfield_recordI, hf']
              exact sstepFieldRG hi hn hr hg hq
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
            refine sboundField hg hu (fun _ h => nomatch h) ?_
            have hp : (ms.presentIn K).lookup l = none := by
              rw [SFields.presentIn_lookup]; simp [hmiss]
            rw [sfield_recordI, hrel.lookup_none hp]
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
      · show SStG s I _ ((I .row v).field l)
        rw [hg.out .row v hv]
        refine .projDefR fun τ ⟨u, hc, e⟩ => ?_
        subst e
        have h := ihRank a' a l hlt hR
        rw [(SType.sI_avoid hg a' (hg.avoid v hv _ (.inr hl'))).2] at h
        exact h.comp
          (((lower_chain hi hr hc a' hl' h₁ _ (Nat.le_refl _)).sfieldStep
            fun x y hxy _ => sstepField hi hn hr y x l hxy).toG hi hn hr)

theorem sstepFieldCoreG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : SGenHyp s A I)
    (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      SStG s I ((a.sRowI I).field l) ((u.sRowI I).field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → SStG s I ((a.sRowI I).field l) ((b'.sRowI I).field l))
    (a : SType) (l : String) (hl : Logged s a b) :
    SStG s I ((a.sRowI I).field l) ((b.sRowI I).field l) := by
  cases a with
  | prim _ => exact sstepFieldNVG hi hn hr hg b ihRank ihSize (.prim _) (fun _ h => nomatch h) l hl
  | arrow _ _ =>
    exact sstepFieldNVG hi hn hr hg b ihRank ihSize (.arrow _ _) (fun _ h => nomatch h) l hl
  | record _ _ =>
    exact sstepFieldNVG hi hn hr hg b ihRank ihSize (.record _ _) (fun _ h => nomatch h) l hl
  | abs => exact sstepFieldNVG hi hn hr hg b ihRank ihSize .abs (fun _ h => nomatch h) l hl
  | var w =>
    by_cases hA : Av A (.var w) ∧ Av A b
    · rw [(SType.sI_avoid hg _ hA.1).2, (SType.sI_avoid hg b hA.2).2]
      exact (sstepField hi hn hr b _ l hl).toG hi hn hr
    rcases hl with rfl | hl
    · exact .of_sub Sorted.Sub.refl
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
        exact sboundField hg hb hbv (sstepFieldNVG hi hn hr hg b ihRank ihSize _ hbv l hR)
      | viaR _ _ _ hav => exact absurd rfl (hav _)

theorem sstepFieldG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : SGenHyp s A I)
    (b a : SType) (l : String) (hl : Logged s a b) :
    SStG s I ((a.sRowI I).field l) ((b.sRowI I).field l) := by
  suffices h : ∀ n, ∀ b, tailRank rank b < n → ∀ m, sizeOf b < m → ∀ a l, Logged s a b →
      SStG s I ((a.sRowI I).field l) ((b.sRowI I).field l) from
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
      exact sstepFieldCoreG hi hn hr hg b
        (fun u a l hu hl => ihn u (by omega) _ (Nat.lt_succ_self _) a l hl)
        (fun b' a l hb' hs hl => ihm b' (by omega) (by omega) a l hl)

end Steps

/-! ## The theorem -/

section
variable {s : State} {A : List Nat} {I : SInterp} {rank : Nat → Nat}

theorem SSolG.holds (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : SGenHyp s A I)
    {srt : Srt} {x y : Sorted.Ty srt} (h : SSolG s I srt x y) : Sorted.Sub (sdefsOf s) x y :=
  Sorted.Sub.coind_trans (SSolG s I)
    (fun _ _ _ h => match h with
      | .ty h ha => sstepTyG hi hn hr hg h ha
      | .row h => .row fun l => sstepFieldG hi hn hr hg _ _ l h
      | .sub h => SStG.of_sub h)
    h

/-- **The solution under a generalization, sorted**: every accepted
constraint holds under `I` at the row sort, and at the type sort when its
left side is not `Abs`. -/
theorem ssolution_gen (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : SGenHyp s A I)
    (hl : Logged s a b) :
    (a ≠ .abs → Sorted.Sub (sdefsOf s) (a.sTyI I) (b.sTyI I)) ∧
      Sorted.Sub (sdefsOf s) (a.sRowI I) (b.sRowI I) :=
  ⟨fun ha => SSolG.holds hi hn hr hg (.ty hl (.inl ha)), SSolG.holds hi hn hr hg (.row hl)⟩

end

end BoltCore.Alg
