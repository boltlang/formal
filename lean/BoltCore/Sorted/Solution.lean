import BoltCore.SolutionRows
import BoltCore.Sorted.Sub

/-!
# The solution, sorted (step 2 of `docs/design/sorts.md`)

The algorithm's simple types stay unsorted; a simple type is translated by
the position it is used in:

* `sTy` as a type: a record is `rcd` of its row;
* `sRow` as a row: a record's fields go in front of its tail's row, and the
  top row `Abs` is `⊤`;
* `sField` as a field: `Abs` is `⊤`, any other type `τ` is `pre τ`.

A variable becomes the graph variable of the same number at the sort of its
position. Every graph variable is defined at every sort, by its reachable
non-variable upper bounds translated at that sort (`sdefsOf`). There is no
`⊤` definition for type variables (`TyVar` in the unsorted solution): `⊤` is
the top of the type sort with no side condition, and a selected field is
present by the shape of the typing rule.

The solution theorem relates every accepted constraint at the row sort, and
at the type sort when its left side is not `Abs`: the unsorted proof's
"type-level pairs" and "field pairs" become pairs at the type and row
sorts. The proof is the unsorted one (`SolutionRows.lean`), whose
algorithm-level lemmas (row views, tail ranks, chains through lower bounds)
are reused as they are.
-/

namespace BoltCore.Alg

open State
open BoltCore.Sorted (Srt)

/-! ## Translations -/

mutual
/-- A simple type as a type. (`Abs` is not a type; it is sent to `⊤`, which
only matters for ill-sorted input.) -/
def SType.sTy : SType → Sorted.Ty .ty
  | .var v => .gvar v
  | .prim n => .prim n
  | .arrow a b => .arrow a.sTy b.sTy
  | .record fs t => .rcd (fs.sRowOn t.sRow)
  | .abs => .top

/-- A simple type as a row. Primitive and function types have no fields. -/
def SType.sRow : SType → Sorted.Ty .row
  | .var v => .gvar v
  | .record fs t => fs.sRowOn t.sRow
  | .prim _ | .arrow _ _ | .abs => .top

/-- Fields in front of a row. -/
def SFields.sRowOn : SFields → Sorted.Ty .row → Sorted.Ty .row
  | .nil, ρ => ρ
  | .cons n f fs, ρ =>
    .cons n (match f with
      | .abs => .top
      | f => .pre f.sTy) (fs.sRowOn ρ)
end

/-- A simple type as a field. -/
def SType.sField : SType → Sorted.Ty .field
  | .abs => .top
  | f => .pre f.sTy

/-- A simple type at a sort. -/
def SType.sAt (t : SType) : (srt : Srt) → Sorted.Ty srt
  | .ty => t.sTy
  | .row => t.sRow
  | .field => t.sField

theorem SFields.sRowOn_cons (n : String) (f : SType) (fs : SFields) (ρ : Sorted.Ty .row) :
    (SFields.cons n f fs).sRowOn ρ = .cons n f.sField (fs.sRowOn ρ) := by
  cases f <;> rfl

theorem SType.sField_of_ne {f : SType} (h : f ≠ .abs) : f.sField = .pre f.sTy := by
  cases f <;> first | rfl | exact absurd rfl h

/-! ## The definitions of the solution -/

/-- `gvar n`, at each sort, is the intersection of the reachable
non-variable upper bounds of `n`, translated at that sort. -/
def sdefsOf (s : State) : Sorted.Defs := fun srt n τ => ∃ u, Clo s.bounds n u ∧ τ = u.sAt srt

theorem sdefsOf.clo {s : State} (srt : Srt) (h : Clo s.bounds n u) : sdefsOf s srt n (u.sAt srt) :=
  ⟨u, h, rfl⟩

/-! ## Fields of translated rows -/

theorem field_sRowOn (l : String) (ρ : Sorted.Ty .row) : ∀ fs : SFields,
    (fs.sRowOn ρ).field l = match fs.lookup l with
      | some f => f.sField
      | none => ρ.field l
  | .nil => rfl
  | .cons n f fs => by
    rw [SFields.sRowOn_cons]
    simp only [Sorted.Ty.field, SFields.lookup]
    by_cases h : n = l
    · simp [h]
    · simp [h, field_sRowOn l ρ fs]

theorem sfield_record (l : String) (fs : SFields) (t : SType) :
    (SType.record fs t).sRow.field l = match fs.lookup l with
      | some f => f.sField
      | none => t.sRow.field l :=
  field_sRowOn l _ fs

theorem SFields.sRowOn_append (ρ : Sorted.Ty .row) : ∀ fs gs : SFields,
    (fs.append gs).sRowOn ρ = fs.sRowOn (gs.sRowOn ρ)
  | .nil, _ => rfl
  | .cons n f fs, gs => by
    simp only [SFields.append, SFields.sRowOn_cons]
    rw [SFields.sRowOn_append ρ fs gs]

/-- A row is the record of its flattened fields over its flattened tail. -/
theorem sRow_rowView : ∀ x : SType, x.sRow = (SType.record (rowView x).1 (rowView x).2).sRow
  | .record fs t => by
    simp only [rowView, SType.sRow]
    rw [SFields.sRowOn_append, sRow_rowView t]; rfl
  | .var _ | .prim _ | .arrow _ _ | .abs => rfl

theorem sfield_restRow (l : String) (ex : SFields) (t : SType) :
    (restRow ex t).sRow.field l = match ex.lookup l with
      | some f => f.sField
      | none => t.sRow.field l := by
  cases ex with
  | nil => simp [restRow, SFields.lookup]
  | cons => simp only [restRow]; exact sfield_record ..

/-! ## One layer -/

/-- The coinductive relation: accepted constraints at the type sort (left
side not `Abs`, or reflexive), and at the row sort. -/
inductive SSolR (s : State) : Sorted.Rel where
  | ty : Logged s a b → (a ≠ .abs ∨ a = b) → SSolR s .ty a.sTy b.sTy
  | row : Logged s a b → SSolR s .row a.sRow b.sRow

section Steps

variable {s : State}

abbrev SSt (s : State) {srt : Srt} (x y : Sorted.Ty srt) : Prop := Sorted.Step (sdefsOf s) (Sorted.TC (SSolR s)) x y

theorem SSt.comp {srt : Srt} {x y z : Sorted.Ty srt} (h₁ : SSt s x y) (h₂ : SSt s y z) : SSt s x z :=
  (Sorted.cut h₁ h₂).mono fun _ _ _ h => match h with
    | .inl h => h
    | .inr ⟨_, h₁, h₂⟩ => .trans h₁ h₂

theorem sstepRefl : ∀ a : SType, SSt s a.sTy a.sTy
  | .var _ => .gvar
  | .prim _ => .prim
  | .arrow _ _ => .arrow (.base (.ty (.inl rfl) (.inr rfl))) (.base (.ty (.inl rfl) (.inr rfl)))
  | .record fs t => .rcd (.base (SSolR.row (a := .record fs t) (b := .record fs t) (.inl rfl)))
  | .abs => .top

theorem sstepReflSField (f : SType) : SSt s f.sField f.sField := by
  cases f with
  | abs => exact .top
  | _ => exact .pre (sstepRefl _)

theorem sstepReflField (l : String) : ∀ a : SType, SSt s (a.sRow.field l) (a.sRow.field l)
  | .record fs t => by
    rw [sfield_record]
    cases fs.lookup l with
    | some f => exact sstepReflSField f
    | none => exact sstepReflField l t
  | .var _ => .proj
  | .prim _ | .arrow _ _ | .abs => .top

/-- One layer for an accepted constraint between non-variable types. -/
theorem sstepNonvar (hi : Inv s) (hn : LogNAC s) (hl : Logged s a b) (ha : a ≠ .abs)
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w) : SSt s a.sTy b.sTy := by
  rcases hl with rfl | hl
  · exact sstepRefl a
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => exact absurd rfl ha
    | @record fa ta _ _ fb tb =>
      exact .rcd (.base (SSolR.row (a := .record fa ta) (b := .record fb tb) (.inr hl)))
    | varL => exact absurd rfl (hav _)
    | varR => exact absurd rfl (hbv _)
    | viaL => exact absurd rfl (hav _)
    | viaR => exact absurd rfl (hbv _)

theorem Chain.sstep (hi : Inv s) (hn : LogNAC s) {P : SType → Prop} :
    Chain s P a u → a ≠ .abs → SSt s a.sTy u.sTy
  | .one hl hav hbv _, ha => sstepNonvar hi hn hl ha hav hbv
  | .cons hl hav hbv hba _ c, ha => (sstepNonvar hi hn hl ha hav hbv).comp (c.sstep hi hn hba)

theorem Chain.sfieldStep {P : SType → Prop} {l : String}
    (ih : ∀ x y, Logged s x y → P y → SSt s (x.sRow.field l) (y.sRow.field l)) :
    Chain s P a u → SSt s (a.sRow.field l) (u.sRow.field l)
  | .one hl _ _ hp => ih _ _ hl hp
  | .cons hl _ _ _ hp c => (ih _ _ hl hp).comp (c.sfieldStep ih)

/-- A variable below a non-variable, one layer. -/
theorem sstepVarNonvar (hi : Inv s) (hn : LogNAC s) (hl : Logged s (.var w) u)
    (hnv : ∀ x, u ≠ .var x) : SSt s (.gvar w) u.sTy := by
  rcases hl with h | h
  · exact absurd h.symm (hnv w)
  · cases hi.just.step h with
    | absR => exact .top
    | varL hu => exact .defL (sdefsOf.clo .ty (.here hu hnv)) (sstepRefl u)
    | viaL hb hbv hba _ hR =>
      exact .defL (sdefsOf.clo .ty (.here hb hbv)) (sstepNonvar hi hn hR hba hbv hnv)
    | varR => exact absurd rfl (hnv _)
    | viaR => exact absurd rfl (hnv _)

theorem sstepVarLower (hi : Inv s) (hn : LogNAC s) (hc : Clo s.bounds m u) :
    ∀ w, SType.var w ∈ (s.bounds m).lower → SSt s (.gvar w) u.sTy := by
  induction hc with
  | @here n u hu hnv =>
    intro w hw
    rcases hi.cons n (.var w) u hw hu with h | h
    · exact sstepVarNonvar hi hn h hnv
    · exact nomatch h
  | @step n m' u hm hc ih =>
    intro w hw
    rcases hi.cons n (.var w) (.var m') hw hm with h | h
    · rcases h with h | h
      · cases h; exact .defL (sdefsOf.clo .ty hc) (sstepRefl u)
      · cases hi.just.step h with
        | varL hu' => exact .defL (sdefsOf.clo .ty (.step hu' hc)) (sstepRefl u)
        | varR hl => exact ih w hl
        | viaL _ _ _ hbv => exact absurd rfl (hbv _)
        | viaR _ _ _ hav => exact absurd rfl (hav _)
    · exact nomatch h

/-- One layer at the type sort, for an accepted constraint whose left side
is not `Abs` (or which is reflexive). -/
theorem sstepTy (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat} (hr : TailRanked s rank)
    (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) : SSt s a.sTy b.sTy := by
  rcases hl with rfl | hl
  · exact sstepRefl a
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | @record fa ta _ _ fb tb =>
      exact .rcd (.base (SSolR.row (a := .record fa ta) (b := .record fb tb) (.inr hl)))
    | varL hub =>
      match b with
      | .var w =>
        exact .defR fun τ ⟨u, hc, e⟩ => by
          subst e; exact .defL (sdefsOf.clo .ty (.step hub hc)) (sstepRefl u)
      | .prim _ => exact .defL (sdefsOf.clo .ty (.here hub (fun _ h => nomatch h))) (sstepRefl _)
      | .arrow _ _ => exact .defL (sdefsOf.clo .ty (.here hub (fun _ h => nomatch h))) (sstepRefl _)
      | .record _ _ => exact .defL (sdefsOf.clo .ty (.here hub (fun _ h => nomatch h))) (sstepRefl _)
      | .abs => exact .defL (sdefsOf.clo .ty (.here hub (fun _ h => nomatch h))) (sstepRefl _)
    | @varR v _ hlb =>
      refine .defR fun τ ⟨u, hc, e⟩ => ?_
      subst e
      cases a with
      | var w => exact sstepVarLower hi hn hc w hlb
      | prim _ | arrow _ _ | record _ _ =>
        exact (lower_chain hi hr hc _ hlb (fun _ h => nomatch h) _ (Nat.le_refl _)).sstep hi hn
          (fun h => nomatch h)
      | abs => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | viaL hb hbv hba hnv hR =>
      exact .defL (sdefsOf.clo .ty (.here hb hbv)) (sstepNonvar hi hn hR hba hbv hnv)
    | viaR hl' h₁ h₂ hav haa hR =>
      refine .defR fun τ ⟨u, hc, e⟩ => ?_
      subst e
      exact (sstepNonvar hi hn hR haa hav h₁).comp
        ((lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _)).sstep hi hn h₂)

/-- A present field pair: both sides present and the types related. -/
theorem sstepFieldR (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat} (hr : TailRanked s rank)
    {f₀ f₁ : SType} : FieldR (Logged s) f₀ f₁ → SSt s f₀.sField f₁.sField
  | .toAbs => .top
  | .pre h₀ h₁ h => by
    rw [SType.sField_of_ne h₀, SType.sField_of_ne h₁]
    exact .pre (sstepTy hi hn hr h (.inl h₀))

theorem sfieldVarLower (hi : Inv s) {rank : Nat → Nat} (hr : TailRanked s rank) {l : String}
    {B : Nat} (ih : ∀ x y, Logged s x y → tailRank rank y < B →
      SSt s (x.sRow.field l) (y.sRow.field l))
    (hc : Clo s.bounds m u) : ∀ w, SType.var w ∈ (s.bounds m).lower →
      tailRank rank (.var m) ≤ B → SSt s ((SType.var w).sRow.field l) (u.sRow.field l) := by
  induction hc with
  | @here n u hu hnv =>
    intro w hw hB
    rcases hi.cons n (.var w) u hw hu with h | h
    · rcases h with h | h
      · exact absurd h.symm (hnv w)
      · cases hi.just.step h with
        | absR => exact .top
        | varL hu' => exact .projDefL (sdefsOf.clo .row (.here hu' hnv)) (sstepReflField l u)
        | viaL hb hbv _ _ hR =>
          exact .projDefL (sdefsOf.clo .row (.here hb hbv))
            (ih _ _ hR (Nat.lt_of_lt_of_le (tailRank_var_lt hr (.here hu hnv)) hB))
        | varR => exact absurd rfl (hnv _)
        | viaR => exact absurd rfl (hnv _)
    · exact nomatch h
  | @step n m' u hm hc ih' =>
    intro w hw hB
    rcases hi.cons n (.var w) (.var m') hw hm with h | h
    · rcases h with h | h
      · cases h; exact .projDefL (sdefsOf.clo .row hc) (sstepReflField l u)
      · cases hi.just.step h with
        | varL hu' => exact .projDefL (sdefsOf.clo .row (.step hu' hc)) (sstepReflField l u)
        | varR hl => exact ih' w hl (Nat.le_trans (tailRank_upVar_le hr hm) hB)
        | viaL _ _ _ hbv => exact absurd rfl (hbv _)
        | viaR _ _ _ hav => exact absurd rfl (hav _)
    · exact nomatch h

/-- One layer for a field of an accepted constraint with a non-variable left
side (`stepFieldNV`, sorted). -/
theorem sstepFieldNV (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat}
    (hr : TailRanked s rank) (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      SSt s (a.sRow.field l) (u.sRow.field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → SSt s (a.sRow.field l) (b'.sRow.field l))
    (a : SType) (hav : ∀ w, a ≠ .var w) (l : String) (hl : Logged s a b) :
    SSt s (a.sRow.field l) (b.sRow.field l) := by
  rcases hl with rfl | hl
  · exact sstepReflField l a
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow => exact .top
    | @absRecord t fs hf ht =>
      rw [sfield_record]
      cases hfl : fs.lookup l with
      | some f =>
        cases hf _ (SFields.absPairs_mem fs hfl) with
        | toAbs => exact .top
        | pre h₀ => exact absurd rfl h₀
      | none =>
        exact ihSize t .abs l (by simp [tailRank, rowView])
          (by simp only [SType.record.sizeOf_spec]; omega) ht
    | @record fa ta fs₀ t₀ fb tb fs₁ t₁ t₀' e₀ e₁ hcom hexp hrest =>
      rw [sRow_rowView (.record fa ta), sRow_rowView (.record fb tb), e₀, e₁,
        sfield_record, sfield_record]
      dsimp only
      have hrest_field := sfield_restRow l (fs₁.missing fs₀) t₀'
      rw [SFields.missing_lookup] at hrest_field
      have hmiss := SFields.missing_lookup fs₀ l fs₁
      have hrec : SSt s ((restRow (fs₁.missing fs₀) t₀').sRow.field l) (t₁.sRow.field l) := by
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
          exact sstepFieldR hi hn hr (hcom _ (SFields.common_mem fs₁ h₁ h₀))
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
              refine .projDefL (sdefsOf.clo .row (.here hu (fun _ h => nomatch h))) ?_
              show SSt s ((SType.record _ _).sRow.field l) _
              rw [sfield_record, hf']
              exact sstepFieldR hi hn hr hq
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
            refine .projDefL (sdefsOf.clo .row (.here hu (fun _ h => nomatch h))) ?_
            have hp : (ms.presentIn K).lookup l = none := by
              rw [SFields.presentIn_lookup]; simp [hmiss]
            show SSt s ((SType.record _ _).sRow.field l) _
            rw [sfield_record, hrel.lookup_none hp]
            dsimp only
            rw [← hrest_field]
            exact hrec
    | varL => exact absurd rfl (hav _)
    | viaL => exact absurd rfl (hav _)
    | @varR v _ hlb =>
      exact .projDefR fun τ ⟨u, hc, e⟩ => by
        subst e
        exact (lower_chain hi hr hc a hlb hav _ (Nat.le_refl _)).sfieldStep
          fun x y hxy hy => ihRank y x l hy hxy
    | viaR hl' h₁ h₂ _ _ hR =>
      exact .projDefR fun τ ⟨u, hc, e⟩ => by
        subst e
        exact (Chain.cons hR hav h₁ h₂ (tailRank_lower_lt hr hl' h₁)
          (lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _))).sfieldStep
            fun x y hxy hy => ihRank y x l hy hxy

theorem sstepFieldCore (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat}
    (hr : TailRanked s rank) (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      SSt s (a.sRow.field l) (u.sRow.field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → SSt s (a.sRow.field l) (b'.sRow.field l))
    (a : SType) (l : String) (hl : Logged s a b) :
    SSt s (a.sRow.field l) (b.sRow.field l) := by
  cases a with
  | prim _ => exact sstepFieldNV hi hn hr b ihRank ihSize (.prim _) (fun _ h => nomatch h) l hl
  | arrow _ _ => exact sstepFieldNV hi hn hr b ihRank ihSize (.arrow _ _) (fun _ h => nomatch h) l hl
  | record _ _ => exact sstepFieldNV hi hn hr b ihRank ihSize (.record _ _) (fun _ h => nomatch h) l hl
  | abs => exact sstepFieldNV hi hn hr b ihRank ihSize .abs (fun _ h => nomatch h) l hl
  | var w =>
    rcases hl with rfl | hl
    · exact sstepReflField l _
    · cases hi.just.step hl with
      | absR => exact .top
      | varL hub =>
        cases b with
        | var w =>
          exact .projDefR fun τ ⟨u, hc, e⟩ => by
            subst e; exact .projDefL (sdefsOf.clo .row (.step hub hc)) (sstepReflField l u)
        | prim _ | arrow _ _ | record _ _ | abs =>
          exact .projDefL (sdefsOf.clo .row (.here hub (fun _ h => nomatch h))) (sstepReflField l _)
      | @varR v _ hlb =>
        exact .projDefR fun τ ⟨u, hc, e⟩ => by
          subst e
          exact sfieldVarLower hi hr (fun x y hxy hy => ihRank y x l hy hxy) hc w hlb (Nat.le_refl _)
      | viaL hb hbv _ _ hR =>
        exact .projDefL (sdefsOf.clo .row (.here hb hbv)) (sstepFieldNV hi hn hr b ihRank ihSize _ hbv l hR)
      | viaR _ _ _ hav => exact absurd rfl (hav _)

theorem sstepField (hi : Inv s) (hn : LogNAC s) {rank : Nat → Nat}
    (hr : TailRanked s rank) (b a : SType) (l : String) (hl : Logged s a b) :
    SSt s (a.sRow.field l) (b.sRow.field l) := by
  suffices h : ∀ n, ∀ b, tailRank rank b < n → ∀ m, sizeOf b < m → ∀ a l, Logged s a b →
      SSt s (a.sRow.field l) (b.sRow.field l) from
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
      exact sstepFieldCore hi hn hr b
        (fun u a l hu hl => ihn u (by omega) _ (Nat.lt_succ_self _) a l hl)
        (fun b' a l hb' hs hl => ihm b' (by omega) (by omega) a l hl)

end Steps

/-! ## The solution theorem -/

theorem SSolR.sub {s : State} {rank : Nat → Nat} (hi : Inv s) (hn : LogNAC s)
    (hr : TailRanked s rank) {srt : Srt} {x y : Sorted.Ty srt} (h : SSolR s srt x y) :
    Sorted.Sub (sdefsOf s) x y :=
  Sorted.Sub.coind_trans (SSolR s)
    (fun _ _ _ h => match h with
      | .ty h ha => sstepTy hi hn hr h ha
      | .row h => .row fun l => sstepField hi hn hr _ _ l h)
    h

/-- **Solution theorem, sorted**: every accepted constraint holds of the
solution at the row sort, and at the type sort when its left side is not
`Abs`. -/
theorem ssolution_ty {s : State} {rank : Nat → Nat} (hi : Inv s) (hn : LogNAC s)
    (hr : TailRanked s rank) (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) :
    Sorted.Sub (sdefsOf s) a.sTy b.sTy :=
  SSolR.sub hi hn hr (.ty hl ha)

theorem ssolution_row {s : State} {rank : Nat → Nat} (hi : Inv s) (hn : LogNAC s)
    (hr : TailRanked s rank) (hl : Logged s a b) : Sorted.Sub (sdefsOf s) a.sRow b.sRow :=
  SSolR.sub hi hn hr (.row hl)

end BoltCore.Alg
