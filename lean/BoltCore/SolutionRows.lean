import BoltCore.Solution
import BoltCore.Sorts

/-!
# The solution theorem

Every accepted constraint holds of the solution (`defsOf`): at the row
sort, and at the type sort when its left side is not `Abs`
(`solution_ty`, `solution_row`). The proof is stated more generally, for
the solution under a generalization (`solution_gen`): the variables `A` of
a `let` are read through an *interpretation* that gives each variable a type
and a row (`SInterp`), required only to satisfy their bounds (`GenHyp`),
while every other variable keeps its graph variable. That is what typing a
`let`'s right-hand side at each instance of its scheme needs; the plain
theorem is the case where nothing is generalized. The coinductive relation (`SolG`) holds
the accepted constraints at both sorts, and every subtyping fact (the
bounds of generalized variables provide some); comparing two rows is a judgement
at the row sort, compared field by field. Proving one layer for a row pair
(`stepField`) follows the algorithm's record case: common fields, labels
supplied by the left tail (through row expansion), extra left fields
flowing into the right tail, and labels in neither.

`Abs` is never a type: it is `⊤` at the field and row sorts. Constraints
with `Abs` on the left are row constraints, related at the row sort only;
`Sorts.lean` keeps `Abs` out of function types, so that their components'
translations as types mean something.

A signature is the union of its argument records, as a type and as a row.
A record below a signature is below one of its argument records
(`StG.sigR`, `StG.sigFieldR`); that record is closed, so its row step needs
no induction on the right side (`stepFieldClosedG`). A signature below a
type is the same statement for each of its argument records (`StG.sigL`,
`StG.sigFieldL`), which are not signatures.

When the right side of a row pair is a row variable `ρ`, the proof has to
look at each of `ρ`'s upper bounds, and recurses through *their* tails
without passing a type constructor. This terminates if chains of row
variables through upper bounds' tails are acyclic (`TailRanked`), which
kinds guarantee (`Kinds.lean`).
-/

namespace BoltCore.Alg

open State

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

theorem SFields.misPairs_mem {l : String} {f : SType} : ∀ fs : SFields,
    fs.lookup l = some f → (SType.missing, f) ∈ fs.misPairs
  | .nil, h => by simp [SFields.lookup] at h
  | .cons n g rest, h => by
    simp only [SFields.lookup] at h
    simp only [SFields.misPairs]
    split at h
    · cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (SFields.misPairs_mem rest h)

theorem SFields.toMisPairs_mem {l : String} {f : SType} : ∀ fs : SFields,
    fs.lookup l = some f → (f, SType.missing) ∈ fs.toMisPairs
  | .nil, h => by simp [SFields.lookup] at h
  | .cons n g rest, h => by
    simp only [SFields.lookup] at h
    simp only [SFields.toMisPairs]
    split at h
    · cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (SFields.toMisPairs_mem rest h)

/-- Only `Abs` is above `Abs`. -/
theorem FieldR.abs_left {R : SType → SType → Prop} {f : SType} (h : FieldR R .abs f) :
    f = .abs := by
  cases h with
  | refl => rfl
  | toAbs => rfl
  | preOpt h₀ => exact False.elim h₀
  | pre h₀ => exact False.elim h₀

/-- Only `Missing` is below `Missing`. -/
theorem FieldR.missing_right {R : SType → SType → Prop} {f : SType} (h : FieldR R f .missing) :
    f = .missing := by
  cases h with
  | refl => rfl
  | misMis => rfl
  | pre _ h₁ => exact False.elim h₁

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
  | .var _, _, _ | .prim _, _, _ | .arrow _ _, _, _ | .abs, _, _
  | .missing, _, _ | .opt _, _, _ | .nil, _, _ | .sig _, _, _ => by simp [rowView]

theorem rowView_of_ne_record : ∀ y : SType, (∀ fs t, y ≠ .record fs t) → rowView y = (.nil, y)
  | .record fs t, h => absurd rfl (h fs t)
  | .var _, _ | .prim _, _ | .arrow _ _, _ | .abs, _ | .missing, _ | .opt _, _ | .nil, _
  | .sig _, _ => rfl

theorem rowView_tail_le : ∀ x : SType, sizeOf (rowView x).2 ≤ sizeOf x
  | .record fs t => by
    simp only [rowView]
    have := rowView_tail_le t
    simp only [SType.record.sizeOf_spec]
    omega
  | .var _ | .prim _ | .arrow _ _ | .abs | .missing | .opt _ | .nil | .sig _ => by simp [rowView]

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

/-! ## One layer

The coinduction is up to transitivity (`Sub.coind_trans`): a constraint
justified through an extruded bound (`viaR`) only holds through a chain of
accepted constraints, whose one-layer steps compose by cut elimination. -/

/-- A logged arrow constraint has non-`Abs` components. -/
theorem arrow_comps (hn : LogNAC s) (hl : (SType.arrow l₀ r₀, SType.arrow l₁ r₁) ∈ s.log) :
    l₁ ≠ .abs ∧ r₀ ≠ .abs := ⟨(hn _ hl).2.1, (hn _ hl).1.2.1⟩

/-- A chain of accepted constraints between non-variable types, whose right
sides satisfy `P` (a bound on their tail ranks, for fields). -/
inductive Chain (s : State) (P : SType → Prop) : SType → SType → Prop where
  | one : Logged s a b → (∀ w, a ≠ .var w) → (∀ w, b ≠ .var w) → P b → Chain s P a b
  | cons : Logged s a b → (∀ w, a ≠ .var w) → (∀ w, b ≠ .var w) → b ≠ .abs → P b →
      Chain s P b c → Chain s P a c

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
        | viaVar => exact absurd rfl (hxv _)
        | sigL hb => exact absurd hb id
    · exact nomatch h

/-! ## Generalized variables and interpretations -/

/-- `t` does not mention the variables `A`. -/
def Av (A : List Nat) (t : SType) : Prop := ∀ w ∈ t.vars, w ∉ A

instance (A : List Nat) (t : SType) : Decidable (Av A t) := by
  unfold Av; infer_instance

theorem Av.var {A : List Nat} {v : Nat} : Av A (.var v) ↔ v ∉ A := by simp [Av, SType.vars]

/-! ## Translations under an interpretation -/


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
    ∀ t : SType, Av A t →
      t.toTyI I = t.toTy ∧ t.toRowI I = t.toRow ∧ t.toFieldI I = t.toField
  | .var v, h =>
    ⟨hg.out .ty v (Av.var.1 h), hg.out .row v (Av.var.1 h),
      congrArg Ty.pre (hg.out .ty v (Av.var.1 h))⟩
  | .prim _, _ | .abs, _ | .missing, _ | .nil, _ => ⟨rfl, rfl, rfl⟩
  | .opt τ, h => by
    have hτ := SType.interp_avoid hg τ fun w hw => h w (by simp [SType.vars, hw])
    exact ⟨hτ.1, rfl, congrArg Ty.opt hτ.1⟩
  | .arrow a b, h => by
    have ha := SType.interp_avoid hg a fun w hw => h w (by simp [SType.vars, hw])
    have hb := SType.interp_avoid hg b fun w hw => h w (by simp [SType.vars, hw])
    have e : (SType.arrow a b).toTyI I = (SType.arrow a b).toTy := by
      simp only [SType.toTyI, SType.toTy, ha.1, hb.1]
    exact ⟨e, rfl, congrArg Ty.pre e⟩
  | .record fs t, h => by
    have ht := SType.interp_avoid hg t fun w hw => h w (by simp [SType.vars, hw])
    have hf := SFields.interp_avoid hg fs (fun w hw => h w (by simp [SType.vars, hw])) ht.2.1
    have e : (SType.record fs t).toTyI I = (SType.record fs t).toTy := by
      simp only [SType.toTyI, SType.toTy, hf]
    exact ⟨e, by simp only [SType.toRowI, SType.toRow, hf], congrArg Ty.pre e⟩
  | .sig P, h => by
    have hP := SParams.interp_avoid hg P fun w hw => h w (by simp [SType.vars, hw])
    have e : (SType.sig P).toTyI I = (SType.sig P).toTy := by
      simp only [SType.toTyI, SType.toTy, hP]
    exact ⟨e, by simp only [SType.toRowI, SType.toRow, hP], congrArg Ty.pre e⟩

theorem SFields.interp_avoid (hg : GenHyp s A I) :
    ∀ fs : SFields, (∀ w ∈ fs.vars, w ∉ A) → ∀ {ρ ρ' : Ty .row}, ρ = ρ' →
      fs.toRowOnI I ρ = fs.toRowOn ρ'
  | .nil, _, _, _, h => h
  | .cons n f fs, h, _, _, hρ => by
    rw [SFields.toRowOnI_cons, SFields.toRowOn_cons,
      SFields.interp_avoid hg fs (fun w hw => h w (by simp [SFields.vars, hw])) hρ]
    have hf := SType.interp_avoid hg f fun w hw => h w (by simp [SFields.vars, hw])
    rw [hf.2.2]

theorem SParams.interp_avoid (hg : GenHyp s A I) :
    ∀ P : SParams, (∀ w ∈ P.vars, w ∉ A) → P.toParamsI I = P.toParamsI .gv
  | .nil, _ => rfl
  | .cons _ _ _ τ P, h => by
    have hτ := SType.interp_avoid hg τ fun w hw => h w (by simp [SParams.vars, hw])
    have hP := SParams.interp_avoid hg P fun w hw => h w (by simp [SParams.vars, hw])
    simp only [SParams.toParamsI, hτ.1, hP]
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
  | .var _ | .prim _ | .arrow _ _ | .abs | .missing | .opt _ | .nil | .sig _ => rfl

theorem field_restRowI (I : SInterp) (l : String) (ex : SFields) (t : SType) :
    ((restRow ex t).toRowI I).field l = match ex.lookup l with
      | some f => f.toFieldI I
      | none => (t.toRowI I).field l := by
  cases ex with
  | nil => simp [restRow, SFields.lookup]
  | cons => simp only [restRow]; exact field_recordI ..

end

/-! ## Argument records under an interpretation

The parameters of a logged signature are types (`SParams.NAC`), so each of
its argument records translates to the argument record of its translated
parameters, and the signature to their union. -/

theorem SType.toTyI_list (I : SInterp) : ∀ {τs : List SType}, (∀ τ ∈ τs, τ.IsPre) →
    (SType.list τs).toTyI I = Ty.list (τs.map (·.toTyI I))
  | [], _ => rfl
  | τ :: τs, h => by
    have ih := SType.toTyI_list I (τs := τs) fun σ hσ => h σ (List.mem_cons_of_mem _ hσ)
    simp only [SType.list, SType.toTyI, SType.toRowI, SFields.toRowOnI_cons, Ty.list,
      List.map_cons, SType.toFieldI_of_pre (h τ (List.mem_cons_self ..)),
      SType.toFieldI_of_pre (SType.list_isPre τs), ih]
    rfl

theorem SFields.toRowOnI_ofParams (I : SInterp) : ∀ {ps : List (Param SType)},
    (∀ p ∈ ps, p.ty.IsPre) →
    (SFields.ofParams ps).toRowOnI I .nil = Ty.ofParams (ps.map (Param.map (·.toTyI I)))
  | [], _ => rfl
  | p :: ps, h => by
    have ih := SFields.toRowOnI_ofParams I (ps := ps) fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p (List.mem_cons_self ..)
    simp only [SFields.ofParams, SFields.toRowOnI_cons, Ty.ofParams, List.map_cons, ih]
    congr 1
    cases ho : p.opt
    · simp [Param.field, Param.map, ho, SType.toFieldI_of_pre hp]
    · simp [Param.field, Param.map, ho, SType.toFieldI]

/-- An argument record of a signature, as a row, is the argument row of
the translated parameters. -/
theorem SParams.domain_toRowI (I : SInterp) {P : SParams} (h : P.NAC) (k : Nat) :
    (P.domain k).toRowI I = Ty.argRow (P.toParamsI I) k := by
  have h₁ : ∀ τ ∈ Param.pos k P.toList, τ.IsPre := fun τ hτ => by
    obtain ⟨p, hp, rfl⟩ := Param.mem_pos hτ
    exact (h.mem p hp).1
  have h₂ : ∀ p ∈ Param.named k P.toList, p.ty.IsPre := fun p hp =>
    (h.mem p (Param.mem_named hp)).1
  simp only [SParams.domain, SType.toRowI, SFields.toRowOnI_cons, Ty.argRow,
    SType.toFieldI_of_pre (SType.list_isPre _), SType.toTyI_list I h₁,
    SFields.toRowOnI_ofParams I h₂, SParams.toParamsI_eq, Param.pos_map, Param.named_map]

/-- The rows of a signature are those of its argument records. -/
theorem SParams.sigRows_eq (I : SInterp) {P : SParams} (h : P.NAC) :
    Ty.sigRows (P.toParamsI I) = P.domains.map (·.toRowI I) := by
  have hc : Param.counts (P.toParamsI I) = Param.counts P.toList := by
    rw [SParams.toParamsI_eq, Param.counts_map]
  simp only [Ty.sigRows, SParams.domains, List.map_map, hc]
  exact List.map_congr_left fun k _ => (SParams.domain_toRowI I h k).symm

theorem SParams.domains_nonvar {P : SParams} {d : SType} (hd : d ∈ P.domains) :
    ∀ w, d ≠ .var w := by
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
  exact fun _ h => by simp [SParams.domain] at h

theorem SParams.domains_ne_abs {P : SParams} {d : SType} (hd : d ∈ P.domains) : d ≠ .abs := by
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
  exact fun h => by simp [SParams.domain] at h

theorem SParams.domains_ne_sig {P : SParams} {d : SType} (hd : d ∈ P.domains) :
    ∀ Q, d ≠ .sig Q := by
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
  exact fun _ h => by simp [SParams.domain] at h

theorem SType.IsRecSig.nonvar : ∀ {b : SType}, b.IsRecSig → ∀ w, b ≠ .var w
  | .record _ _, _, _ | .sig _, _, _ => fun h => nomatch h
  | .var _, h, _ | .prim _, h, _ | .arrow _ _, h, _ | .abs, h, _ | .missing, h, _
  | .opt _, h, _ | .nil, h, _ => absurd h id

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

/-- Everything reachable from a variable outside `A` avoids `A`. -/
theorem Clo.avoid (hg : GenHyp s A I) {v : Nat} {u : SType} (hc : Clo s.bounds v u) (hv : v ∉ A) :
    Av A u := by
  induction hc with
  | here hu _ => exact hg.avoid _ hv _ (.inl hu)
  | step hm _ ih => exact ih (Av.var.1 (hg.avoid _ hv _ (.inl hm)))

theorem SType.interp_avoid_ty (hg : GenHyp s A I) {u : SType} (h : Av A u) :
    u.toTyI I = u.toTy := (SType.interp_avoid hg u h).1

theorem SType.interp_avoid_row (hg : GenHyp s A I) {u : SType} (h : Av A u) :
    u.toRowI I = u.toRow := (SType.interp_avoid hg u h).2.1

/-- A variable bound of a variable outside `A` is outside `A`. -/
theorem GenHyp.var_out (hg : GenHyp s A I) {v w : Nat} (hv : v ∉ A)
    (h : SType.var w ∈ (s.bounds v).upper ∨ SType.var w ∈ (s.bounds v).lower) : w ∉ A :=
  Av.var.1 (hg.avoid v hv _ h)

/-- Below an argument record of a signature is below the signature. -/
theorem StG.sigR {P : SParams} (hP : P.NAC) {d : SType} (hd : d ∈ P.domains) {x : Ty .ty}
    (h : StG s I x (.rcd (d.toRowI I))) : StG s I x ((SType.sig P).toTyI I) := by
  show StG s I x (Ty.unions ((Ty.sigRows (P.toParamsI I)).map .rcd))
  rw [SParams.sigRows_eq I hP, List.map_map]
  exact Step.unionsR (List.mem_map.mpr ⟨d, hd, rfl⟩) h

/-- A signature is below what each of its argument records is below. -/
theorem StG.sigL {P : SParams} (hP : P.NAC) {y : Ty .ty}
    (h : ∀ d ∈ P.domains, StG s I (.rcd (d.toRowI I)) y) : StG s I ((SType.sig P).toTyI I) y := by
  show StG s I (Ty.unions ((Ty.sigRows (P.toParamsI I)).map .rcd)) y
  rw [SParams.sigRows_eq I hP, List.map_map]
  exact Step.unionsL fun a ha => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    exact h d hd

/-- The same at a field: a signature as a row is the union of the rows of
its argument records. -/
theorem StG.sigFieldR {P : SParams} (hP : P.NAC) {d : SType} (hd : d ∈ P.domains) {l : String}
    {x : Ty .field} (h : StG s I x ((d.toRowI I).field l)) :
    StG s I x (((SType.sig P).toRowI I).field l) := by
  show StG s I x ((Ty.unions (Ty.sigRows (P.toParamsI I))).field l)
  rw [SParams.sigRows_eq I hP, Ty.field_unions, List.map_map]
  exact Step.unionsR (List.mem_map.mpr ⟨d, hd, rfl⟩) h

theorem StG.sigFieldL {P : SParams} (hP : P.NAC) {l : String} {y : Ty .field}
    (h : ∀ d ∈ P.domains, StG s I ((d.toRowI I).field l) y) :
    StG s I (((SType.sig P).toRowI I).field l) y := by
  show StG s I ((Ty.unions (Ty.sigRows (P.toParamsI I))).field l) y
  rw [SParams.sigRows_eq I hP, Ty.field_unions, List.map_map]
  exact Step.unionsL fun a ha => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    exact h d hd

/-- Between non-variables, one layer, given the case of a signature on the
left (`hsig`), which is the same statement for its argument records. -/
theorem stepNonvarG₀ (hi : Inv s) (hn : LogNAC s) (hl : Logged s a b) (ha : a ≠ .abs)
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w)
    (hsig : ∀ P, a = .sig P → P.NAC → (∀ d ∈ P.domains, Logged s d b) →
      StG s I (a.toTyI I) (b.toTyI I)) : StG s I (a.toTyI I) (b.toTyI I) := by
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => exact absurd rfl ha
    | nilRecord => exact .rcd (.base (SolG.row (a := .nil) (b := .record _ _) (.inr hl)))
    | recordNil => exact .rcd (.base (SolG.row (a := .record _ _) (b := .nil) (.inr hl)))
    | @record fa ta _ _ fb tb =>
      exact .rcd (.base (SolG.row (a := .record fa ta) (b := .record fb tb) (.inr hl)))
    | varL => exact absurd rfl (hav _)
    | varR => exact absurd rfl (hbv _)
    | viaL => exact absurd rfl (hav _)
    | viaR => exact absurd rfl (hbv _)
    | viaVar => exact absurd rfl (hav _)
    | recordSig hd hR => exact StG.sigR (hn _ hl).2 hd (.rcd (.base (SolG.row hR)))
    | sigL _ hR => exact hsig _ rfl (hn _ hl).1 hR

theorem stepNonvarG (hi : Inv s) (hn : LogNAC s) (hl : Logged s a b) (ha : a ≠ .abs)
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w) : StG s I (a.toTyI I) (b.toTyI I) :=
  stepNonvarG₀ hi hn hl ha hav hbv fun P e hP hR => by
    subst e
    refine StG.sigL hP fun d hd => ?_
    have h := stepNonvarG₀ (I := I) hi hn (hR d hd) (SParams.domains_ne_abs hd)
      (SParams.domains_nonvar hd) hbv fun Q e => absurd e (SParams.domains_ne_sig hd Q)
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
    exact h

theorem Chain.stepG (hi : Inv s) (hn : LogNAC s) {P : SType → Prop} :
    Chain s P a u → a ≠ .abs → StG s I (a.toTyI I) (u.toTyI I)
  | .one hl hav hbv _, ha => stepNonvarG hi hn hl ha hav hbv
  | .cons hl hav hbv hba _ c, ha => (stepNonvarG hi hn hl ha hav hbv).comp (c.stepG hi hn hba)

theorem Chain.fieldStepG {P : SType → Prop} {l : String}
    (ih : ∀ x y, Logged s x y → P y → StG s I ((x.toRowI I).field l) ((y.toRowI I).field l)) :
    Chain s P a u → StG s I ((a.toRowI I).field l) ((u.toRowI I).field l)
  | .one hl _ _ hp => ih _ _ hl hp
  | .cons hl _ _ _ hp c => (ih _ _ hl hp).comp (c.fieldStepG ih)

/-- A variable outside `A` below a non-variable, one layer. -/
theorem stepVarNonvarG (hi : Inv s) (hn : LogNAC s) (hg : GenHyp s A I) (hw : w ∉ A)
    (hl : Logged s (.var w) u) (hnv : ∀ x, u ≠ .var x) : StG s I (.gvar w) (u.toTyI I) := by
  rcases hl with h | h
  · exact absurd h.symm (hnv w)
  · cases hi.just.step h with
    | absR => exact .top
    | varL hu =>
      rw [SType.interp_avoid_ty hg (hg.avoid w hw _ (.inl hu))]
      exact .defL (defsOf.clo .ty (.here hu hnv)) (StG.of_sub Sub.refl)
    | viaL hb hbv hba _ hR =>
      have h' := stepNonvarG (I := I) hi hn hR hba hbv hnv
      rw [SType.interp_avoid_ty hg (hg.avoid w hw _ (.inl hb))] at h'
      exact .defL (defsOf.clo .ty (.here hb hbv)) h'
    | varR => exact absurd rfl (hnv _)
    | viaR => exact absurd rfl (hnv _)
    | viaVar => exact absurd rfl (hnv _)

/-- **Variable lower bounds**: a variable lower bound `w` of `m` (outside
`A`) is below every upper bound reachable from `m`, one layer. -/
theorem stepVarLowerG (hi : Inv s) (hn : LogNAC s) (hg : GenHyp s A I) (hc : Clo s.bounds m u)
    (hm : m ∉ A) : ∀ w, SType.var w ∈ (s.bounds m).lower → StG s I (.gvar w) (u.toTyI I) := by
  induction hc with
  | @here n u hu hnv =>
    intro w hw
    rcases hi.cons n (.var w) u hw hu with h | h
    · exact stepVarNonvarG hi hn hg (hg.var_out hm (.inr hw)) h hnv
    · exact nomatch h
  | @step n m' u hm' hc ih =>
    intro w hw
    have hm'A := hg.var_out hm (.inl hm')
    have hu := hc.avoid hg hm'A
    rcases hi.cons n (.var w) (.var m') hw hm' with h | h
    · rcases h with h | h
      · cases h
        rw [SType.interp_avoid_ty hg hu]
        exact .defL (defsOf.clo .ty hc) (StG.of_sub Sub.refl)
      · cases hi.just.step h with
        | varL hu' =>
          rw [SType.interp_avoid_ty hg hu]
          exact .defL (defsOf.clo .ty (.step hu' hc)) (StG.of_sub Sub.refl)
        | varR hl => exact ih hm'A w hl
        | viaL _ _ _ hbv => exact absurd rfl (hbv _)
        | viaR _ _ _ hav => exact absurd rfl (hav _)
        | viaVar hu' hl' =>
          -- `w ≤ m₂` by the definitions, and `m₂` is a lower bound of `m'`
          refine StG.comp (.defR fun τ ⟨u', hc', e⟩ => ?_) (ih hm'A _ hl')
          subst e
          exact .defL (defsOf.clo .ty (.step hu' hc')) (StG.of_sub Sub.refl)
    · exact nomatch h

/-- A variable below one of its upper bounds, one layer. -/
theorem stepUpperG (hg : GenHyp s A I) {v : Nat} {b : SType} (hub : b ∈ (s.bounds v).upper) :
    StG s I (I .ty v) (b.toTyI I) := by
  by_cases hv : v ∈ A
  · exact .of_sub (hg.up v hv _ hub).1
  rw [hg.out .ty v hv]
  match b, hub with
  | .var w, hub =>
    show StG s I _ (I .ty w)
    rw [hg.out .ty w (hg.var_out hv (.inl hub))]
    exact .defR fun τ ⟨u, hc, e⟩ => by
      subst e; exact .defL (defsOf.clo .ty (.step hub hc)) (StG.of_sub Sub.refl)
  | .prim _, hub | .arrow _ _, hub | .record _ _, hub | .abs, hub
  | .missing, hub | .opt _, hub | .nil, hub | .sig _, hub =>
    rw [SType.interp_avoid_ty hg (hg.avoid v hv _ (.inl hub))]
    exact .defL (defsOf.clo .ty (.here hub (fun _ h => nomatch h))) (StG.of_sub Sub.refl)

/-- A lower bound of a variable below the variable, one layer. -/
theorem stepLowerG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    {v : Nat} {a : SType} (hlb : a ∈ (s.bounds v).lower) (ha' : a ≠ .abs) :
    StG s I (a.toTyI I) (I .ty v) := by
  by_cases hv : v ∈ A
  · exact .of_sub ((hg.low v hv _ hlb).1 ha')
  rw [hg.out .ty v hv]
  refine .defR fun τ ⟨u, hc, e⟩ => ?_
  subst e
  show StG s I _ u.toTy
  rw [← SType.interp_avoid_ty hg (hc.avoid hg hv)]
  cases a with
  | var w =>
    show StG s I (I .ty w) _
    rw [hg.out .ty w (hg.var_out hv (.inr hlb))]
    exact stepVarLowerG hi hn hg hc hv w hlb
  | prim _ | arrow _ _ | record _ _ | missing | opt _ | nil | sig _ =>
    exact (lower_chain hi hr hc _ hlb (fun _ h => nomatch h) _ (Nat.le_refl _)).stepG hi hn ha'
  | abs => exact absurd rfl ha'

theorem stepTyG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) : StG s I (a.toTyI I) (b.toTyI I) := by
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow h₁ h₂ =>
      exact .arrow (.base (.ty h₁ (.inl (arrow_comps hn hl).1)))
        (.base (.ty h₂ (.inl (arrow_comps hn hl).2)))
    | absRecord => rcases ha with ha | ha; exact absurd rfl ha; exact nomatch ha
    | nilRecord => exact .rcd (.base (SolG.row (a := .nil) (b := .record _ _) (.inr hl)))
    | recordNil => exact .rcd (.base (SolG.row (a := .record _ _) (b := .nil) (.inr hl)))
    | @record fa ta _ _ fb tb =>
      exact .rcd (.base (SolG.row (a := .record fa ta) (b := .record fb tb) (.inr hl)))
    | varL hub => exact stepUpperG hg hub
    | varR hlb =>
      refine stepLowerG hi hn hr hg hlb ?_
      rcases ha with ha | ha
      · exact ha
      · subst ha; exact fun h => nomatch h
    | viaVar hu hl' =>
      exact (stepUpperG hg hu).comp (stepLowerG hi hn hr hg hl' (fun h => nomatch h))
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
        show StG s I _ u.toTy
        rw [← SType.interp_avoid_ty hg (hc.avoid hg hv)]
        exact h.comp ((lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _)).stepG hi hn h₂)
    | recordSig hd hR => exact StG.sigR (hn _ hl).2 hd (.rcd (.base (SolG.row hR)))
    | sigL hb =>
      exact stepNonvarG hi hn (.inr hl) (fun h => nomatch h) (fun _ h => nomatch h) hb.nonvar

theorem stepFieldRG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    {f₀ f₁ : SType} : FieldR (Logged s) f₀ f₁ → StG s I (f₀.toFieldI I) (f₁.toFieldI I)
  | .refl => .of_sub Sub.refl
  | .toAbs => .top
  | .misMis => .missing
  | .misOpt => .unionR₂ .missing
  | .optOpt h₀ h =>
    .unionL (.unionR₁ (.pre (stepTyG hi hn hr hg h (.inl h₀)))) (.unionR₂ .missing)
  | .preOpt h₀ h => by
    rw [SType.toFieldI_of_pre h₀]
    exact .unionR₁ (.pre (stepTyG hi hn hr hg h (.inl h₀.ne_abs)))
  | .pre h₀ h₁ h => by
    rw [SType.toFieldI_of_pre h₀, SType.toFieldI_of_pre h₁]
    exact .pre (stepTyG hi hn hr hg h (.inl h₀.ne_abs))

/-- The missing field below a field, one layer. -/
theorem stepMisField {f : SType} (h : FieldR (Logged s) .missing f) :
    StG s I .missing (f.toFieldI I) := by
  cases h with
  | refl => exact .missing
  | toAbs => exact .top
  | misMis => exact .missing
  | misOpt => exact .unionR₂ .missing
  | preOpt h₀ => exact False.elim h₀
  | pre h₀ => exact False.elim h₀

/-- From a row variable to one of its non-variable upper bounds, at a field:
through the graph definition outside `A`, through the bound inside. -/
theorem boundField (hg : GenHyp s A I) {ρ : Nat} {x : SType} {l : String}
    {τ : Ty .field} (hu : x ∈ (s.bounds ρ).upper) (hx : ∀ w, x ≠ .var w)
    (h : StG s I ((x.toRowI I).field l) τ) : StG s I (((SType.var ρ).toRowI I).field l) τ := by
  by_cases hρ : ρ ∈ A
  · exact (StG.of_sub ((hg.up ρ hρ x hu).2.fields l)).comp h
  · show StG s I ((I .row ρ).field l) τ
    rw [(SType.interp_avoid hg x (hg.avoid ρ hρ _ (.inl hu))).2.1] at h
    rw [hg.out .row ρ hρ]
    exact .projDefL (defsOf.clo .row (.here hu hx)) h

/-- **Rows below the empty row**: every field is missing. The right side
does not shrink here, so the induction is on the left side: on the rank of
its tail variable (an upper bound of a row variable has a tail of lower
rank), then on its size (the tail of a row is smaller). -/
theorem fieldToNil (hi : Inv s) (hr : TailRanked s rank) (hg : GenHyp s A I) (l : String) :
    ∀ n a, tailRank rank a < n → ∀ m, sizeOf a < m → Logged s a .nil →
      StG s I ((a.toRowI I).field l) .missing := by
  intro n
  induction n with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ihn =>
    intro a ha m
    induction m generalizing a with
    | zero => intro h; exact absurd h (Nat.not_lt_zero _)
    | succ m ihm =>
      intro hm hl
      rcases hl with rfl | hl
      · exact .missing
      · cases hi.just.step hl with
        | @recordNil fa ta fs₀ t₀ e₀ hf ht =>
          rw [toRowI_rowView I (.record fa ta), e₀, field_recordI]
          cases hfl : fs₀.lookup l with
          | some f =>
            have := (hf _ (SFields.toMisPairs_mem fs₀ hfl)).missing_right
            subst this
            exact .missing
          | none =>
            have ht' : t₀ = (rowView (.record fa ta)).2 := by rw [e₀]
            refine ihm t₀ ?_ ?_ ht
            · rw [ht', tailRank_tail]; exact ha
            · rw [ht']; have := rowView_tail_lt fa ta; omega
        | @varL w _ hub =>
          by_cases hw : w ∈ A
          · exact .of_sub ((hg.up w hw _ hub).2.fields l)
          · show StG s I ((I .row w).field l) _
            rw [hg.out .row w hw]
            exact .projDefL (defsOf.clo .row (.here hub (fun _ h => nomatch h))) .missing
        | @viaL w b' _ hb hbv _ _ hR =>
          have hlt := tailRank_var_lt hr (.here hb hbv)
          exact boundField hg hb hbv (ihn b' (by omega) _ (Nat.lt_succ_self _) hR)
        | sigL hb => exact absurd hb id

/-- The field version of `stepVarLowerG`, given field steps for accepted
constraints into right sides of smaller tail rank. -/
theorem fieldVarLowerG (hi : Inv s) (hr : TailRanked s rank) (hg : GenHyp s A I) {l : String}
    {B : Nat} (ih : ∀ x y, Logged s x y → tailRank rank y < B →
      StG s I ((x.toRowI I).field l) ((y.toRowI I).field l))
    (hc : Clo s.bounds m u) (hm : m ∉ A) : ∀ w, SType.var w ∈ (s.bounds m).lower →
      tailRank rank (.var m) ≤ B → StG s I (.proj l (.gvar w)) ((u.toRowI I).field l) := by
  induction hc with
  | @here n u hu hnv =>
    intro w hw hB
    have hwA := hg.var_out hm (.inr hw)
    rcases hi.cons n (.var w) u hw hu with h | h
    · rcases h with h | h
      · exact absurd h.symm (hnv w)
      · cases hi.just.step h with
        | absR => exact .top
        | varL hu' =>
          rw [SType.interp_avoid_row hg (hg.avoid w hwA _ (.inl hu'))]
          exact .projDefL (defsOf.clo .row (.here hu' hnv)) (StG.of_sub Sub.refl)
        | viaL hb hbv _ _ hR =>
          have h' := ih _ _ hR (Nat.lt_of_lt_of_le (tailRank_var_lt hr (.here hu hnv)) hB)
          rw [SType.interp_avoid_row hg (hg.avoid w hwA _ (.inl hb))] at h'
          exact .projDefL (defsOf.clo .row (.here hb hbv)) h'
        | varR => exact absurd rfl (hnv _)
        | viaR => exact absurd rfl (hnv _)
        | viaVar => exact absurd rfl (hnv _)
    · exact nomatch h
  | @step n m' u hm' hc ih' =>
    intro w hw hB
    have hm'A := hg.var_out hm (.inl hm')
    have hu := hc.avoid hg hm'A
    rcases hi.cons n (.var w) (.var m') hw hm' with h | h
    · rcases h with h | h
      · cases h
        rw [SType.interp_avoid_row hg hu]
        exact .projDefL (defsOf.clo .row hc) (StG.of_sub Sub.refl)
      · cases hi.just.step h with
        | varL hu' =>
          rw [SType.interp_avoid_row hg hu]
          exact .projDefL (defsOf.clo .row (.step hu' hc)) (StG.of_sub Sub.refl)
        | varR hl => exact ih' hm'A w hl (Nat.le_trans (tailRank_upVar_le hr hm') hB)
        | viaL _ _ _ hbv => exact absurd rfl (hbv _)
        | viaR _ _ _ hav => exact absurd rfl (hav _)
        | viaVar hu' hl' =>
          refine StG.comp (.projDefR fun τ ⟨u', hc', e⟩ => ?_)
            (ih' hm'A _ hl' (Nat.le_trans (tailRank_upVar_le hr hm') hB))
          subst e
          exact .projDefL (defsOf.clo .row (.step hu' hc')) (StG.of_sub Sub.refl)
    · exact nomatch h

/-- A record below a record, at a field, as the algorithm's record case
goes, given the step from the rest of the left row into the right tail. -/
theorem stepFieldRecordG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    {fa fb fs₀ fs₁ : SFields} {ta tb t₀ t₁ t₀' : SType} (l : String)
    (e₀ : rowView (.record fa ta) = (fs₀, t₀)) (e₁ : rowView (.record fb tb) = (fs₁, t₁))
    (hcom : ∀ l f₀ f₁, fs₀.lookup l = some f₀ → fs₁.lookup l = some f₁ →
      FieldR (Logged s) f₀ f₁)
    (hexp : ExpandG s.bounds (Logged s) t₀ (fs₀.missing fs₁) t₀')
    (hrec : StG s I (((restRow (fs₁.missing fs₀) t₀').toRowI I).field l)
      ((t₁.toRowI I).field l)) :
    StG s I (((SType.record fa ta).toRowI I).field l)
      (((SType.record fb tb).toRowI I).field l) := by
  rw [toRowI_rowView I (.record fa ta), toRowI_rowView I (.record fb tb), e₀, e₁,
    field_recordI, field_recordI]
  dsimp only
  have hrest_field := field_restRowI I l (fs₁.missing fs₀) t₀'
  rw [SFields.missing_lookup] at hrest_field
  have hmiss := SFields.missing_lookup fs₀ l fs₁
  generalize hm : fs₀.missing fs₁ = ms at hexp hmiss
  cases h₁ : fs₁.lookup l with
  | some f₁ =>
    cases h₀ : fs₀.lookup l with
    | some f₀ =>
      dsimp only
      exact stepFieldRG hi hn hr hg (hcom l f₀ f₁ h₀ h₁)
    | none =>
      dsimp only
      simp only [h₀, h₁, Option.isSome, Bool.false_eq_true, ite_false] at hmiss
      cases hexp with
      | none => simp [SFields.lookup] at hmiss
      | abs _ hab =>
        have := (hab _ (SFields.absPairs_mem _ hmiss)).abs_left
        subst this
        exact .top
      | nil _ hmis => exact stepMisField (hmis _ (SFields.misPairs_mem _ hmiss))
      | varAbsent K hab hp =>
        have hk : l ∈ K := by
          by_cases hk : l ∈ K
          · exact hk
          · have := SFields.presentIn_lookup K l ms
            rw [hp, hmiss] at this; simp [hk, SFields.lookup] at this
        have hal : (ms.absentIn K).lookup l = some f₁ := by
          rw [SFields.absentIn_lookup]; simp [hk, hmiss]
        have := (hab _ (SFields.absPairs_mem _ hal)).abs_left
        subst this
        exact .top
      | var K _ hab _ hu hrel =>
        by_cases hk : l ∈ K
        · have hal : (ms.absentIn K).lookup l = some f₁ := by
            rw [SFields.absentIn_lookup]; simp [hk, hmiss]
          have := (hab _ (SFields.absPairs_mem _ hal)).abs_left
          subst this
          exact .top
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
      | nil => rw [← hrest_field]; exact hrec
      | varAbsent => rw [← hrest_field]; exact hrec
      | var K _ _ _ hu hrel =>
        refine boundField hg hu (fun _ h => nomatch h) ?_
        have hp : (ms.presentIn K).lookup l = none := by
          rw [SFields.presentIn_lookup]; simp [hmiss]
        rw [field_recordI, hrel.lookup_none hp]
        dsimp only
        rw [← hrest_field]
        exact hrec

/-- A record below a closed record (an argument record), at a field: the
rest of the left row is below the empty row. -/
theorem stepFieldClosedG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank)
    (hg : GenHyp s A I) {fa fb : SFields} {ta : SType} (l : String)
    (hl : Logged s (.record fa ta) (.record fb .nil)) :
    StG s I (((SType.record fa ta).toRowI I).field l)
      (((SType.record fb .nil).toRowI I).field l) := by
  rcases hl with h | hl
  · rw [h]; exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | @record _ _ fs₀ t₀ _ _ fs₁ t₁ t₀' e₀ e₁ hcom hexp hrest =>
      refine stepFieldRecordG hi hn hr hg l e₀ e₁ hcom hexp ?_
      simp only [rowView, Prod.mk.injEq] at e₁
      obtain ⟨_, rfl⟩ := e₁
      exact fieldToNil hi hr hg l _ _ (Nat.lt_succ_self _) _ (Nat.lt_succ_self _) hrest

/-- Between a non-variable and `b`, at a field, given the case of a
signature on the left (`hsig`), which is the same statement for its
argument records. -/
theorem stepFieldNVG₀ (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      StG s I ((a.toRowI I).field l) ((u.toRowI I).field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → StG s I ((a.toRowI I).field l) ((b'.toRowI I).field l))
    (a : SType) (hav : ∀ w, a ≠ .var w) (l : String) (hl : Logged s a b)
    (hsig : ∀ P, a = .sig P → P.NAC → (∀ d ∈ P.domains, Logged s d b) →
      StG s I ((a.toRowI I).field l) ((b.toRowI I).field l)) :
    StG s I ((a.toRowI I).field l) ((b.toRowI I).field l) := by
  rcases hl with rfl | hl
  · exact .of_sub Sub.refl
  · cases hi.just.step hl with
    | absR => exact .top
    | arrow => exact .top
    | @absRecord t fs hf ht =>
      rw [field_recordI]
      cases hfl : fs.lookup l with
      | some f =>
        have := (hf _ (SFields.absPairs_mem fs hfl)).abs_left
        subst this
        exact .top
      | none =>
        exact ihSize t .abs l (by simp [tailRank, rowView])
          (by simp only [SType.record.sizeOf_spec]; omega) ht
    | @nilRecord t fs hf ht =>
      rw [field_recordI]
      cases hfl : fs.lookup l with
      | some f => exact stepMisField (hf _ (SFields.misPairs_mem fs hfl))
      | none =>
        exact ihSize t .nil l (by simp [tailRank, rowView])
          (by simp only [SType.record.sizeOf_spec]; omega) ht
    | recordNil =>
      exact fieldToNil hi hr hg l _ _ (Nat.lt_succ_self _) _ (Nat.lt_succ_self _) (.inr hl)
    | @record fa ta fs₀ t₀ fb tb fs₁ t₁ t₀' e₀ e₁ hcom hexp hrest =>
      refine stepFieldRecordG hi hn hr hg l e₀ e₁ hcom hexp ?_
      have ht : t₁ = (rowView (.record fb tb)).2 := by rw [e₁]
      refine ihSize t₁ _ l ?_ ?_ hrest
      · rw [ht, tailRank_tail]
      · rw [ht]; exact rowView_tail_lt fb tb
    | varL => exact absurd rfl (hav _)
    | viaL => exact absurd rfl (hav _)
    | viaVar => exact absurd rfl (hav _)
    | @varR v _ hlb =>
      by_cases hv : v ∈ A
      · exact .of_sub ((hg.low v hv _ hlb).2.fields l)
      show StG s I _ ((I .row v).field l)
      rw [hg.out .row v hv]
      refine .projDefR fun τ ⟨u, hc, e⟩ => ?_
      subst e
      show StG s I _ (u.toRow.field l)
      rw [← SType.interp_avoid_row hg (hc.avoid hg hv)]
      exact (lower_chain hi hr hc a hlb hav _ (Nat.le_refl _)).fieldStepG
        fun x y hxy hy => ihRank y x l hy hxy
    | @viaR v a' _ hl' h₁ h₂ _ _ hR =>
      have hlt := tailRank_lower_lt hr hl' h₁
      by_cases hv : v ∈ A
      · exact (ihRank a' a l hlt hR).comp (.of_sub ((hg.low v hv _ hl').2.fields l))
      · show StG s I _ ((I .row v).field l)
        rw [hg.out .row v hv]
        refine .projDefR fun τ ⟨u, hc, e⟩ => ?_
        subst e
        show StG s I _ (u.toRow.field l)
        rw [← SType.interp_avoid_row hg (hc.avoid hg hv)]
        exact (Chain.cons hR hav h₁ h₂ hlt
          (lower_chain hi hr hc _ hl' h₁ _ (Nat.le_refl _))).fieldStepG
            fun x y hxy hy => ihRank y x l hy hxy
    | recordSig hd hR =>
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
      exact StG.sigFieldR (hn _ hl).2 hd (stepFieldClosedG hi hn hr hg l hR)
    | sigL _ hR => exact hsig _ rfl (hn _ hl).1 hR

theorem stepFieldNVG (hi : Inv s) (hn : LogNAC s) (hr : TailRanked s rank) (hg : GenHyp s A I)
    (b : SType)
    (ihRank : ∀ u a l, tailRank rank u < tailRank rank b → Logged s a u →
      StG s I ((a.toRowI I).field l) ((u.toRowI I).field l))
    (ihSize : ∀ b' a l, tailRank rank b' = tailRank rank b → sizeOf b' < sizeOf b →
      Logged s a b' → StG s I ((a.toRowI I).field l) ((b'.toRowI I).field l))
    (a : SType) (hav : ∀ w, a ≠ .var w) (l : String) (hl : Logged s a b) :
    StG s I ((a.toRowI I).field l) ((b.toRowI I).field l) :=
  stepFieldNVG₀ hi hn hr hg b ihRank ihSize a hav l hl fun P e hP hR => by
    subst e
    exact StG.sigFieldL hP fun d hd =>
      stepFieldNVG₀ hi hn hr hg b ihRank ihSize d (SParams.domains_nonvar hd) l (hR d hd)
        fun Q e => absurd e (SParams.domains_ne_sig hd Q)

/-- A row variable below one of its upper bounds, at a field. -/
theorem fieldUpperG (hg : GenHyp s A I) {w : Nat} {b : SType} {l : String}
    (hub : b ∈ (s.bounds w).upper) :
    StG s I ((I .row w).field l) ((b.toRowI I).field l) := by
  by_cases hw : w ∈ A
  · exact .of_sub ((hg.up w hw _ hub).2.fields l)
  rw [hg.out .row w hw]
  match b, hub with
  | .var w', hub =>
    show StG s I _ ((I .row w').field l)
    rw [hg.out .row w' (hg.var_out hw (.inl hub))]
    exact .projDefR fun τ ⟨u, hc, e⟩ => by
      subst e; exact .projDefL (defsOf.clo .row (.step hub hc)) (StG.of_sub Sub.refl)
  | .prim _, hub | .arrow _ _, hub | .record _ _, hub | .abs, hub
  | .missing, hub | .opt _, hub | .nil, hub | .sig _, hub =>
    rw [SType.interp_avoid_row hg (hg.avoid w hw _ (.inl hub))]
    exact .projDefL (defsOf.clo .row (.here hub (fun _ h => nomatch h))) (StG.of_sub Sub.refl)

/-- A variable lower bound of a row variable below it, at a field, given
field steps for accepted constraints into right sides of smaller tail
rank. -/
theorem fieldLowerVarG (hi : Inv s) (hr : TailRanked s rank) (hg : GenHyp s A I) {l : String}
    {v w : Nat}
    (ih : ∀ x y, Logged s x y → tailRank rank y < tailRank rank (.var v) →
      StG s I ((x.toRowI I).field l) ((y.toRowI I).field l))
    (hlb : SType.var w ∈ (s.bounds v).lower) :
    StG s I ((I .row w).field l) ((I .row v).field l) := by
  by_cases hv : v ∈ A
  · exact .of_sub ((hg.low v hv _ hlb).2.fields l)
  rw [hg.out .row w (hg.var_out hv (.inr hlb)), hg.out .row v hv]
  refine .projDefR fun τ ⟨u, hc, e⟩ => ?_
  subst e
  show StG s I _ (u.toRow.field l)
  rw [← SType.interp_avoid_row hg (hc.avoid hg hv)]
  exact fieldVarLowerG hi hr hg ih hc hv w hlb (Nat.le_refl _)

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
  | missing => exact stepFieldNVG hi hn hr hg b ihRank ihSize .missing (fun _ h => nomatch h) l hl
  | opt _ => exact stepFieldNVG hi hn hr hg b ihRank ihSize (.opt _) (fun _ h => nomatch h) l hl
  | nil => exact stepFieldNVG hi hn hr hg b ihRank ihSize .nil (fun _ h => nomatch h) l hl
  | sig _ => exact stepFieldNVG hi hn hr hg b ihRank ihSize (.sig _) (fun _ h => nomatch h) l hl
  | var w =>
    rcases hl with rfl | hl
    · exact .of_sub Sub.refl
    · cases hi.just.step hl with
      | absR => exact .top
      | varL hub => exact fieldUpperG hg hub
      | varR hlb =>
        exact fieldLowerVarG hi hr hg (fun x y hxy hy => ihRank y x l hy hxy) hlb
      | viaL hb hbv _ _ hR =>
        exact boundField hg hb hbv (stepFieldNVG hi hn hr hg b ihRank ihSize _ hbv l hR)
      | viaR _ _ _ hav => exact absurd rfl (hav _)
      | viaVar hu hl' =>
        exact (fieldUpperG hg hu).comp
          (fieldLowerVarG hi hr hg (fun x y hxy hy => ihRank y x l hy hxy) hl')

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


/-! ## The solution theorem -/

/-- Nothing is generalized: the solution's interpretation. -/
theorem GenHyp.nil (s : State) : GenHyp s [] .gv :=
  ⟨fun _ _ _ => rfl, (fun _ _ _ _ _ _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩

/-- **Solution theorem**: every accepted constraint holds of the solution at
the type sort, when its left side is not `Abs`, and at the row sort. -/
theorem solution_ty {s : State} {rank : Nat → Nat} (hi : Inv s) (hn : LogNAC s)
    (hr : TailRanked s rank) (hl : Logged s a b) (ha : a ≠ .abs ∨ a = b) :
    Sub (defsOf s) a.toTy b.toTy := by
  rcases ha with ha | rfl
  · have := (solution_gen hi hn hr (GenHyp.nil s) hl).1 ha
    rwa [SType.toTyI_gv, SType.toTyI_gv] at this
  · exact Sub.refl

theorem solution_row {s : State} {rank : Nat → Nat} (hi : Inv s) (hn : LogNAC s)
    (hr : TailRanked s rank) (hl : Logged s a b) : Sub (defsOf s) a.toRow b.toRow := by
  have := (solution_gen hi hn hr (GenHyp.nil s) hl).2
  rwa [SType.toRowI_gv, SType.toRowI_gv] at this

end BoltCore.Alg
