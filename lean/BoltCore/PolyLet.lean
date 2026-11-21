import BoltCore.Certificate
import BoltCore.Typing

/-!
# Polymorphic `let` in certificates

Typing skeletons with let-polymorphism (`PTyp`): a `let` (or `let rec`)
generalizes a list of variables `gen` of its right-hand side's type, and
each use of the bound name instantiates them with a renaming `ρ`, as
`freshen_above` does. The checker verifies:

* **generalization** (`GenOK`): bounds of variables outside `gen` do not
  mention `gen`, and neither does the context;
* **instantiation** (`InstOK`): `ρ` fixes every variable outside `gen`, and
  the renamed bounds of `gen` are accepted constraints.

The scheme of a generalized `let` (`mkScheme`) has the generalized
variables as free variables at the type and row sorts, and for each bound
of a generalized variable a constraint at the type sort (unless its smaller
side is `Abs`) and one at the row sort. Soundness (`PTyp.sound`) types the
right-hand side at every instance through `solution_gen`, and each use at
an instance given by the copies' solution.

A nested `let` is generalized under the instance of an enclosing one, so
soundness is proved under an interpretation `I` that is itself an instance
(`GenHyp`), and the scheme's variables are numbered above every free
variable the scheme would otherwise contain, so substituting them captures
nothing.
-/

namespace BoltCore

/-- A number above every number of the list. -/
def natBound : List Nat → Nat
  | [] => 0
  | n :: ns => max (n + 1) (natBound ns)

theorem lt_natBound : ∀ {l : List Nat} {n : Nat}, n ∈ l → n < natBound l
  | m :: ms, n, h => by
    simp only [natBound]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := lt_natBound h; omega

/-! ## Free variables -/

/-- The free variables occurring in a type, of any sort. -/
def Ty.fvars : Ty s → List Nat
  | .fvar n => [n]
  | .top | .bot | .gvar _ | .prim _ | .missing | .nil => []
  | .union a b | .inter a b | .arrow a b => a.fvars ++ b.fvars
  | .rcd ρ | .pre ρ | .proj _ ρ => ρ.fvars
  | .cons _ θ ρ => θ.fvars ++ ρ.fvars

/-- Substituting variables that do not occur changes nothing. -/
theorem Ty.substM_fresh {m : Subst} :
    {s : Srt} → (t : Ty s) → (∀ n ∈ t.fvars, ∀ srt, m srt n = none) → t.substM m = t
  | s, .fvar n, h => by simp [Ty.substM, h n (by simp [Ty.fvars]) s]
  | _, .top, _ | _, .bot, _ | _, .prim _, _ | _, .gvar _, _ | _, .missing, _ | _, .nil, _ => rfl
  | _, .union a b, h | _, .inter a b, h | _, .arrow a b, h => by
    simp only [Ty.substM]
    rw [Ty.substM_fresh a fun n hn => h n (by simp [Ty.fvars, hn]),
      Ty.substM_fresh b fun n hn => h n (by simp [Ty.fvars, hn])]
  | _, .rcd ρ, h | _, .pre ρ, h | _, .proj _ ρ, h => by
    simp only [Ty.substM]
    rw [Ty.substM_fresh ρ fun n hn => h n (by simp [Ty.fvars, hn])]
  | _, .cons _ θ ρ, h => by
    simp only [Ty.substM]
    rw [Ty.substM_fresh θ fun n hn => h n (by simp [Ty.fvars, hn]),
      Ty.substM_fresh ρ fun n hn => h n (by simp [Ty.fvars, hn])]

/-! ## Graph variables of signatures -/

theorem Ty.gvars_unions {m : Nat} {s : Srt} : ∀ {l : List (Ty s)}, m ∈ (Ty.unions l).gvars →
    ∃ a ∈ l, m ∈ a.gvars
  | [], h => nomatch h
  | [a], h => ⟨a, List.mem_cons_self .., h⟩
  | a :: b :: l, h => by
    simp only [Ty.unions, Ty.gvars, List.mem_append] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨c, hc, hm⟩ := Ty.gvars_unions h
      exact ⟨c, List.mem_cons_of_mem _ hc, hm⟩

theorem Ty.gvars_list {m : Nat} : ∀ {τs : List (Ty .ty)}, m ∈ (Ty.list τs).gvars →
    ∃ τ ∈ τs, m ∈ τ.gvars
  | [], h => nomatch h
  | τ :: τs, h => by
    simp only [Ty.list, Ty.gvars, List.mem_append, List.append_nil] at h
    rcases h with h | h
    · exact ⟨τ, List.mem_cons_self .., h⟩
    · obtain ⟨σ, hσ, hm⟩ := Ty.gvars_list h
      exact ⟨σ, List.mem_cons_of_mem _ hσ, hm⟩

theorem Ty.gvars_ofParams {m : Nat} : ∀ {ps : List (Param (Ty .ty))},
    m ∈ (Ty.ofParams ps).gvars → ∃ p ∈ ps, m ∈ p.ty.gvars
  | [], h => nomatch h
  | p :: ps, h => by
    simp only [Ty.ofParams, Ty.gvars, List.mem_append] at h
    rcases h with h | h
    · refine ⟨p, List.mem_cons_self .., ?_⟩
      cases ho : p.opt <;> simpa [Param.field, ho, Ty.gvars] using h
    · obtain ⟨q, hq, hm⟩ := Ty.gvars_ofParams h
      exact ⟨q, List.mem_cons_of_mem _ hq, hm⟩

/-- The graph variables of a signature are those of its parameters' types. -/
theorem Ty.gvars_sigRows {m : Nat} {ps : List (Param (Ty .ty))} {ρ : Ty .row}
    (hρ : ρ ∈ Ty.sigRows ps) (h : m ∈ ρ.gvars) : ∃ p ∈ ps, m ∈ p.ty.gvars := by
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hρ
  simp only [Ty.argRow, Ty.gvars, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨τ, hτ, hm⟩ := Ty.gvars_list h
    obtain ⟨p, hp, rfl⟩ := Param.mem_pos hτ
    exact ⟨p, hp, hm⟩
  · obtain ⟨p, hp, hm⟩ := Ty.gvars_ofParams h
    exact ⟨p, Param.mem_named hp, hm⟩

end BoltCore

namespace BoltCore.Alg

open State

/-! ## Schemes of generalized variables -/

section Schemes
variable (σ : Nat → Bounds)

/-- The constraints of the generalized variables: their bounds. -/
def genCs (gen : List Nat) : List (SType × SType) :=
  gen.flatMap fun α =>
    (σ α).upper.map (fun u => (SType.var α, u)) ++ (σ α).lower.map (fun l => (l, SType.var α))

/-- The variables a scheme for `gen` and `st` mentions. -/
def schemeVars (gen : List Nat) (st : SType) : List Nat :=
  st.vars ++ (genCs σ gen).flatMap fun p => p.1.vars ++ p.2.vars

end Schemes

theorem mem_genCs {σ : Nat → Bounds} {gen : List Nat} {q : SType × SType} (h : q ∈ genCs σ gen) :
    ∃ α ∈ gen, (∃ u ∈ (σ α).upper, q = (.var α, u)) ∨ (∃ l ∈ (σ α).lower, q = (l, .var α)) := by
  simp only [genCs, List.mem_flatMap, List.mem_append, List.mem_map] at h
  obtain ⟨α, hα, (⟨u, hu, rfl⟩ | ⟨l, hl, rfl⟩)⟩ := h
  · exact ⟨α, hα, .inl ⟨u, hu, rfl⟩⟩
  · exact ⟨α, hα, .inr ⟨l, hl, rfl⟩⟩

theorem genCs_vars {σ : Nat → Bounds} {gen : List Nat} {st : SType} {q : SType × SType}
    (h : q ∈ genCs σ gen) :
    (∀ v ∈ q.1.vars, v ∈ schemeVars σ gen st) ∧ (∀ v ∈ q.2.vars, v ∈ schemeVars σ gen st) :=
  ⟨fun _ hv => List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, h, List.mem_append_left _ hv⟩),
   fun _ hv => List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, h, List.mem_append_right _ hv⟩)⟩

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

def SType.isAbs : SType → Bool
  | .abs => true
  | _ => false

theorem SType.isAbs_false {t : SType} : t.isAbs = false ↔ t ≠ .abs := by
  cases t <;> simp [SType.isAbs]

def genName (base : Nat) (gen : List Nat) (v : Nat) : Nat := base + gen.idxOf v

theorem genName_inj {gen : List Nat} {base v w : Nat} (hv : v ∈ gen) (hw : w ∈ gen)
    (h : genName base gen v = genName base gen w) : v = w := by
  have h' : gen.idxOf v = gen.idxOf w := by simp only [genName] at h; omega
  have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)
  have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hw)
  simp only [h'] at h1
  rw [← h1, h2]

/-! ## Contexts with schemes -/

/-- The entry does not mention the variables `gen'`. -/
def CEntry.Avoids (σ : Nat → Bounds) (gen' : List Nat) : CEntry → Prop
  | .mono st => Av gen' st
  | .poly gen st => ∀ v ∈ schemeVars σ gen st, v ∉ gen → v ∉ gen'

/-! ## Checking generalization and instantiation -/

/-- `gen` may be generalized: bounds of other variables do not mention it,
and neither does the context. -/
structure GenOK (c : Certificate) (Γ : PCtx) (gen : List Nat) : Prop where
  avoid : ∀ v, v ∉ gen → ∀ b, (b ∈ (c.bounds v).upper ∨ b ∈ (c.bounds v).lower) → Av gen b
  ctx : ∀ p ∈ Γ, p.2.Avoids c.bounds gen

/-! ## Interpretations -/

/-- An interpretation, substituted. -/
def SInterp.substM (I : SInterp) (m : Subst) : SInterp := fun srt v => (I srt v).substM m

mutual
theorem SType.interp_congr {I J : SInterp} :
    ∀ t : SType, (∀ v ∈ t.vars, ∀ srt, I srt v = J srt v) →
      t.toTyI I = t.toTyI J ∧ t.toRowI I = t.toRowI J
  | .var v, h => ⟨h v (by simp [SType.vars]) _, h v (by simp [SType.vars]) _⟩
  | .prim _, _ | .abs, _ | .missing, _ | .nil, _ => ⟨rfl, rfl⟩
  | .opt t, h => ⟨(SType.interp_congr t fun v hv => h v (by simp [SType.vars, hv])).1, rfl⟩
  | .arrow a b, h => by
    have ha := SType.interp_congr a fun v hv => h v (by simp [SType.vars, hv])
    have hb := SType.interp_congr b fun v hv => h v (by simp [SType.vars, hv])
    exact ⟨by simp only [SType.toTyI, ha.1, hb.1], rfl⟩
  | .record fs t, h => by
    have ht := SType.interp_congr t fun v hv => h v (by simp [SType.vars, hv])
    have hf := SFields.interp_congr fs (fun v hv => h v (by simp [SType.vars, hv])) ht.2
    exact ⟨by simp only [SType.toTyI, hf], by simp only [SType.toRowI, hf]⟩
  | .sig P, h => by
    have hP := SParams.interp_congr P fun v hv => h v (by simp [SType.vars, hv])
    exact ⟨by simp only [SType.toTyI, hP], by simp only [SType.toRowI, hP]⟩

theorem SFields.interp_congr {I J : SInterp} :
    ∀ fs : SFields, (∀ v ∈ fs.vars, ∀ srt, I srt v = J srt v) →
      ∀ {ρ ρ' : Ty .row}, ρ = ρ' → fs.toRowOnI I ρ = fs.toRowOnI J ρ'
  | .nil, _, _, _, e => e
  | .cons n f fs, h, _, _, e => by
    rw [SFields.toRowOnI_cons, SFields.toRowOnI_cons,
      SFields.interp_congr fs (fun v hv => h v (by simp [SFields.vars, hv])) e]
    have hf := SType.interp_congr f fun v hv => h v (by simp [SFields.vars, hv])
    have hfld : f.toFieldI I = f.toFieldI J := by
      cases f with
      | abs => rfl
      | missing => rfl
      | opt _ => exact congrArg Ty.opt hf.1
      | _ => exact congrArg Ty.pre hf.1
    rw [hfld]

theorem SParams.interp_congr {I J : SInterp} :
    ∀ P : SParams, (∀ v ∈ P.vars, ∀ srt, I srt v = J srt v) → P.toParamsI I = P.toParamsI J
  | .nil, _ => rfl
  | .cons _ _ _ τ P, h => by
    have hτ := SType.interp_congr τ fun v hv => h v (by simp [SParams.vars, hv])
    have hP := SParams.interp_congr P fun v hv => h v (by simp [SParams.vars, hv])
    simp only [SParams.toParamsI, hτ.1, hP]
end

mutual
theorem SType.interp_substM (I : SInterp) (m : Subst) : ∀ t : SType,
    (t.toTyI I).substM m = t.toTyI (I.substM m) ∧ (t.toRowI I).substM m = t.toRowI (I.substM m)
  | .var _ => ⟨rfl, rfl⟩
  | .prim _ | .abs | .missing | .nil => ⟨rfl, rfl⟩
  | .opt t => ⟨(SType.interp_substM I m t).1, rfl⟩
  | .arrow a b => by
    have ha := SType.interp_substM I m a
    have hb := SType.interp_substM I m b
    exact ⟨by simp only [SType.toTyI, Ty.substM, ha.1, hb.1], rfl⟩
  | .record fs t => by
    have ht := SType.interp_substM I m t
    have hf := SFields.interp_substM I m fs (t.toRowI I)
    exact ⟨by simp only [SType.toTyI, Ty.substM, hf, ht.2],
      by simp only [SType.toRowI, hf, ht.2]⟩
  | .sig P => by
    have hP := SParams.interp_substM I m P
    exact ⟨by simp only [SType.toTyI, Ty.substM_sig, hP],
      by simp only [SType.toRowI, Ty.substM_unions, Ty.substM_sigRows, hP]⟩

theorem SFields.interp_substM (I : SInterp) (m : Subst) : ∀ (fs : SFields) (ρ : Ty .row),
    (fs.toRowOnI I ρ).substM m = fs.toRowOnI (I.substM m) (ρ.substM m)
  | .nil, _ => rfl
  | .cons n f fs, ρ => by
    rw [SFields.toRowOnI_cons, SFields.toRowOnI_cons]
    simp only [Ty.substM, SFields.interp_substM I m fs ρ]
    have hf := SType.interp_substM I m f
    have hfld : (f.toFieldI I).substM m = f.toFieldI (I.substM m) := by
      cases f with
      | abs => rfl
      | missing => rfl
      | opt _ => exact congrArg Ty.opt hf.1
      | _ => exact congrArg Ty.pre hf.1
    rw [hfld]

theorem SParams.interp_substM (I : SInterp) (m : Subst) : ∀ P : SParams,
    (P.toParamsI I).map (Param.map (·.substM m)) = P.toParamsI (I.substM m)
  | .nil => rfl
  | .cons _ _ _ τ P => by
    simp only [SParams.toParamsI, List.map_cons, Param.map, (SType.interp_substM I m τ).1,
      SParams.interp_substM I m P]
end

mutual
theorem SType.rename_interp (ρ : Nat → Nat) (I : SInterp) : ∀ t : SType,
    (t.rename ρ).toTyI I = t.toTyI (fun srt v => I srt (ρ v)) ∧
      (t.rename ρ).toRowI I = t.toRowI (fun srt v => I srt (ρ v))
  | .var _ | .prim _ | .abs | .missing | .nil => ⟨rfl, rfl⟩
  | .opt t => ⟨(SType.rename_interp ρ I t).1, rfl⟩
  | .arrow a b => by
    have ha := SType.rename_interp ρ I a
    have hb := SType.rename_interp ρ I b
    exact ⟨by simp only [SType.rename, SType.toTyI, ha.1, hb.1], rfl⟩
  | .record fs t => by
    have ht := SType.rename_interp ρ I t
    have hf := SFields.rename_interp ρ I fs ht.2
    exact ⟨by simp only [SType.rename, SType.toTyI, hf], by simp only [SType.rename, SType.toRowI, hf]⟩
  | .sig P => by
    have hP := SParams.rename_interp ρ I P
    exact ⟨by simp only [SType.rename, SType.toTyI, hP], by simp only [SType.rename, SType.toRowI, hP]⟩

theorem SFields.rename_interp (ρ : Nat → Nat) (I : SInterp) : ∀ (fs : SFields) {r r' : Ty .row},
    r = r' → (fs.rename ρ).toRowOnI I r = fs.toRowOnI (fun srt v => I srt (ρ v)) r'
  | .nil, _, _, e => e
  | .cons n f fs, _, _, e => by
    simp only [SFields.rename]
    rw [SFields.toRowOnI_cons, SFields.toRowOnI_cons, SFields.rename_interp ρ I fs e]
    have hf := SType.rename_interp ρ I f
    have hfld : (f.rename ρ).toFieldI I = f.toFieldI (fun srt v => I srt (ρ v)) := by
      cases f with
      | abs => rfl
      | missing => rfl
      | opt _ => exact congrArg Ty.opt hf.1
      | _ => exact congrArg Ty.pre hf.1
    rw [hfld]

theorem SParams.rename_interp (ρ : Nat → Nat) (I : SInterp) : ∀ P : SParams,
    (P.rename ρ).toParamsI I = P.toParamsI (fun srt v => I srt (ρ v))
  | .nil => rfl
  | .cons _ _ _ τ P => by
    simp only [SParams.rename, SParams.toParamsI, (SType.rename_interp ρ I τ).1,
      SParams.rename_interp ρ I P]
end

/-! ## Schemes of generalized variables -/

/-- Read the variables `gen` through `G`, the others through `I`. -/
def withGen (gen : List Nat) (G I : SInterp) : SInterp := fun srt v => if v ∈ gen then G srt v else I srt v

/-- The scheme's variables are numbered from here: above every free variable
in what `I` gives the scheme's other variables. -/
def schemeBase (σ : Nat → Bounds) (I : SInterp) (gen : List Nat) (st : SType) : Nat :=
  natBound ((schemeVars σ gen st).flatMap fun v =>
    if v ∈ gen then [] else (I .ty v).fvars ++ (I .row v).fvars ++ (I .field v).fvars)

/-- The interpretation inside the scheme: `gen` as its free variables. -/
def schemeF (σ : Nat → Bounds) (I : SInterp) (gen : List Nat) (st : SType) : SInterp :=
  withGen gen (fun _ v => .fvar (genName (schemeBase σ I gen st) gen v)) I

/-- The constraints a bound gives: at the type sort, unless the smaller side
is `Abs`, and at the row sort. -/
def boundCs (F : SInterp) (p : SType × SType) : List Cstr :=
  (if p.1.isAbs then [] else [⟨p.1.toTyI F, p.2.toTyI F⟩]) ++ [⟨p.1.toRowI F, p.2.toRowI F⟩]

/-- The constrained scheme generalizing `gen` in `st`, under `I`. -/
def mkScheme (σ : Nat → Bounds) (I : SInterp) (gen : List Nat) (st : SType) : Scheme where
  vars := gen.map (genName (schemeBase σ I gen st) gen)
  cs := (genCs σ gen).flatMap (boundCs (schemeF σ I gen st))
  body := st.toTyI (schemeF σ I gen st)

section
variable {σ : Nat → Bounds} {I : SInterp} {gen : List Nat} {st : SType}

theorem schemeBase_lt {v n : Nat} (hv : v ∈ schemeVars σ gen st) (hg : v ∉ gen) {srt : Srt}
    (hn : n ∈ (I srt v).fvars) : n < schemeBase σ I gen st := by
  apply lt_natBound
  refine List.mem_flatMap.mpr ⟨v, hv, ?_⟩
  simp only [hg, ite_false, List.mem_append]
  cases srt
  · exact .inl (.inl hn)
  · exact .inl (.inr hn)
  · exact .inr hn

/-- Substituting the scheme's variables only touches them. -/
theorem scheme_substM {m : Subst}
    (hm : ∀ n, n < schemeBase σ I gen st → ∀ srt, m srt n = none)
    {t : SType} (ht : ∀ v ∈ t.vars, v ∈ schemeVars σ gen st) :
    (t.toTyI (schemeF σ I gen st)).substM m =
        t.toTyI (withGen gen (fun _ v => (Ty.fvar (genName (schemeBase σ I gen st) gen v)).substM m) I) ∧
      (t.toRowI (schemeF σ I gen st)).substM m =
        t.toRowI (withGen gen (fun _ v => (Ty.fvar (genName (schemeBase σ I gen st) gen v)).substM m) I) := by
  have hs := SType.interp_substM (schemeF σ I gen st) m t
  have hc := SType.interp_congr (I := (schemeF σ I gen st).substM m)
    (J := withGen gen (fun srt v => (Ty.fvar (genName (schemeBase σ I gen st) gen v)).substM m) I) t
    (fun v hv srt => by
      simp only [SInterp.substM, schemeF, withGen]
      split
      · rfl
      · next hg => exact Ty.substM_fresh _ fun n hn => hm n (schemeBase_lt (ht v hv) hg hn))
  exact ⟨hs.1.trans hc.1, hs.2.trans hc.2⟩

/-- The substitution that instantiates the scheme's variables with `G`. -/
def genSubst (σ : Nat → Bounds) (I : SInterp) (gen : List Nat) (st : SType) (G : SInterp) :
    Subst :=
  fun srt n => (gen.find? fun v => genName (schemeBase σ I gen st) gen v == n).map (G srt)

theorem genSubst_name {G : SInterp} {v : Nat} (hv : v ∈ gen) (srt : Srt) :
    genSubst σ I gen st G srt (genName (schemeBase σ I gen st) gen v) = some (G srt v) := by
  simp only [genSubst]
  cases h : gen.find? fun w => genName (schemeBase σ I gen st) gen w ==
      genName (schemeBase σ I gen st) gen v with
  | none =>
    have := List.find?_eq_none.mp h v hv
    simp at this
  | some w =>
    have hw := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [beq_iff_eq] at hp
    rw [genName_inj hw hv hp]; rfl

theorem genSubst_low {G : SInterp} {n : Nat} (hn : n < schemeBase σ I gen st) (srt : Srt) :
    genSubst σ I gen st G srt n = none := by
  simp only [genSubst]
  have : gen.find? (fun w => genName (schemeBase σ I gen st) gen w == n) = none :=
    List.find?_eq_none.mpr fun w _ h => by
      simp only [beq_iff_eq, genName] at h; omega
  rw [this]; rfl

theorem genSubst_dom {G : SInterp} {srt : Srt} {n : Nat} (h : (genSubst σ I gen st G srt n).isSome) :
    n ∈ (mkScheme σ I gen st).vars := by
  simp only [genSubst] at h
  obtain ⟨w, hw, hp⟩ := List.find?_isSome.mp (by rwa [Option.isSome_map] at h)
  simp only [beq_iff_eq] at hp
  exact List.mem_map.mpr ⟨w, hw, hp⟩

/-- The bounds of `gen` hold, read through `W`, at both sorts. -/
def BoundsHold (E : Defs) (σ : Nat → Bounds) (gen : List Nat) (W : SInterp) : Prop :=
  ∀ q ∈ genCs σ gen, (q.1 ≠ .abs → Sub E (q.1.toTyI W) (q.2.toTyI W)) ∧
    Sub E (q.1.toRowI W) (q.2.toRowI W)

/-- An instance of the scheme: read `gen` through `G`, given that the bounds
of `gen` hold so. -/
theorem mkScheme_instance {E : Defs} {G : SInterp}
    (hcs : BoundsHold E σ gen (withGen gen G I)) :
    (mkScheme σ I gen st).Instance E (st.toTyI (withGen gen G I)) := by
  have key : ∀ t : SType, (∀ v ∈ t.vars, v ∈ schemeVars σ gen st) →
      (t.toTyI (schemeF σ I gen st)).substM (genSubst σ I gen st G) = t.toTyI (withGen gen G I) ∧
      (t.toRowI (schemeF σ I gen st)).substM (genSubst σ I gen st G) = t.toRowI (withGen gen G I) := by
    intro t ht
    have h := scheme_substM (m := genSubst σ I gen st G) (fun n hn srt => genSubst_low hn srt) ht
    have hc := SType.interp_congr (I := withGen gen
        (fun srt v => (Ty.fvar (genName (schemeBase σ I gen st) gen v)).substM (genSubst σ I gen st G)) I)
      (J := withGen gen G I) t (fun v _ srt => by
        simp only [withGen]
        split
        · next hg => simp only [Ty.substM, genSubst_name hg]; rfl
        · rfl)
    exact ⟨h.1.trans hc.1, h.2.trans hc.2⟩
  refine ⟨genSubst σ I gen st G, fun _ _ h => genSubst_dom h, fun c hc => ?_, ?_⟩
  · obtain ⟨q, hq, hc⟩ := List.mem_flatMap.mp hc
    have hv := genCs_vars (st := st) hq
    simp only [boundCs, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · split at hc
      · exact nomatch hc
      · next hab =>
        simp only [List.mem_singleton] at hc; subst hc
        simp only [SatAfter]
        rw [(key q.1 hv.1).1, (key q.2 hv.2).1]
        exact (hcs q hq).1 (SType.isAbs_false.mp (by simpa using hab))
    · simp only [SatAfter]
      rw [(key q.1 hv.1).2, (key q.2 hv.2).2]
      exact (hcs q hq).2
  · show st.toTyI _ = (st.toTyI (schemeF σ I gen st)).substM _
    exact ((key st fun v hv => List.mem_append_left _ hv).1).symm

/-- Conversely, every instance reads `gen` through some `G` under which the
bounds hold. -/
theorem mkScheme_instance_inv {E : Defs} {τ : Ty .ty}
    (h : (mkScheme σ I gen st).Instance E τ) :
    ∃ G : SInterp, τ = st.toTyI (withGen gen G I) ∧ BoundsHold E σ gen (withGen gen G I) := by
  obtain ⟨m, hdom, hcs, rfl⟩ := h
  have hm : ∀ n, n < schemeBase σ I gen st → ∀ srt, m srt n = none := fun n hn srt => by
    cases hmn : m srt n with
    | none => rfl
    | some _ =>
      have := hdom srt n (by simp [hmn])
      simp only [mkScheme, List.mem_map, genName] at this
      obtain ⟨_, _, rfl⟩ := this
      omega
  refine ⟨fun srt v => (Ty.fvar (genName (schemeBase σ I gen st) gen v)).substM m,
    (scheme_substM hm fun v hv => List.mem_append_left _ hv).1, fun q hq => ?_⟩
  have hv := genCs_vars (st := st) hq
  have hk := scheme_substM (st := st) hm hv.1
  have hk' := scheme_substM (st := st) hm hv.2
  refine ⟨fun hab => ?_, ?_⟩
  · have := hcs ⟨q.1.toTyI (schemeF σ I gen st), q.2.toTyI (schemeF σ I gen st)⟩
      (List.mem_flatMap.mpr ⟨q, hq, by
        simp [boundCs, SType.isAbs_false.mpr hab]⟩)
    simp only [SatAfter] at this
    rwa [hk.1, hk'.1] at this
  · have := hcs ⟨q.1.toRowI (schemeF σ I gen st), q.2.toRowI (schemeF σ I gen st)⟩
      (List.mem_flatMap.mpr ⟨q, hq, by simp [boundCs]⟩)
    simp only [SatAfter] at this
    rwa [hk.2, hk'.2] at this

/-- The scheme only depends on what `I` gives the variables it mentions. -/
theorem mkScheme_congr {J : SInterp} (h : ∀ v ∈ schemeVars σ gen st, v ∉ gen → ∀ srt, I srt v = J srt v) :
    mkScheme σ I gen st = mkScheme σ J gen st := by
  have hb : schemeBase σ I gen st = schemeBase σ J gen st := by
    simp only [schemeBase]
    congr 1
    apply flatMap_congr'
    intro v hv
    split
    · rfl
    · next hg => rw [h v hv hg .ty, h v hv hg .row, h v hv hg .field]
  have hF : ∀ v ∈ schemeVars σ gen st, ∀ srt, schemeF σ I gen st srt v = schemeF σ J gen st srt v := by
    intro v hv srt
    simp only [schemeF, withGen, hb]
    split
    · rfl
    · next hg => exact h v hv hg srt
  simp only [mkScheme, hb]
  congr 1
  · apply flatMap_congr'
    intro p hp
    have hv := genCs_vars (st := st) hp
    have h₁ := SType.interp_congr p.1 fun v h' => hF v (hv.1 v h')
    have h₂ := SType.interp_congr p.2 fun v h' => hF v (hv.2 v h')
    simp only [boundCs, h₁.1, h₁.2, h₂.1, h₂.2]
  · exact (SType.interp_congr st fun v h' => hF v (List.mem_append_left _ h')).1

end

/-! ## Contexts with schemes -/

def CEntry.toScheme (σ : Nat → Bounds) (I : SInterp) : CEntry → Scheme
  | .mono st => .mono (st.toTyI I)
  | .poly gen st => mkScheme σ I gen st

def PCtx.toCtx (σ : Nat → Bounds) (I : SInterp) (Γ : PCtx) : Ctx :=
  Γ.map fun p => (p.1, p.2.toScheme σ I)

theorem PCtx.lookup_toCtx {σ : Nat → Bounds} {I : SInterp} {Γ : PCtx} {x : String} {e : CEntry}
    (h : Γ.lookup x = some e) : (Γ.toCtx σ I).lookup x = some (e.toScheme σ I) := by
  simp only [PCtx.lookup] at h
  simp only [Ctx.lookup, PCtx.toCtx]
  rw [lookup_map (fun e : CEntry => e.toScheme σ I), h]; rfl

theorem CEntry.toScheme_withGen {σ : Nat → Bounds} {I G : SInterp} {gen' : List Nat} {e : CEntry}
    (h : e.Avoids σ gen') : e.toScheme σ (withGen gen' G I) = e.toScheme σ I := by
  cases e with
  | mono st =>
    simp only [CEntry.toScheme]
    exact congrArg Scheme.mono (SType.interp_congr st fun v hv srt => by
      simp [withGen, h v hv]).1
  | poly gen st =>
    simp only [CEntry.toScheme]
    exact mkScheme_congr fun v hv hg srt => by simp [withGen, h v hv hg]

theorem PCtx.toCtx_withGen {σ : Nat → Bounds} {I G : SInterp} {gen' : List Nat} {Γ : PCtx}
    (h : ∀ p ∈ Γ, p.2.Avoids σ gen') : Γ.toCtx σ (withGen gen' G I) = Γ.toCtx σ I := by
  simp only [PCtx.toCtx]
  apply List.map_congr_left
  intro p hp
  rw [CEntry.toScheme_withGen (h p hp)]

/-! ## Instantiation and skeletons -/

/-- A use instantiates `gen` by the renaming `ρ` (the copies `freshen_above`
made): `ρ` fixes every other variable, and the copies' renamed bounds are
accepted. -/
structure InstOK (c : Certificate) (gen : List Nat) (ρ : Nat → Nat) : Prop where
  fix : ∀ v, v ∉ gen → ρ v = v
  up : ∀ α ∈ gen, ∀ u ∈ (c.bounds α).upper, c.Accepts (.var (ρ α)) (u.rename ρ)
  low : ∀ α ∈ gen, ∀ l ∈ (c.bounds α).lower, c.Accepts (l.rename ρ) (.var (ρ α))

mutual
/-- Typing skeletons with let-polymorphism. -/
inductive PTyp (c : Certificate) : PCtx → Term → SType → Prop where
  | lit : PTyp c Γ (.lit n) (.prim "int")
  | var : Γ.lookup x = some (.mono st) → PTyp c Γ (.var x) st
  | inst : Γ.lookup x = some (.poly gen st) → InstOK c gen ρ → PTyp c Γ (.var x) (st.rename ρ)
  | lam : PTyp c ((x, .mono st₁) :: Γ) t st₂ → PTyp c Γ (.lam x t) (.arrow st₁ st₂)
  | app : PTyp c Γ f stf → PTyp c Γ a sta → stf ≠ .abs →
      c.Accepts stf (.arrow sta st) → PTyp c Γ (.app f a) st
  /-- A record literal is closed. -/
  | rcd : PFields c Γ fs F → PTyp c Γ (.rcd fs) (.record F .nil)
  /-- Selection: the selected field is present (its type is a type). -/
  | sel : PTyp c Γ t st₀ → st₀ ≠ .abs →
      c.Accepts st₀ (.record (.cons l st .nil) .abs) → st.IsPre → PTyp c Γ (.sel t l) st
  /-- Selection with a default: the field is optional, and the default has
  its type. -/
  | selOr : PTyp c Γ t st₀ → st₀ ≠ .abs →
      c.Accepts st₀ (.record (.cons l (.opt st) .nil) .abs) →
      PTyp c Γ d std → std ≠ .abs → c.Accepts std st → PTyp c Γ (.selOr t l d) st
  | ext : PTyp c Γ t st₀ → PFields c Γ fs F → st₀ ≠ .abs →
      c.Accepts st₀ (.record F.absOf ρ) → PTyp c Γ (.ext t fs) (.record F ρ)
  | extNil : PTyp c Γ t st → PTyp c Γ (.ext t []) st
  | letIn : PTyp c Γ r str → GenOK c Γ gen → PTyp c ((x, .poly gen str) :: Γ) b st →
      PTyp c Γ (.letIn false x r b) st
  | letRec : r.IsFun → PTyp c ((x, .mono stx) :: Γ) r inf → inf ≠ .abs → c.Accepts inf stx →
      GenOK c Γ gen → PTyp c ((x, .poly gen stx) :: Γ) b st → PTyp c Γ (.letIn true x r b) st
  /-- A conditional: the condition is accepted below `bool`, and each
  branch below the result. -/
  | ite : PTyp c Γ cnd stc → stc ≠ .abs → c.Accepts stc (.prim "bool") →
      PTyp c Γ a sta → sta ≠ .abs → c.Accepts sta st →
      PTyp c Γ b stb → stb ≠ .abs → c.Accepts stb st → PTyp c Γ (.ite cnd a b) st
  /-- A function of a parameter list: its domain is the signature. -/
  | fn : Param.WF P.toList → PParams c Γ ps P Γ' → PTyp c Γ' t st →
      PTyp c Γ (.fn ps t) (.arrow (.sig P) st)

/-- Fields of a record literal; they are present (their types are types). -/
inductive PFields (c : Certificate) : PCtx → List (String × Term) → SFields → Prop where
  | nil : PFields c Γ [] .nil
  | cons : PTyp c Γ t st → st.IsPre → PFields c Γ fs F →
      PFields c Γ ((l, t) :: fs) (.cons l st F)

/-- The parameters of a `fn`, with their types and the context of the body;
the type of a default is accepted below its parameter's. -/
inductive PParams (c : Certificate) :
    PCtx → List (String × PKind × Option Term) → SParams → PCtx → Prop where
  | nil : PParams c Γ [] .nil Γ
  | req : PParams c ((x, .mono st) :: Γ) ps P Γ' →
      PParams c Γ ((x, k, none) :: ps) (.cons x k false st P) Γ'
  | dflt : PTyp c Γ d std → std ≠ .abs → c.Accepts std st →
      PParams c ((x, .mono st) :: Γ) ps P Γ' →
      PParams c Γ ((x, k, some d) :: ps) (.cons x k true st P) Γ'
end

theorem PFields.pres {c : Certificate} : PFields c Γ fs F → F.Pres
  | .nil => trivial
  | .cons _ h hF => ⟨h, hF.pres⟩

/-! ## Soundness -/

section
variable {c : Certificate}

theorem Certificate.Valid.holdsG (hv : c.Valid) {A : List Nat} {I : SInterp}
    (hg : GenHyp c.state A I) (h : c.Accepts a b) :
    (a ≠ .abs → Sub (defsOf c.state) (a.toTyI I) (b.toTyI I)) ∧
      Sub (defsOf c.state) (a.toRowI I) (b.toRowI I) :=
  solution_gen hv.inv hv.nac hv.final.ranked hg h

theorem GenHyp.extend {A gen : List Nat} {I G : SInterp} (hg : GenHyp c.state A I)
    (hok : GenOK c Γ gen) (hcs : BoundsHold (defsOf c.state) c.bounds gen (withGen gen G I)) :
    GenHyp c.state (A ++ gen) (withGen gen G I) := by
  have same : ∀ v, v ∉ gen → ∀ b, (b ∈ (c.bounds v).upper ∨ b ∈ (c.bounds v).lower) →
      b.toTyI (withGen gen G I) = b.toTyI I ∧ b.toRowI (withGen gen G I) = b.toRowI I :=
    fun v hv b hb => SType.interp_congr b fun w hw srt => by simp [withGen, hok.avoid v hv b hb w hw]
  refine ⟨fun srt v hv => ?_, fun v hv b hb w hw => ?_, fun α hα u hu => ?_, fun α hα l hl => ?_⟩
  · simp only [List.mem_append, not_or] at hv
    simp only [withGen, hv.2, ite_false]
    exact hg.out srt v hv.1
  · simp only [List.mem_append, not_or] at hv ⊢
    exact ⟨hg.avoid v hv.1 b hb w hw, hok.avoid v hv.2 b hb w hw⟩
  · by_cases hαg : α ∈ gen
    · have := hcs (.var α, u) (List.mem_flatMap.mpr ⟨α, hαg, List.mem_append_left _
        (List.mem_map.mpr ⟨u, hu, rfl⟩)⟩)
      exact ⟨this.1 (fun h => nomatch h), this.2⟩
    · have hαA : α ∈ A := by
        simp only [List.mem_append] at hα; exact hα.resolve_right hαg
      have hs := same α hαg u (.inl hu)
      simp only [withGen, hαg, ite_false]
      rw [hs.1, hs.2]
      exact hg.up α hαA u hu
  · by_cases hαg : α ∈ gen
    · exact hcs (l, .var α) (List.mem_flatMap.mpr ⟨α, hαg, List.mem_append_right _
        (List.mem_map.mpr ⟨l, hl, rfl⟩)⟩)
    · have hαA : α ∈ A := by
        simp only [List.mem_append] at hα; exact hα.resolve_right hαg
      have hs := same α hαg l (.inr hl)
      simp only [withGen, hαg, ite_false]
      rw [hs.1, hs.2]
      exact hg.low α hαA l hl

/-- The bounds of `gen` hold of the solution itself: the scheme has an
instance. -/
theorem bounds_hold (hv : c.Valid) {A : List Nat} {I : SInterp} (hg : GenHyp c.state A I)
    {gen : List Nat} : BoundsHold (defsOf c.state) c.bounds gen (withGen gen I I) := by
  intro q hq
  have hI : withGen gen I I = I := funext fun srt => funext fun v => by simp [withGen]
  rw [hI]
  obtain ⟨α, _, ⟨u, hu, rfl⟩ | ⟨l, hl, rfl⟩⟩ := mem_genCs hq
  · exact hv.holdsG hg (.inr (hv.inLog.1 α u hu))
  · exact hv.holdsG hg (.inr (hv.inLog.2 α l hl))

mutual
/-- **Soundness of polymorphic skeletons**: under an instance `I` of
the variables generalized so far, a skeleton checked against a valid
certificate gives a declarative typing. -/
theorem PTyp.sound (hv : c.Valid) {A : List Nat} {I : SInterp} (hg : GenHyp c.state A I) :
    PTyp c Γ t st → Typ (defsOf c.state) (Γ.toCtx c.bounds I) t (st.toTyI I)
  | .lit => .lit
  | .var hx => Typ.var_mono (PCtx.lookup_toCtx hx)
  | .inst (gen := gen) (st := st) (ρ := ρ) hx hok => by
    have hK : withGen gen (fun srt v => I srt (ρ v)) I = fun srt v => I srt (ρ v) :=
      funext fun srt => funext fun v => by
        simp only [withGen]; split
        · rfl
        · next hg' => rw [hok.fix v hg']
    have hinst := mkScheme_instance (σ := c.bounds) (I := I) (st := st) (gen := gen)
      (E := defsOf c.state) (G := fun srt v => I srt (ρ v)) (by
        intro q hq
        rw [hK, (SType.rename_interp ρ I q.1).1.symm, (SType.rename_interp ρ I q.2).1.symm,
          (SType.rename_interp ρ I q.1).2.symm, (SType.rename_interp ρ I q.2).2.symm]
        obtain ⟨α, hα, ⟨u, hu, rfl⟩ | ⟨l, hl, rfl⟩⟩ := mem_genCs hq
        · have := hv.holdsG hg (hok.up α hα u hu)
          exact ⟨fun _ => this.1 (fun h => nomatch h), this.2⟩
        · have := hv.holdsG hg (hok.low α hα l hl)
          exact ⟨fun h => this.1 (SType.rename_ne_abs h), this.2⟩)
    rw [hK, ← (SType.rename_interp ρ I st).1] at hinst
    exact .var (PCtx.lookup_toCtx hx) hinst
  | .lam h => .lam (h.sound hv hg)
  | .app h₁ h₂ ha hc => .app (.sub (h₁.sound hv hg) ((hv.holdsG hg hc).1 ha)) (h₂.sound hv hg)
  | .rcd (F := F) h => by
    have e : (SType.record F .nil).toTyI I = Ty.record (F.toListI I) := by
      simp only [SType.toTyI, SType.toRowI, Ty.record]
      exact congrArg Ty.rcd (SFields.toRowOnI_pres h.pres)
    rw [e]
    exact .rcd (h.sound hv hg)
  | .sel (l := l) (st := st) h ha hc hst => by
    have hs := (hv.holdsG hg hc).1 ha
    have e : (SType.record (.cons l st .nil) .abs).toTyI I = .rcd (.cons l (.pre (st.toTyI I)) .top) := by
      simp only [SType.toTyI, SType.toRowI, SFields.toRowOnI_cons, SType.toFieldI_of_pre hst]; rfl
    rw [e] at hs
    exact .sel (.sub (h.sound hv hg) hs)
  | .selOr (l := l) (st := st) h ha hc hd hda hcd => by
    have hs := (hv.holdsG hg hc).1 ha
    have e : (SType.record (.cons l (.opt st) .nil) .abs).toTyI I =
        .rcd (.cons l (Ty.opt (st.toTyI I)) .top) := rfl
    rw [e] at hs
    exact .selOr (.sub (h.sound hv hg) hs) (.sub (hd.sound hv hg) ((hv.holdsG hg hcd).1 hda))
  | .ext (F := F) (ρ := ρ) h₁ h₂ ha hc => by
    have hs := (hv.holdsG hg hc).1 ha
    simp only [SType.toTyI, SFields.toRowOnI_absOf] at hs
    have e : (SType.record F ρ).toTyI I = .rcd (Ty.ofFields (F.toListI I) (ρ.toRowI I)) := by
      simp only [SType.toTyI]
      exact congrArg Ty.rcd (SFields.toRowOnI_pres h₂.pres)
    rw [e]
    exact .ext (.sub (h₁.sound hv hg) hs) (h₂.sound hv hg)
  | .extNil h => .extNil (h.sound hv hg)
  | .letIn (gen := gen) (str := str) h₁ hok h₂ => by
    refine .letIn (σ := mkScheme c.bounds I gen str) (fun τ' hτ => ?_)
      (mkScheme_instance (bounds_hold hv hg)) (h₂.sound hv hg)
    obtain ⟨G, rfl, hcs⟩ := mkScheme_instance_inv hτ
    have ih := h₁.sound hv (hg.extend hok hcs)
    rwa [PCtx.toCtx_withGen hok.ctx] at ih
  | .letRec (x := x) (gen := gen) (stx := stx) hf h₁ ha hc hok h₂ => by
    refine .letRec hf (σ := mkScheme c.bounds I gen stx) (fun τ' hτ => ?_)
      (mkScheme_instance (bounds_hold hv hg)) (h₂.sound hv hg)
    obtain ⟨G, rfl, hcs⟩ := mkScheme_instance_inv hτ
    have hg' := hg.extend hok hcs
    have ih : Typ (defsOf c.state)
        ((x, Scheme.mono (stx.toTyI (withGen gen G I))) ::
          Γ.toCtx c.bounds (withGen gen G I)) _ _ :=
      h₁.sound hv hg'
    rw [PCtx.toCtx_withGen hok.ctx] at ih
    exact .sub ih ((hv.holdsG hg' hc).1 ha)
  | .ite hc hca hcc ha haa hac hb hba hbc =>
    .ite (.sub (hc.sound hv hg) ((hv.holdsG hg hcc).1 hca))
      (.sub (ha.sound hv hg) ((hv.holdsG hg hac).1 haa))
      (.sub (hb.sound hv hg) ((hv.holdsG hg hbc).1 hba))
  | .fn (P := P) hw hp h => by
    have hw' : Param.WF (P.toParamsI I) := by rw [SParams.toParamsI_eq]; exact hw.map _
    exact .fn hw' (hp.sound hv hg) (h.sound hv hg)

theorem PFields.sound (hv : c.Valid) {A : List Nat} {I : SInterp} (hg : GenHyp c.state A I) :
    PFields c Γ fs F → TypFields (defsOf c.state) (Γ.toCtx c.bounds I) fs (F.toListI I)
  | .nil => .nil
  | .cons h₁ _ h₂ => .cons (h₁.sound hv hg) (h₂.sound hv hg)

theorem PParams.sound (hv : c.Valid) {A : List Nat} {I : SInterp} (hg : GenHyp c.state A I) :
    PParams c Γ ps P Γ' →
      TypParams (defsOf c.state) (Γ.toCtx c.bounds I) ps (P.toParamsI I) (Γ'.toCtx c.bounds I)
  | .nil => .nil
  | .req h => .req (h.sound hv hg)
  | .dflt hd ha hc h =>
    .dflt (.sub (hd.sound hv hg) ((hv.holdsG hg hc).1 ha)) (h.sound hv hg)
end

/-- **Theorem 1 with let-polymorphism, for certificates**: a polymorphic
skeleton checked against a valid certificate gives a declarative typing
with constrained schemes. -/
theorem PTyp.sound_top (hv : c.Valid) (h : PTyp c Γ t st) :
    Typ (defsOf c.state) (Γ.toCtx c.bounds .gv) t st.toTy := by
  have := h.sound hv (GenHyp.nil c.state)
  rwa [SType.toTyI_gv] at this

/-! ## No recursive types in the solution -/

mutual
theorem SType.toTy_gvars : ∀ a : SType, (∀ m ∈ a.toTy.gvars, m ∈ a.vars) ∧ (∀ m ∈ a.toRow.gvars, m ∈ a.vars)
  | .var _ => ⟨fun m h => by simpa [SType.toTy, SType.toTyI, SInterp.gv, Ty.gvars, SType.vars] using h,
      fun m h => by simpa [SType.toRow, SType.toRowI, SInterp.gv, Ty.gvars, SType.vars] using h⟩
  | .prim _ | .abs | .missing | .nil => ⟨fun _ h => by simp [SType.toTy, SType.toTyI, Ty.gvars] at h,
      fun _ h => by simp [SType.toRow, SType.toRowI, Ty.gvars] at h⟩
  | .opt t => ⟨fun m h => (SType.toTy_gvars t).1 m h,
      fun _ h => by simp [SType.toRow, SType.toRowI, Ty.gvars] at h⟩
  | .arrow a b => ⟨fun m h => by
      simp only [SType.toTy, SType.toTyI, Ty.gvars, List.mem_append] at h
      simp only [SType.vars, List.mem_append]
      exact h.imp ((SType.toTy_gvars a).1 m) ((SType.toTy_gvars b).1 m),
      fun _ h => by simp [SType.toRow, SType.toRowI, Ty.gvars] at h⟩
  | .record fs t =>
    have hf := SFields.toRowOn_gvars fs t.toRow
    have ht := (SType.toTy_gvars t).2
    have h : ∀ m ∈ (fs.toRowOn t.toRow).gvars, m ∈ (SType.record fs t).vars := fun m hm => by
      simp only [SType.vars, List.mem_append]
      rcases hf m hm with h | h
      · exact .inl h
      · exact .inr (ht m h)
    ⟨fun m hm => h m (by simpa [SType.toTy, SType.toTyI, SInterp.gv, Ty.gvars] using hm), h⟩
  | .sig P =>
    have hP := SParams.toParams_gvars P
    ⟨fun m hm => by
        obtain ⟨a, ha, hma⟩ := Ty.gvars_unions hm
        obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp ha
        obtain ⟨p, hp, hmp⟩ := Ty.gvars_sigRows hρ hma
        exact hP p hp m hmp,
      fun m hm => by
        obtain ⟨ρ, hρ, hmρ⟩ := Ty.gvars_unions hm
        obtain ⟨p, hp, hmp⟩ := Ty.gvars_sigRows hρ hmρ
        exact hP p hp m hmp⟩

theorem SFields.toRowOn_gvars : ∀ (fs : SFields) (ρ : Ty .row), ∀ m ∈ (fs.toRowOn ρ).gvars,
    m ∈ fs.vars ∨ m ∈ ρ.gvars
  | .nil, _, _, h => .inr h
  | .cons n f fs, ρ, m, h => by
    rw [SFields.toRowOn_cons] at h
    simp only [Ty.gvars, List.mem_append] at h
    simp only [SFields.vars, List.mem_append]
    rcases h with h | h
    · refine .inl (.inl ?_)
      cases f with
      | abs => simp [SType.toField, SType.toFieldI, Ty.gvars] at h
      | missing => simp [SType.toField, SType.toFieldI, Ty.gvars] at h
      | opt τ =>
        have h' : m ∈ τ.toTy.gvars := by
          simpa [SType.toField, SType.toFieldI, Ty.gvars] using h
        exact (SType.toTy_gvars (.opt τ)).1 m h'
      | _ => exact (SType.toTy_gvars _).1 m (by simpa [SType.toField, SType.toFieldI, Ty.gvars] using h)
    · rcases SFields.toRowOn_gvars fs ρ m h with h | h
      · exact .inl (.inr h)
      · exact .inr h

theorem SParams.toParams_gvars : ∀ P : SParams, ∀ p ∈ P.toParamsI .gv, ∀ m ∈ p.ty.gvars,
    m ∈ P.vars
  | .nil, _, h, _, _ => nomatch h
  | .cons _ _ _ τ P, p, hp, m, hm => by
    simp only [SParams.toParamsI, List.mem_cons] at hp
    simp only [SParams.vars, List.mem_append]
    rcases hp with rfl | hp
    · exact .inl ((SType.toTy_gvars τ).1 m hm)
    · exact .inr (SParams.toParams_gvars P p hp m hm)
end

theorem SType.toAt_gvars (a : SType) : ∀ srt : Srt, ∀ m ∈ (a.toAt srt).gvars, m ∈ a.vars
  | .ty => (SType.toTy_gvars a).1
  | .row => (SType.toTy_gvars a).2
  | .field => fun m h => by
    cases a with
    | abs => simp [SType.toAt, SType.toField, SType.toFieldI, Ty.gvars] at h
    | missing => simp [SType.toAt, SType.toField, SType.toFieldI, Ty.gvars] at h
    | opt τ =>
      have h' : m ∈ τ.toTy.gvars := by
        simpa [SType.toAt, SType.toField, SType.toFieldI, Ty.gvars] using h
      exact (SType.toTy_gvars (.opt τ)).1 m h'
    | _ => exact (SType.toTy_gvars _).1 m (by simpa [SType.toAt, SType.toField, SType.toFieldI, Ty.gvars] using h)

/-- **No recursive types**: the solution of a valid certificate defines
each graph variable only in terms of graph variables of lower rank. -/
theorem Certificate.Valid.nonrec (hv : c.Valid) : Defs.Ranked (defsOf c.state) c.rank := by
  rintro srt n _ ⟨u, hc, rfl⟩ m hm
  exact hc.ranked hv.acyclic m (SType.toAt_gvars u srt m hm)

end

end BoltCore.Alg
