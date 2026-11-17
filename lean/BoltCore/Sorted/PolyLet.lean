import BoltCore.Sorted.SolutionGen
import BoltCore.Sorted.Typing
import BoltCore.Sorted.Theorem1
import BoltCore.PolyLet

/-!
# Polymorphic `let` in certificates, sorted (step 3)

`PolyLet.lean` over the sorted core. The scheme of a generalized `let`
(`smkScheme`) has the generalized variables as free variables at the type
and row sorts, and for each bound of a generalized variable a constraint at
the type sort (unless its smaller side is `Abs`) and one at the row sort.
There are no `α ≤ ⊤` constraints, and instantiation does not need copies
to keep kinds (`SInstOK`).

The skeleton `SPTyp` is `PTyp` with two changes: a selection asks that the
selected field's type is not `Abs` instead of `Present`, and a record
literal's fields are not `Abs` (so their translations are present fields).
`GenOK`, `CEntry`, `PCtx` and the certificate's validity are reused.
-/

namespace BoltCore.Sorted

/-! ## Free variables -/

/-- The free variables occurring in a type, of any sort. -/
def Ty.fvars : Ty s → List Nat
  | .fvar n => [n]
  | .top | .bot | .gvar _ | .prim _ => []
  | .union a b | .inter a b | .arrow a b => a.fvars ++ b.fvars
  | .rcd ρ | .pre ρ | .proj _ ρ => ρ.fvars
  | .cons _ θ ρ => θ.fvars ++ ρ.fvars

/-- Substituting variables that do not occur changes nothing. -/
theorem Ty.substM_fresh {m : Subst} :
    {s : Srt} → (t : Ty s) → (∀ n ∈ t.fvars, ∀ srt, m srt n = none) → t.substM m = t
  | s, .fvar n, h => by simp [Ty.substM, h n (by simp [Ty.fvars]) s]
  | _, .top, _ | _, .bot, _ | _, .prim _, _ | _, .gvar _, _ => rfl
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

end BoltCore.Sorted

namespace BoltCore.Alg

open State
open BoltCore.Sorted (Srt)

/-! ## Interpretations -/

/-- An interpretation, substituted. -/
def SInterp.substM (I : SInterp) (m : Sorted.Subst) : SInterp := fun srt v => (I srt v).substM m

mutual
theorem SType.sI_congr {I J : SInterp} :
    ∀ t : SType, (∀ v ∈ t.vars, ∀ srt, I srt v = J srt v) →
      t.sTyI I = t.sTyI J ∧ t.sRowI I = t.sRowI J
  | .var v, h => ⟨h v (by simp [SType.vars]) _, h v (by simp [SType.vars]) _⟩
  | .prim _, _ | .abs, _ => ⟨rfl, rfl⟩
  | .arrow a b, h => by
    have ha := SType.sI_congr a fun v hv => h v (by simp [SType.vars, hv])
    have hb := SType.sI_congr b fun v hv => h v (by simp [SType.vars, hv])
    exact ⟨by simp only [SType.sTyI, ha.1, hb.1], rfl⟩
  | .record fs t, h => by
    have ht := SType.sI_congr t fun v hv => h v (by simp [SType.vars, hv])
    have hf := SFields.sI_congr fs (fun v hv => h v (by simp [SType.vars, hv])) ht.2
    exact ⟨by simp only [SType.sTyI, hf], by simp only [SType.sRowI, hf]⟩

theorem SFields.sI_congr {I J : SInterp} :
    ∀ fs : SFields, (∀ v ∈ fs.vars, ∀ srt, I srt v = J srt v) →
      ∀ {ρ ρ' : Sorted.Ty .row}, ρ = ρ' → fs.sRowOnI I ρ = fs.sRowOnI J ρ'
  | .nil, _, _, _, e => e
  | .cons n f fs, h, _, _, e => by
    rw [SFields.sRowOnI_cons, SFields.sRowOnI_cons,
      SFields.sI_congr fs (fun v hv => h v (by simp [SFields.vars, hv])) e]
    have hf := SType.sI_congr f fun v hv => h v (by simp [SFields.vars, hv])
    cases f with
    | abs => rfl
    | _ => simp only [SType.sFieldI, hf.1]
end

mutual
theorem SType.sI_substM (I : SInterp) (m : Sorted.Subst) : ∀ t : SType,
    (t.sTyI I).substM m = t.sTyI (I.substM m) ∧ (t.sRowI I).substM m = t.sRowI (I.substM m)
  | .var _ => ⟨rfl, rfl⟩
  | .prim _ | .abs => ⟨rfl, rfl⟩
  | .arrow a b => by
    have ha := SType.sI_substM I m a
    have hb := SType.sI_substM I m b
    exact ⟨by simp only [SType.sTyI, Sorted.Ty.substM, ha.1, hb.1], rfl⟩
  | .record fs t => by
    have ht := SType.sI_substM I m t
    have hf := SFields.sI_substM I m fs (t.sRowI I)
    exact ⟨by simp only [SType.sTyI, Sorted.Ty.substM, hf, ht.2],
      by simp only [SType.sRowI, hf, ht.2]⟩

theorem SFields.sI_substM (I : SInterp) (m : Sorted.Subst) : ∀ (fs : SFields) (ρ : Sorted.Ty .row),
    (fs.sRowOnI I ρ).substM m = fs.sRowOnI (I.substM m) (ρ.substM m)
  | .nil, _ => rfl
  | .cons n f fs, ρ => by
    rw [SFields.sRowOnI_cons, SFields.sRowOnI_cons]
    simp only [Sorted.Ty.substM, SFields.sI_substM I m fs ρ]
    have hf := SType.sI_substM I m f
    cases f with
    | abs => rfl
    | _ => simp only [SType.sFieldI, Sorted.Ty.substM, hf.1]
end

mutual
theorem SType.rename_sI (ρ : Nat → Nat) (I : SInterp) : ∀ t : SType,
    (t.rename ρ).sTyI I = t.sTyI (fun srt v => I srt (ρ v)) ∧
      (t.rename ρ).sRowI I = t.sRowI (fun srt v => I srt (ρ v))
  | .var _ | .prim _ | .abs => ⟨rfl, rfl⟩
  | .arrow a b => by
    have ha := SType.rename_sI ρ I a
    have hb := SType.rename_sI ρ I b
    exact ⟨by simp only [SType.rename, SType.sTyI, ha.1, hb.1], rfl⟩
  | .record fs t => by
    have ht := SType.rename_sI ρ I t
    have hf := SFields.rename_sI ρ I fs ht.2
    exact ⟨by simp only [SType.rename, SType.sTyI, hf], by simp only [SType.rename, SType.sRowI, hf]⟩

theorem SFields.rename_sI (ρ : Nat → Nat) (I : SInterp) : ∀ (fs : SFields) {r r' : Sorted.Ty .row},
    r = r' → (fs.rename ρ).sRowOnI I r = fs.sRowOnI (fun srt v => I srt (ρ v)) r'
  | .nil, _, _, e => e
  | .cons n f fs, _, _, e => by
    simp only [SFields.rename]
    rw [SFields.sRowOnI_cons, SFields.sRowOnI_cons, SFields.rename_sI ρ I fs e]
    have hf := SType.rename_sI ρ I f
    have hfld : (f.rename ρ).sFieldI I = f.sFieldI (fun srt v => I srt (ρ v)) := by
      cases f with
      | abs => rfl
      | _ => exact congrArg Sorted.Ty.pre hf.1
    rw [hfld]
end

/-! ## Schemes of generalized variables -/

/-- Read the variables `gen` through `G`, the others through `I`. -/
def swithGen (gen : List Nat) (G I : SInterp) : SInterp := fun srt v => if v ∈ gen then G srt v else I srt v

/-- The scheme's variables are numbered from here: above every free variable
in what `I` gives the scheme's other variables. -/
def sschemeBase (σ : Nat → Bounds) (I : SInterp) (gen : List Nat) (st : SType) : Nat :=
  natBound ((schemeVars σ gen st).flatMap fun v =>
    if v ∈ gen then [] else (I .ty v).fvars ++ (I .row v).fvars ++ (I .field v).fvars)

/-- The interpretation inside the scheme: `gen` as its free variables. -/
def sschemeF (σ : Nat → Bounds) (I : SInterp) (gen : List Nat) (st : SType) : SInterp :=
  swithGen gen (fun _ v => .fvar (genName (sschemeBase σ I gen st) gen v)) I

/-- The constraints a bound gives: at the type sort, unless the smaller side
is `Abs`, and at the row sort. -/
def boundCs (F : SInterp) (p : SType × SType) : List Sorted.Cstr :=
  (if p.1.isAbs then [] else [⟨p.1.sTyI F, p.2.sTyI F⟩]) ++ [⟨p.1.sRowI F, p.2.sRowI F⟩]

/-- The constrained scheme generalizing `gen` in `st`, under `I`. -/
def smkScheme (σ : Nat → Bounds) (I : SInterp) (gen : List Nat) (st : SType) : Sorted.Scheme where
  vars := gen.map (genName (sschemeBase σ I gen st) gen)
  cs := (genCs σ gen).flatMap (boundCs (sschemeF σ I gen st))
  body := st.sTyI (sschemeF σ I gen st)

section
variable {σ : Nat → Bounds} {I : SInterp} {gen : List Nat} {st : SType}

theorem sschemeBase_lt {v n : Nat} (hv : v ∈ schemeVars σ gen st) (hg : v ∉ gen) {srt : Srt}
    (hn : n ∈ (I srt v).fvars) : n < sschemeBase σ I gen st := by
  apply lt_natBound
  refine List.mem_flatMap.mpr ⟨v, hv, ?_⟩
  simp only [hg, ite_false, List.mem_append]
  cases srt
  · exact .inl (.inl hn)
  · exact .inl (.inr hn)
  · exact .inr hn

/-- Substituting the scheme's variables only touches them. -/
theorem sscheme_substM {m : Sorted.Subst}
    (hm : ∀ n, n < sschemeBase σ I gen st → ∀ srt, m srt n = none)
    {t : SType} (ht : ∀ v ∈ t.vars, v ∈ schemeVars σ gen st) :
    (t.sTyI (sschemeF σ I gen st)).substM m =
        t.sTyI (swithGen gen (fun _ v => (Sorted.Ty.fvar (genName (sschemeBase σ I gen st) gen v)).substM m) I) ∧
      (t.sRowI (sschemeF σ I gen st)).substM m =
        t.sRowI (swithGen gen (fun _ v => (Sorted.Ty.fvar (genName (sschemeBase σ I gen st) gen v)).substM m) I) := by
  have hs := SType.sI_substM (sschemeF σ I gen st) m t
  have hc := SType.sI_congr (I := (sschemeF σ I gen st).substM m)
    (J := swithGen gen (fun srt v => (Sorted.Ty.fvar (genName (sschemeBase σ I gen st) gen v)).substM m) I) t
    (fun v hv srt => by
      simp only [SInterp.substM, sschemeF, swithGen]
      split
      · rfl
      · next hg => exact Sorted.Ty.substM_fresh _ fun n hn => hm n (sschemeBase_lt (ht v hv) hg hn))
  exact ⟨hs.1.trans hc.1, hs.2.trans hc.2⟩

/-- The substitution that instantiates the scheme's variables with `G`. -/
def sgenSubst (σ : Nat → Bounds) (I : SInterp) (gen : List Nat) (st : SType) (G : SInterp) :
    Sorted.Subst :=
  fun srt n => (gen.find? fun v => genName (sschemeBase σ I gen st) gen v == n).map (G srt)

theorem sgenSubst_name {G : SInterp} {v : Nat} (hv : v ∈ gen) (srt : Srt) :
    sgenSubst σ I gen st G srt (genName (sschemeBase σ I gen st) gen v) = some (G srt v) := by
  simp only [sgenSubst]
  cases h : gen.find? fun w => genName (sschemeBase σ I gen st) gen w ==
      genName (sschemeBase σ I gen st) gen v with
  | none =>
    have := List.find?_eq_none.mp h v hv
    simp at this
  | some w =>
    have hw := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [beq_iff_eq] at hp
    rw [genName_inj hw hv hp]; rfl

theorem sgenSubst_low {G : SInterp} {n : Nat} (hn : n < sschemeBase σ I gen st) (srt : Srt) :
    sgenSubst σ I gen st G srt n = none := by
  simp only [sgenSubst]
  have : gen.find? (fun w => genName (sschemeBase σ I gen st) gen w == n) = none :=
    List.find?_eq_none.mpr fun w _ h => by
      simp only [beq_iff_eq, genName] at h; omega
  rw [this]; rfl

theorem sgenSubst_dom {G : SInterp} {srt : Srt} {n : Nat} (h : (sgenSubst σ I gen st G srt n).isSome) :
    n ∈ (smkScheme σ I gen st).vars := by
  simp only [sgenSubst] at h
  obtain ⟨w, hw, hp⟩ := List.find?_isSome.mp (by rwa [Option.isSome_map] at h)
  simp only [beq_iff_eq] at hp
  exact List.mem_map.mpr ⟨w, hw, hp⟩

/-- The bounds of `gen` hold, read through `W`, at both sorts. -/
def BoundsHold (E : Sorted.Defs) (σ : Nat → Bounds) (gen : List Nat) (W : SInterp) : Prop :=
  ∀ q ∈ genCs σ gen, (q.1 ≠ .abs → Sorted.Sub E (q.1.sTyI W) (q.2.sTyI W)) ∧
    Sorted.Sub E (q.1.sRowI W) (q.2.sRowI W)

/-- An instance of the scheme: read `gen` through `G`, given that the bounds
of `gen` hold so. -/
theorem smkScheme_instance {E : Sorted.Defs} {G : SInterp}
    (hcs : BoundsHold E σ gen (swithGen gen G I)) :
    (smkScheme σ I gen st).Instance E (st.sTyI (swithGen gen G I)) := by
  have key : ∀ t : SType, (∀ v ∈ t.vars, v ∈ schemeVars σ gen st) →
      (t.sTyI (sschemeF σ I gen st)).substM (sgenSubst σ I gen st G) = t.sTyI (swithGen gen G I) ∧
      (t.sRowI (sschemeF σ I gen st)).substM (sgenSubst σ I gen st G) = t.sRowI (swithGen gen G I) := by
    intro t ht
    have h := sscheme_substM (m := sgenSubst σ I gen st G) (fun n hn srt => sgenSubst_low hn srt) ht
    have hc := SType.sI_congr (I := swithGen gen
        (fun srt v => (Sorted.Ty.fvar (genName (sschemeBase σ I gen st) gen v)).substM (sgenSubst σ I gen st G)) I)
      (J := swithGen gen G I) t (fun v _ srt => by
        simp only [swithGen]
        split
        · next hg => simp only [Sorted.Ty.substM, sgenSubst_name hg]; rfl
        · rfl)
    exact ⟨h.1.trans hc.1, h.2.trans hc.2⟩
  refine ⟨sgenSubst σ I gen st G, fun _ _ h => sgenSubst_dom h, fun c hc => ?_, ?_⟩
  · obtain ⟨q, hq, hc⟩ := List.mem_flatMap.mp hc
    have hv := genCs_vars (st := st) hq
    simp only [boundCs, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · split at hc
      · exact nomatch hc
      · next hab =>
        simp only [List.mem_singleton] at hc; subst hc
        simp only [Sorted.SatAfter]
        rw [(key q.1 hv.1).1, (key q.2 hv.2).1]
        exact (hcs q hq).1 (SType.isAbs_false.mp (by simpa using hab))
    · simp only [Sorted.SatAfter]
      rw [(key q.1 hv.1).2, (key q.2 hv.2).2]
      exact (hcs q hq).2
  · show st.sTyI _ = (st.sTyI (sschemeF σ I gen st)).substM _
    exact ((key st fun v hv => List.mem_append_left _ hv).1).symm

/-- Conversely, every instance reads `gen` through some `G` under which the
bounds hold. -/
theorem smkScheme_instance_inv {E : Sorted.Defs} {τ : Sorted.Ty .ty}
    (h : (smkScheme σ I gen st).Instance E τ) :
    ∃ G : SInterp, τ = st.sTyI (swithGen gen G I) ∧ BoundsHold E σ gen (swithGen gen G I) := by
  obtain ⟨m, hdom, hcs, rfl⟩ := h
  have hm : ∀ n, n < sschemeBase σ I gen st → ∀ srt, m srt n = none := fun n hn srt => by
    cases hmn : m srt n with
    | none => rfl
    | some _ =>
      have := hdom srt n (by simp [hmn])
      simp only [smkScheme, List.mem_map, genName] at this
      obtain ⟨_, _, rfl⟩ := this
      omega
  refine ⟨fun srt v => (Sorted.Ty.fvar (genName (sschemeBase σ I gen st) gen v)).substM m,
    (sscheme_substM hm fun v hv => List.mem_append_left _ hv).1, fun q hq => ?_⟩
  have hv := genCs_vars (st := st) hq
  have hk := sscheme_substM (st := st) hm hv.1
  have hk' := sscheme_substM (st := st) hm hv.2
  refine ⟨fun hab => ?_, ?_⟩
  · have := hcs ⟨q.1.sTyI (sschemeF σ I gen st), q.2.sTyI (sschemeF σ I gen st)⟩
      (List.mem_flatMap.mpr ⟨q, hq, by
        simp [boundCs, SType.isAbs_false.mpr hab]⟩)
    simp only [Sorted.SatAfter] at this
    rwa [hk.1, hk'.1] at this
  · have := hcs ⟨q.1.sRowI (sschemeF σ I gen st), q.2.sRowI (sschemeF σ I gen st)⟩
      (List.mem_flatMap.mpr ⟨q, hq, by simp [boundCs]⟩)
    simp only [Sorted.SatAfter] at this
    rwa [hk.2, hk'.2] at this

/-- The scheme only depends on what `I` gives the variables it mentions. -/
theorem smkScheme_congr {J : SInterp} (h : ∀ v ∈ schemeVars σ gen st, v ∉ gen → ∀ srt, I srt v = J srt v) :
    smkScheme σ I gen st = smkScheme σ J gen st := by
  have hb : sschemeBase σ I gen st = sschemeBase σ J gen st := by
    simp only [sschemeBase]
    congr 1
    apply flatMap_congr'
    intro v hv
    split
    · rfl
    · next hg => rw [h v hv hg .ty, h v hv hg .row, h v hv hg .field]
  have hF : ∀ v ∈ schemeVars σ gen st, ∀ srt, sschemeF σ I gen st srt v = sschemeF σ J gen st srt v := by
    intro v hv srt
    simp only [sschemeF, swithGen, hb]
    split
    · rfl
    · next hg => exact h v hv hg srt
  simp only [smkScheme, hb]
  congr 1
  · apply flatMap_congr'
    intro p hp
    have hv := genCs_vars (st := st) hp
    have h₁ := SType.sI_congr p.1 fun v h' => hF v (hv.1 v h')
    have h₂ := SType.sI_congr p.2 fun v h' => hF v (hv.2 v h')
    simp only [boundCs, h₁.1, h₁.2, h₂.1, h₂.2]
  · exact (SType.sI_congr st fun v h' => hF v (List.mem_append_left _ h')).1

end

/-! ## Contexts with schemes -/

def CEntry.toSScheme (σ : Nat → Bounds) (I : SInterp) : CEntry → Sorted.Scheme
  | .mono st => .mono (st.sTyI I)
  | .poly gen st => smkScheme σ I gen st

def PCtx.toSCtx (σ : Nat → Bounds) (I : SInterp) (Γ : PCtx) : Sorted.Ctx :=
  Γ.map fun p => (p.1, p.2.toSScheme σ I)

theorem PCtx.lookup_toSCtx {σ : Nat → Bounds} {I : SInterp} {Γ : PCtx} {x : String} {e : CEntry}
    (h : Γ.lookup x = some e) : (Γ.toSCtx σ I).lookup x = some (e.toSScheme σ I) := by
  induction Γ with
  | nil => simp [PCtx.lookup] at h
  | cons p Γ ih =>
    simp only [PCtx.lookup, List.find?_cons] at h
    simp only [PCtx.toSCtx, List.map_cons, Sorted.Ctx.lookup, List.find?_cons]
    by_cases hp : p.1 = x
    · simp only [hp, decide_true] at h ⊢
      simp at h
      subst h
      rfl
    · simp only [hp, decide_false] at h ⊢
      have := ih h
      simpa [PCtx.toSCtx, Sorted.Ctx.lookup] using this

theorem CEntry.toSScheme_withGen {σ : Nat → Bounds} {I G : SInterp} {gen' : List Nat} {e : CEntry}
    (h : e.Avoids σ gen') : e.toSScheme σ (swithGen gen' G I) = e.toSScheme σ I := by
  cases e with
  | mono st =>
    simp only [CEntry.toSScheme]
    exact congrArg Sorted.Scheme.mono (SType.sI_congr st fun v hv srt => by
      simp [swithGen, h v hv]).1
  | poly gen st =>
    simp only [CEntry.toSScheme]
    exact smkScheme_congr fun v hv hg srt => by simp [swithGen, h v hv hg]

theorem PCtx.toSCtx_withGen {σ : Nat → Bounds} {I G : SInterp} {gen' : List Nat} {Γ : PCtx}
    (h : ∀ p ∈ Γ, p.2.Avoids σ gen') : Γ.toSCtx σ (swithGen gen' G I) = Γ.toSCtx σ I := by
  simp only [PCtx.toSCtx]
  apply List.map_congr_left
  intro p hp
  rw [CEntry.toSScheme_withGen (h p hp)]

/-! ## Instantiation and skeletons -/

/-- A use instantiates `gen` by the renaming `ρ`: `ρ` fixes every other
variable, and the copies' renamed bounds are accepted. -/
structure SInstOK (c : Certificate) (gen : List Nat) (ρ : Nat → Nat) : Prop where
  fix : ∀ v, v ∉ gen → ρ v = v
  up : ∀ α ∈ gen, ∀ u ∈ (c.bounds α).upper, c.Accepts (.var (ρ α)) (u.rename ρ)
  low : ∀ α ∈ gen, ∀ l ∈ (c.bounds α).lower, c.Accepts (l.rename ρ) (.var (ρ α))

mutual
/-- Typing skeletons with let-polymorphism, for the sorted system. -/
inductive SPTyp (c : Certificate) : PCtx → Term → SType → Prop where
  | lit : SPTyp c Γ (.lit n) (.prim "int")
  | var : Γ.lookup x = some (.mono st) → SPTyp c Γ (.var x) st
  | inst : Γ.lookup x = some (.poly gen st) → SInstOK c gen ρ → SPTyp c Γ (.var x) (st.rename ρ)
  | lam : SPTyp c ((x, .mono st₁) :: Γ) t st₂ → SPTyp c Γ (.lam x t) (.arrow st₁ st₂)
  | app : SPTyp c Γ f stf → SPTyp c Γ a sta → stf ≠ .abs →
      c.Accepts stf (.arrow sta st) → SPTyp c Γ (.app f a) st
  | rcd : SPFields c Γ fs F → SPTyp c Γ (.rcd fs) (.record F .abs)
  /-- Selection: the selected field's type is not `Abs`. -/
  | sel : SPTyp c Γ t st₀ → st₀ ≠ .abs →
      c.Accepts st₀ (.record (.cons l st .nil) .abs) → st ≠ .abs → SPTyp c Γ (.sel t l) st
  | ext : SPTyp c Γ t st₀ → SPFields c Γ fs F → st₀ ≠ .abs →
      c.Accepts st₀ (.record F.absOf ρ) → SPTyp c Γ (.ext t fs) (.record F ρ)
  | extNil : SPTyp c Γ t st → SPTyp c Γ (.ext t []) st
  | letIn : SPTyp c Γ r str → GenOK c Γ gen → SPTyp c ((x, .poly gen str) :: Γ) b st →
      SPTyp c Γ (.letIn false x r b) st
  | letRec : r.IsFun → SPTyp c ((x, .mono stx) :: Γ) r inf → inf ≠ .abs → c.Accepts inf stx →
      GenOK c Γ gen → SPTyp c ((x, .poly gen stx) :: Γ) b st → SPTyp c Γ (.letIn true x r b) st

/-- Fields of a record literal; their types are not `Abs`. -/
inductive SPFields (c : Certificate) : PCtx → List (String × Term) → SFields → Prop where
  | nil : SPFields c Γ [] .nil
  | cons : SPTyp c Γ t st → st ≠ .abs → SPFields c Γ fs F →
      SPFields c Γ ((l, t) :: fs) (.cons l st F)
end

theorem SPFields.pres {c : Certificate} : SPFields c Γ fs F → F.Pres
  | .nil => trivial
  | .cons _ h hF => ⟨h, hF.pres⟩

/-! ## Soundness -/

/-- The list of field types under an interpretation. -/
def SFields.sListI (I : SInterp) : SFields → List (String × Sorted.Ty .ty)
  | .nil => []
  | .cons n f fs => (n, f.sTyI I) :: fs.sListI I

theorem SFields.sRowOnI_pres {I : SInterp} {ρ : Sorted.Ty .row} :
    ∀ {F : SFields}, F.Pres → F.sRowOnI I ρ = Sorted.Ty.ofFields (F.sListI I) ρ
  | .nil, _ => rfl
  | .cons n f F, ⟨hf, hF⟩ => by
    rw [SFields.sRowOnI_cons, SType.sFieldI_of_ne hf, SFields.sRowOnI_pres hF]; rfl

theorem SFields.sRowOnI_absOf {I : SInterp} {ρ : Sorted.Ty .row} :
    ∀ F : SFields, F.absOf.sRowOnI I ρ = Sorted.Ty.absFields (F.sListI I) ρ
  | .nil => rfl
  | .cons n f F => by
    simp only [SFields.absOf, SFields.sRowOnI_cons, SFields.sRowOnI_absOf F]; rfl

section
variable {c : Certificate}

theorem Certificate.Valid.sholdsG (hv : c.Valid) {A : List Nat} {I : SInterp}
    (hg : SGenHyp c.state A I) (h : c.Accepts a b) :
    (a ≠ .abs → Sorted.Sub (sdefsOf c.state) (a.sTyI I) (b.sTyI I)) ∧
      Sorted.Sub (sdefsOf c.state) (a.sRowI I) (b.sRowI I) :=
  ssolution_gen hv.inv hv.nac hv.final.ranked hg h

theorem SGenHyp.extend {A gen : List Nat} {I G : SInterp} (hg : SGenHyp c.state A I)
    (hok : GenOK c Γ gen) (hcs : BoundsHold (sdefsOf c.state) c.bounds gen (swithGen gen G I)) :
    SGenHyp c.state (A ++ gen) (swithGen gen G I) := by
  have same : ∀ v, v ∉ gen → ∀ b, (b ∈ (c.bounds v).upper ∨ b ∈ (c.bounds v).lower) →
      b.sTyI (swithGen gen G I) = b.sTyI I ∧ b.sRowI (swithGen gen G I) = b.sRowI I :=
    fun v hv b hb => SType.sI_congr b fun w hw srt => by simp [swithGen, hok.avoid v hv b hb w hw]
  refine ⟨fun srt v hv => ?_, fun v hv b hb w hw => ?_, fun α hα u hu => ?_, fun α hα l hl => ?_⟩
  · simp only [List.mem_append, not_or] at hv
    simp only [swithGen, hv.2, ite_false]
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
      simp only [swithGen, hαg, ite_false]
      rw [hs.1, hs.2]
      exact hg.up α hαA u hu
  · by_cases hαg : α ∈ gen
    · exact hcs (l, .var α) (List.mem_flatMap.mpr ⟨α, hαg, List.mem_append_right _
        (List.mem_map.mpr ⟨l, hl, rfl⟩)⟩)
    · have hαA : α ∈ A := by
        simp only [List.mem_append] at hα; exact hα.resolve_right hαg
      have hs := same α hαg l (.inr hl)
      simp only [swithGen, hαg, ite_false]
      rw [hs.1, hs.2]
      exact hg.low α hαA l hl

/-- The bounds of `gen` hold of the solution itself: the scheme has an
instance. -/
theorem sbounds_hold (hv : c.Valid) {A : List Nat} {I : SInterp} (hg : SGenHyp c.state A I)
    {gen : List Nat} : BoundsHold (sdefsOf c.state) c.bounds gen (swithGen gen I I) := by
  intro q hq
  have hI : swithGen gen I I = I := funext fun srt => funext fun v => by simp [swithGen]
  rw [hI]
  obtain ⟨α, _, ⟨u, hu, rfl⟩ | ⟨l, hl, rfl⟩⟩ := mem_genCs hq
  · exact hv.sholdsG hg (.inr (hv.inLog.1 α u hu))
  · exact hv.sholdsG hg (.inr (hv.inLog.2 α l hl))

mutual
/-- **Soundness of polymorphic skeletons, sorted**: under an instance `I` of
the variables generalized so far, a skeleton checked against a valid
certificate gives a sorted declarative typing. -/
theorem SPTyp.sound (hv : c.Valid) {A : List Nat} {I : SInterp} (hg : SGenHyp c.state A I) :
    SPTyp c Γ t st → Sorted.Typ (sdefsOf c.state) (Γ.toSCtx c.bounds I) t (st.sTyI I)
  | .lit => .lit
  | .var hx => Sorted.Typ.var_mono (PCtx.lookup_toSCtx hx)
  | .inst (gen := gen) (st := st) (ρ := ρ) hx hok => by
    have hK : swithGen gen (fun srt v => I srt (ρ v)) I = fun srt v => I srt (ρ v) :=
      funext fun srt => funext fun v => by
        simp only [swithGen]; split
        · rfl
        · next hg' => rw [hok.fix v hg']
    have hinst := smkScheme_instance (σ := c.bounds) (I := I) (st := st) (gen := gen)
      (E := sdefsOf c.state) (G := fun srt v => I srt (ρ v)) (by
        intro q hq
        rw [hK, (SType.rename_sI ρ I q.1).1.symm, (SType.rename_sI ρ I q.2).1.symm,
          (SType.rename_sI ρ I q.1).2.symm, (SType.rename_sI ρ I q.2).2.symm]
        obtain ⟨α, hα, ⟨u, hu, rfl⟩ | ⟨l, hl, rfl⟩⟩ := mem_genCs hq
        · have := hv.sholdsG hg (hok.up α hα u hu)
          exact ⟨fun _ => this.1 (fun h => nomatch h), this.2⟩
        · have := hv.sholdsG hg (hok.low α hα l hl)
          exact ⟨fun h => this.1 (SType.rename_ne_abs h), this.2⟩)
    rw [hK, ← (SType.rename_sI ρ I st).1] at hinst
    exact .var (PCtx.lookup_toSCtx hx) hinst
  | .lam h => .lam (h.sound hv hg)
  | .app h₁ h₂ ha hc => .app (.sub (h₁.sound hv hg) ((hv.sholdsG hg hc).1 ha)) (h₂.sound hv hg)
  | .rcd (F := F) h => by
    have e : (SType.record F .abs).sTyI I = Sorted.Ty.record (F.sListI I) := by
      simp only [SType.sTyI, SType.sRowI, Sorted.Ty.record]
      exact congrArg Sorted.Ty.rcd (SFields.sRowOnI_pres h.pres)
    rw [e]
    exact .rcd (h.sound hv hg)
  | .sel (l := l) (st := st) h ha hc hst => by
    have hs := (hv.sholdsG hg hc).1 ha
    have e : (SType.record (.cons l st .nil) .abs).sTyI I = .rcd (.cons l (.pre (st.sTyI I)) .top) := by
      simp only [SType.sTyI, SType.sRowI, SFields.sRowOnI_cons, SType.sFieldI_of_ne hst]; rfl
    rw [e] at hs
    exact .sel (.sub (h.sound hv hg) hs)
  | .ext (F := F) (ρ := ρ) h₁ h₂ ha hc => by
    have hs := (hv.sholdsG hg hc).1 ha
    simp only [SType.sTyI, SFields.sRowOnI_absOf] at hs
    have e : (SType.record F ρ).sTyI I = .rcd (Sorted.Ty.ofFields (F.sListI I) (ρ.sRowI I)) := by
      simp only [SType.sTyI]
      exact congrArg Sorted.Ty.rcd (SFields.sRowOnI_pres h₂.pres)
    rw [e]
    exact .ext (.sub (h₁.sound hv hg) hs) (h₂.sound hv hg)
  | .extNil h => .extNil (h.sound hv hg)
  | .letIn (gen := gen) (str := str) h₁ hok h₂ => by
    refine .letIn (σ := smkScheme c.bounds I gen str) (fun τ' hτ => ?_)
      (smkScheme_instance (sbounds_hold hv hg)) (h₂.sound hv hg)
    obtain ⟨G, rfl, hcs⟩ := smkScheme_instance_inv hτ
    have ih := h₁.sound hv (hg.extend hok hcs)
    rwa [PCtx.toSCtx_withGen hok.ctx] at ih
  | .letRec (x := x) (gen := gen) (stx := stx) hf h₁ ha hc hok h₂ => by
    refine .letRec hf (σ := smkScheme c.bounds I gen stx) (fun τ' hτ => ?_)
      (smkScheme_instance (sbounds_hold hv hg)) (h₂.sound hv hg)
    obtain ⟨G, rfl, hcs⟩ := smkScheme_instance_inv hτ
    have hg' := hg.extend hok hcs
    have ih : Sorted.Typ (sdefsOf c.state)
        ((x, Sorted.Scheme.mono (stx.sTyI (swithGen gen G I))) ::
          Γ.toSCtx c.bounds (swithGen gen G I)) _ _ :=
      h₁.sound hv hg'
    rw [PCtx.toSCtx_withGen hok.ctx] at ih
    exact .sub ih ((hv.sholdsG hg' hc).1 ha)

theorem SPFields.sound (hv : c.Valid) {A : List Nat} {I : SInterp} (hg : SGenHyp c.state A I) :
    SPFields c Γ fs F → Sorted.TypFields (sdefsOf c.state) (Γ.toSCtx c.bounds I) fs (F.sListI I)
  | .nil => .nil
  | .cons h₁ _ h₂ => .cons (h₁.sound hv hg) (h₂.sound hv hg)
end

/-- No variable is generalized yet: the solution itself is an instance. -/
theorem SGenHyp.nil (c : Certificate) : SGenHyp c.state [] .gv :=
  ⟨fun _ _ _ => rfl, (fun _ _ _ _ _ _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩

/-- **Theorem 1 with let-polymorphism, for certificates, sorted.** -/
theorem SPTyp.sound_top (hv : c.Valid) (h : SPTyp c Γ t st) :
    Sorted.Typ (sdefsOf c.state) (Γ.toSCtx c.bounds .gv) t st.sTy := by
  have := h.sound hv (SGenHyp.nil c)
  rwa [SType.sTyI_gv] at this

/-! ## No recursive types in the sorted solution -/

mutual
theorem SType.sTy_gvars : ∀ a : SType, (∀ m ∈ a.sTy.gvars, m ∈ a.vars) ∧ (∀ m ∈ a.sRow.gvars, m ∈ a.vars)
  | .var _ => ⟨fun m h => by simpa [SType.sTy, Sorted.Ty.gvars, SType.vars] using h,
      fun m h => by simpa [SType.sRow, Sorted.Ty.gvars, SType.vars] using h⟩
  | .prim _ | .abs => ⟨fun _ h => by simp [SType.sTy, Sorted.Ty.gvars] at h,
      fun _ h => by simp [SType.sRow, Sorted.Ty.gvars] at h⟩
  | .arrow a b => ⟨fun m h => by
      simp only [SType.sTy, Sorted.Ty.gvars, List.mem_append] at h
      simp only [SType.vars, List.mem_append]
      exact h.imp ((SType.sTy_gvars a).1 m) ((SType.sTy_gvars b).1 m),
      fun _ h => by simp [SType.sRow, Sorted.Ty.gvars] at h⟩
  | .record fs t =>
    have hf := SFields.sRowOn_gvars fs t.sRow
    have ht := (SType.sTy_gvars t).2
    have h : ∀ m ∈ (fs.sRowOn t.sRow).gvars, m ∈ (SType.record fs t).vars := fun m hm => by
      simp only [SType.vars, List.mem_append]
      rcases hf m hm with h | h
      · exact .inl h
      · exact .inr (ht m h)
    ⟨fun m hm => h m (by simpa [SType.sTy, Sorted.Ty.gvars] using hm), h⟩

theorem SFields.sRowOn_gvars : ∀ (fs : SFields) (ρ : Sorted.Ty .row), ∀ m ∈ (fs.sRowOn ρ).gvars,
    m ∈ fs.vars ∨ m ∈ ρ.gvars
  | .nil, _, _, h => .inr h
  | .cons n f fs, ρ, m, h => by
    rw [SFields.sRowOn_cons] at h
    simp only [Sorted.Ty.gvars, List.mem_append] at h
    simp only [SFields.vars, List.mem_append]
    rcases h with h | h
    · refine .inl (.inl ?_)
      cases f with
      | abs => simp [SType.sField, Sorted.Ty.gvars] at h
      | _ => exact (SType.sTy_gvars _).1 m (by simpa [SType.sField, Sorted.Ty.gvars] using h)
    · rcases SFields.sRowOn_gvars fs ρ m h with h | h
      · exact .inl (.inr h)
      · exact .inr h
end

theorem SType.sAt_gvars (a : SType) : ∀ srt : Srt, ∀ m ∈ (a.sAt srt).gvars, m ∈ a.vars
  | .ty => (SType.sTy_gvars a).1
  | .row => (SType.sTy_gvars a).2
  | .field => fun m h => by
    cases a with
    | abs => simp [SType.sAt, SType.sField, Sorted.Ty.gvars] at h
    | _ => exact (SType.sTy_gvars _).1 m (by simpa [SType.sAt, SType.sField, Sorted.Ty.gvars] using h)

/-- **No recursive types**: the sorted solution of a valid certificate defines
each graph variable only in terms of graph variables of lower rank. -/
theorem Certificate.Valid.snonrec (hv : c.Valid) : Sorted.Defs.Ranked (sdefsOf c.state) c.rank := by
  rintro srt n _ ⟨u, hc, rfl⟩ m hm
  exact hc.ranked hv.acyclic m (SType.sAt_gvars u srt m hm)

end

end BoltCore.Alg
