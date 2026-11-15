import SimpleSub.SolutionGen

/-!
# Polymorphic `let` in certificates

Typing skeletons with let-polymorphism (`PTyp`): a `let` (or `let rec`)
generalizes a list of variables `gen` of its right-hand side's type, and
each use of the bound name instantiates them with a renaming `ρ`, as
`freshen_above` does. The checker verifies:

* **generalization** (`GenOK`): bounds of variables outside `gen` do not
  mention `gen`, and neither does the context;
* **instantiation** (`InstOK`): `ρ` fixes every variable outside `gen`,
  and the renamed bounds of `gen` are accepted constraints.

The scheme of a generalized `let` is the constrained scheme whose
variables are `gen` (as fresh free type variables) and whose constraints
are their bounds (`mkScheme`). Soundness (`PTyp.sound`) types the
right-hand side at every instance through `solution_gen`, and each use at
an instance given by the copies' solution.

A nested `let` is generalized under the instance of an enclosing one, so
soundness is proved under an interpretation `I` of the variables that is
itself an instance (`GenHyp`), and the scheme's variables are numbered
above every free type variable the scheme would otherwise contain, so
substituting them captures nothing.
-/

namespace SimpleSub

/-! ## Free type variables -/

mutual
def Ty.fvars : Ty → List Nat
  | .fvar n => [n]
  | .top | .bot | .abs | .prim _ | .gvar _ => []
  | .union a b | .inter a b | .arrow a b => a.fvars ++ b.fvars
  | .record fs t => fs.fvars ++ t.fvars
  | .proj _ t => t.fvars

def Fields.fvars : Fields → List Nat
  | .nil => []
  | .cons _ f fs => f.fvars ++ fs.fvars
end

mutual
/-- Substituting variables that do not occur changes nothing. -/
theorem Ty.substM_fresh {m : Nat → Option Ty} :
    ∀ t : Ty, (∀ n ∈ t.fvars, m n = none) → t.substM m = t
  | .fvar n, h => by simp [Ty.substM, h n (by simp [Ty.fvars])]
  | .top, _ | .bot, _ | .abs, _ | .prim _, _ | .gvar _, _ => rfl
  | .union a b, h | .inter a b, h | .arrow a b, h => by
    simp only [Ty.substM]
    rw [Ty.substM_fresh a fun n hn => h n (by simp [Ty.fvars, hn]),
      Ty.substM_fresh b fun n hn => h n (by simp [Ty.fvars, hn])]
  | .record fs t, h => by
    simp only [Ty.substM]
    rw [Fields.substM_fresh fs fun n hn => h n (by simp [Ty.fvars, hn]),
      Ty.substM_fresh t fun n hn => h n (by simp [Ty.fvars, hn])]
  | .proj _ t, h => by
    simp only [Ty.substM]
    rw [Ty.substM_fresh t fun n hn => h n (by simp [Ty.fvars, hn])]

theorem Fields.substM_fresh {m : Nat → Option Ty} :
    ∀ fs : Fields, (∀ n ∈ fs.fvars, m n = none) → fs.substM m = fs
  | .nil, _ => rfl
  | .cons _ f fs, h => by
    simp only [Fields.substM]
    rw [Ty.substM_fresh f fun n hn => h n (by simp [Fields.fvars, hn]),
      Fields.substM_fresh fs fun n hn => h n (by simp [Fields.fvars, hn])]
end

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

end SimpleSub

namespace SimpleSub.Alg

open State

/-! ## Interpretations -/

mutual
theorem SType.interp_congr {I J : Nat → Ty} :
    ∀ t : SType, (∀ v ∈ t.vars, I v = J v) → t.interp I = t.interp J
  | .var v, h => h v (by simp [SType.vars])
  | .prim _, _ | .abs, _ => rfl
  | .arrow a b, h => by
    simp only [SType.interp]
    rw [SType.interp_congr a fun v hv => h v (by simp [SType.vars, hv]),
      SType.interp_congr b fun v hv => h v (by simp [SType.vars, hv])]
  | .record fs t, h => by
    simp only [SType.interp]
    rw [SFields.interp_congr fs fun v hv => h v (by simp [SType.vars, hv]),
      SType.interp_congr t fun v hv => h v (by simp [SType.vars, hv])]

theorem SFields.interp_congr {I J : Nat → Ty} :
    ∀ fs : SFields, (∀ v ∈ fs.vars, I v = J v) → fs.interp I = fs.interp J
  | .nil, _ => rfl
  | .cons _ f fs, h => by
    simp only [SFields.interp]
    rw [SType.interp_congr f fun v hv => h v (by simp [SFields.vars, hv]),
      SFields.interp_congr fs fun v hv => h v (by simp [SFields.vars, hv])]
end

mutual
theorem SType.interp_substM (I : Nat → Ty) (m : Nat → Option Ty) :
    ∀ t : SType, (t.interp I).substM m = t.interp fun v => (I v).substM m
  | .var _ => rfl
  | .prim _ | .abs => rfl
  | .arrow a b => by
    simp only [SType.interp, Ty.substM, SType.interp_substM I m a, SType.interp_substM I m b]
  | .record fs t => by
    simp only [SType.interp, Ty.substM, SFields.interp_substM I m fs, SType.interp_substM I m t]

theorem SFields.interp_substM (I : Nat → Ty) (m : Nat → Option Ty) :
    ∀ fs : SFields, (fs.interp I).substM m = fs.interp fun v => (I v).substM m
  | .nil => rfl
  | .cons _ f fs => by
    simp only [SFields.interp, Fields.substM, SType.interp_substM I m f,
      SFields.interp_substM I m fs]
end

mutual
theorem SType.rename_interp (ρ : Nat → Nat) (I : Nat → Ty) :
    ∀ t : SType, (t.rename ρ).interp I = t.interp fun v => I (ρ v)
  | .var _ | .prim _ | .abs => rfl
  | .arrow a b => by
    simp only [SType.rename, SType.interp, SType.rename_interp ρ I a, SType.rename_interp ρ I b]
  | .record fs t => by
    simp only [SType.rename, SType.interp, SFields.rename_interp ρ I fs, SType.rename_interp ρ I t]

theorem SFields.rename_interp (ρ : Nat → Nat) (I : Nat → Ty) :
    ∀ fs : SFields, (fs.rename ρ).interp I = fs.interp fun v => I (ρ v)
  | .nil => rfl
  | .cons _ f fs => by
    simp only [SFields.rename, SFields.interp, SType.rename_interp ρ I f,
      SFields.rename_interp ρ I fs]
end

mutual
theorem SType.fvars_interp {I : Nat → Ty} {n : Nat} :
    ∀ t : SType, n ∈ (t.interp I).fvars → ∃ v ∈ t.vars, n ∈ (I v).fvars
  | .var v, h => ⟨v, by simp [SType.vars], h⟩
  | .prim _, h | .abs, h => by simp [SType.interp, Ty.fvars] at h
  | .arrow a b, h => by
    simp only [SType.interp, Ty.fvars, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨v, hv, h⟩ := SType.fvars_interp a h; exact ⟨v, by simp [SType.vars, hv], h⟩
    · obtain ⟨v, hv, h⟩ := SType.fvars_interp b h; exact ⟨v, by simp [SType.vars, hv], h⟩
  | .record fs t, h => by
    simp only [SType.interp, Ty.fvars, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨v, hv, h⟩ := SFields.fvars_interp fs h; exact ⟨v, by simp [SType.vars, hv], h⟩
    · obtain ⟨v, hv, h⟩ := SType.fvars_interp t h; exact ⟨v, by simp [SType.vars, hv], h⟩

theorem SFields.fvars_interp {I : Nat → Ty} {n : Nat} :
    ∀ fs : SFields, n ∈ (fs.interp I).fvars → ∃ v ∈ fs.vars, n ∈ (I v).fvars
  | .nil, h => by simp [SFields.interp, Fields.fvars] at h
  | .cons _ f fs, h => by
    simp only [SFields.interp, Fields.fvars, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨v, hv, h⟩ := SType.fvars_interp f h; exact ⟨v, by simp [SFields.vars, hv], h⟩
    · obtain ⟨v, hv, h⟩ := SFields.fvars_interp fs h; exact ⟨v, by simp [SFields.vars, hv], h⟩
end

theorem SType.interp_ne_abs_of {I : Nat → Ty} {t : SType} (h : t.interp I ≠ .abs) : t ≠ .abs :=
  fun he => h (by subst he; rfl)

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

/-- Read the variables `gen` through `G`, the others through `I`. -/
def withGen (gen : List Nat) (G I : Nat → Ty) (v : Nat) : Ty := if v ∈ gen then G v else I v

/-- The scheme's variables are numbered from here: above every free type
variable that the types `I` gives the scheme's other variables contain. -/
def schemeBase (σ : Nat → Bounds) (I : Nat → Ty) (gen : List Nat) (st : SType) : Nat :=
  natBound ((schemeVars σ gen st).flatMap fun v => if v ∈ gen then [] else (I v).fvars)

def genName (base : Nat) (gen : List Nat) (v : Nat) : Nat := base + gen.idxOf v

/-- The interpretation inside the scheme: `gen` as its free variables. -/
def schemeF (σ : Nat → Bounds) (I : Nat → Ty) (gen : List Nat) (st : SType) : Nat → Ty :=
  withGen gen (fun v => .fvar (genName (schemeBase σ I gen st) gen v)) I

/-- The constrained scheme generalizing `gen` in `st`, under `I`. -/
def mkScheme (σ : Nat → Bounds) (I : Nat → Ty) (gen : List Nat) (st : SType) : Scheme where
  vars := gen.map (genName (schemeBase σ I gen st) gen)
  cs := (genCs σ gen).map fun p =>
    ⟨p.1.interp (schemeF σ I gen st), p.2.interp (schemeF σ I gen st), !p.1.isAbs⟩
  body := st.interp (schemeF σ I gen st)

section
variable {σ : Nat → Bounds} {I : Nat → Ty} {gen : List Nat} {st : SType}

theorem schemeBase_lt {v n : Nat} (hv : v ∈ schemeVars σ gen st) (hg : v ∉ gen)
    (hn : n ∈ (I v).fvars) : n < schemeBase σ I gen st :=
  lt_natBound (List.mem_flatMap.mpr ⟨v, hv, by simp [hg, hn]⟩)

theorem genName_inj {base v w : Nat} (hv : v ∈ gen) (hw : w ∈ gen)
    (h : genName base gen v = genName base gen w) : v = w := by
  have h' : gen.idxOf v = gen.idxOf w := by simp only [genName] at h; omega
  have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)
  have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hw)
  simp only [h'] at h1
  rw [← h1, h2]

/-- Substituting the scheme's variables only touches them. -/
theorem scheme_substM {m : Nat → Option Ty} (hm : ∀ n, n < schemeBase σ I gen st → m n = none)
    {t : SType} (ht : ∀ v ∈ t.vars, v ∈ schemeVars σ gen st) :
    (t.interp (schemeF σ I gen st)).substM m =
      t.interp (withGen gen (fun v => (Ty.fvar (genName (schemeBase σ I gen st) gen v)).substM m) I) := by
  rw [SType.interp_substM]
  apply SType.interp_congr
  intro v hv
  simp only [schemeF, withGen]
  split
  · rfl
  · next hg => exact Ty.substM_fresh _ fun n hn => hm n (schemeBase_lt (ht v hv) hg hn)

/-- The substitution that instantiates the scheme's variables with `G`. -/
def genSubst (σ : Nat → Bounds) (I : Nat → Ty) (gen : List Nat) (st : SType) (G : Nat → Ty) :
    Nat → Option Ty :=
  fun n => (gen.find? fun v => genName (schemeBase σ I gen st) gen v == n).map G

theorem genSubst_name {G : Nat → Ty} {v : Nat} (hv : v ∈ gen) :
    genSubst σ I gen st G (genName (schemeBase σ I gen st) gen v) = some (G v) := by
  simp only [genSubst]
  cases h : gen.find? fun w => genName (schemeBase σ I gen st) gen w == genName (schemeBase σ I gen st) gen v with
  | none =>
    have := List.find?_eq_none.mp h v hv
    simp at this
  | some w =>
    have hw := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [beq_iff_eq] at hp
    rw [genName_inj hw hv hp]; rfl

theorem genSubst_low {G : Nat → Ty} {n : Nat} (hn : n < schemeBase σ I gen st) :
    genSubst σ I gen st G n = none := by
  simp only [genSubst]
  have : gen.find? (fun w => genName (schemeBase σ I gen st) gen w == n) = none :=
    List.find?_eq_none.mpr fun w _ h => by
      simp only [beq_iff_eq, genName] at h; omega
  rw [this]; rfl

theorem genSubst_dom {G : Nat → Ty} {n : Nat} (h : (genSubst σ I gen st G n).isSome) :
    n ∈ (mkScheme σ I gen st).vars := by
  simp only [genSubst] at h
  obtain ⟨w, hw, hp⟩ := List.find?_isSome.mp (by rwa [Option.isSome_map] at h)
  simp only [beq_iff_eq] at hp
  exact List.mem_map.mpr ⟨w, hw, hp⟩

/-- An instance of the scheme: read `gen` through `G`, given that the
constraints (the bounds of `gen`) hold so. -/
theorem mkScheme_instance {E : Defs} {G : Nat → Ty}
    (hcs : ∀ q ∈ genCs σ gen,
      (q.1 ≠ .abs → Sub E (q.1.interp (withGen gen G I)) (q.2.interp (withGen gen G I))) ∧
        ∀ l, Sub E ((q.1.interp (withGen gen G I)).field l) ((q.2.interp (withGen gen G I)).field l)) :
    (mkScheme σ I gen st).Instance E (st.interp (withGen gen G I)) := by
  have key : ∀ t : SType, (∀ v ∈ t.vars, v ∈ schemeVars σ gen st) →
      (t.interp (schemeF σ I gen st)).substM (genSubst σ I gen st G) = t.interp (withGen gen G I) := by
    intro t ht
    rw [scheme_substM (fun n hn => genSubst_low hn) ht]
    apply SType.interp_congr
    intro _ _
    simp only [withGen]
    split
    · next hg => simp only [Ty.substM, genSubst_name hg]; rfl
    · rfl
  refine ⟨genSubst σ I gen st G, fun n h => genSubst_dom h, fun p hp => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (show p ∈ List.map _ (genCs σ gen) from hp)
    have hv := genCs_vars (st := st) hq
    simp only [SatAfter]
    rw [key q.1 hv.1, key q.2 hv.2]
    exact ⟨fun h => (hcs q hq).1 (SType.isAbs_false.mp (by simpa using h)), (hcs q hq).2⟩
  · show st.interp _ = (st.interp (schemeF σ I gen st)).substM _
    exact (key st fun v hv => List.mem_append_left _ hv).symm

/-- Conversely, every instance reads `gen` through some `G` under which the
constraints hold. -/
theorem mkScheme_instance_inv {E : Defs} {τ : Ty} (h : (mkScheme σ I gen st).Instance E τ) :
    ∃ G : Nat → Ty, τ = st.interp (withGen gen G I) ∧ ∀ q ∈ genCs σ gen,
      (q.1 ≠ .abs → Sub E (q.1.interp (withGen gen G I)) (q.2.interp (withGen gen G I))) ∧
        ∀ l, Sub E ((q.1.interp (withGen gen G I)).field l) ((q.2.interp (withGen gen G I)).field l) := by
  obtain ⟨m, hdom, hcs, rfl⟩ := h
  have hm : ∀ n, n < schemeBase σ I gen st → m n = none := fun n hn => by
    cases hmn : m n with
    | none => rfl
    | some _ =>
      have := hdom n (by simp [hmn])
      simp only [mkScheme, List.mem_map, genName] at this
      obtain ⟨_, _, rfl⟩ := this
      omega
  refine ⟨fun v => (Ty.fvar (genName (schemeBase σ I gen st) gen v)).substM m,
    scheme_substM (st := st) hm fun v hv => List.mem_append_left _ hv, fun q hq => ?_⟩
  have hv := genCs_vars (st := st) hq
  have := hcs ⟨q.1.interp (schemeF σ I gen st), q.2.interp (schemeF σ I gen st), !q.1.isAbs⟩
    (show _ ∈ List.map _ (genCs σ gen) from List.mem_map.mpr ⟨q, hq, rfl⟩)
  simp only [SatAfter] at this
  rw [scheme_substM hm hv.1, scheme_substM hm hv.2] at this
  exact ⟨fun h => this.1 (by simpa using SType.isAbs_false.mpr h), this.2⟩

/-- The scheme only depends on what `I` gives the variables it mentions. -/
theorem mkScheme_congr {J : Nat → Ty} (h : ∀ v ∈ schemeVars σ gen st, v ∉ gen → I v = J v) :
    mkScheme σ I gen st = mkScheme σ J gen st := by
  have hb : schemeBase σ I gen st = schemeBase σ J gen st := by
    simp only [schemeBase]
    congr 1
    apply flatMap_congr'
    intro v hv
    split
    · rfl
    · next hg => rw [h v hv hg]
  have hF : ∀ v ∈ schemeVars σ gen st, schemeF σ I gen st v = schemeF σ J gen st v := by
    intro v hv
    simp only [schemeF, withGen, hb]
    split
    · rfl
    · next hg => exact h v hv hg
  simp only [mkScheme, hb]
  congr 1
  · apply List.map_congr_left
    intro p hp
    have hv := genCs_vars (st := st) hp
    rw [SType.interp_congr p.1 fun v h' => hF v (hv.1 v h'),
      SType.interp_congr p.2 fun v h' => hF v (hv.2 v h')]
  · exact SType.interp_congr st fun v h' => hF v (List.mem_append_left _ h')

end

/-! ## Contexts with schemes -/

inductive CEntry where
  | mono (st : SType)
  /-- A let-bound name, generalizing `gen` in `st`. -/
  | poly (gen : List Nat) (st : SType)

def CEntry.toScheme (σ : Nat → Bounds) (I : Nat → Ty) : CEntry → Scheme
  | .mono st => .mono (st.interp I)
  | .poly gen st => mkScheme σ I gen st

/-- The entry does not mention the variables `gen'`. -/
def CEntry.Avoids (σ : Nat → Bounds) (gen' : List Nat) : CEntry → Prop
  | .mono st => Av gen' st
  | .poly gen st => ∀ v ∈ schemeVars σ gen st, v ∉ gen → v ∉ gen'

abbrev PCtx := List (String × CEntry)

def PCtx.lookup (Γ : PCtx) (x : String) : Option CEntry := (Γ.find? (·.1 = x)).map (·.2)

def PCtx.toCtx (σ : Nat → Bounds) (I : Nat → Ty) (Γ : PCtx) : Ctx :=
  Γ.map fun p => (p.1, p.2.toScheme σ I)

theorem PCtx.lookup_toCtx {σ : Nat → Bounds} {I : Nat → Ty} {Γ : PCtx} {x : String} {e : CEntry}
    (h : Γ.lookup x = some e) : (Γ.toCtx σ I).lookup x = some (e.toScheme σ I) := by
  induction Γ with
  | nil => simp [PCtx.lookup] at h
  | cons p Γ ih =>
    simp only [PCtx.lookup, List.find?_cons] at h
    simp only [PCtx.toCtx, List.map_cons, Ctx.lookup, List.find?_cons]
    by_cases hp : p.1 = x
    · simp only [hp, decide_true] at h ⊢
      simp at h
      subst h
      rfl
    · simp only [hp, decide_false] at h ⊢
      have := ih h
      simpa [PCtx.toCtx, Ctx.lookup] using this

theorem CEntry.toScheme_withGen {σ : Nat → Bounds} {I G : Nat → Ty} {gen' : List Nat}
    {e : CEntry} (h : e.Avoids σ gen') : e.toScheme σ (withGen gen' G I) = e.toScheme σ I := by
  cases e with
  | mono st =>
    simp only [CEntry.toScheme]
    exact congrArg Scheme.mono (SType.interp_congr st fun v hv => by simp [withGen, h v hv])
  | poly gen st =>
    simp only [CEntry.toScheme]
    exact (mkScheme_congr fun v hv hg => by simp [withGen, h v hv hg]).symm

theorem PCtx.toCtx_withGen {σ : Nat → Bounds} {I G : Nat → Ty} {gen' : List Nat} {Γ : PCtx}
    (h : ∀ p ∈ Γ, p.2.Avoids σ gen') : Γ.toCtx σ (withGen gen' G I) = Γ.toCtx σ I := by
  simp only [PCtx.toCtx]
  apply List.map_congr_left
  intro p hp
  rw [CEntry.toScheme_withGen (h p hp)]

/-! ## Checking generalization and instantiation -/

/-- `gen` may be generalized: bounds of other variables do not mention it,
and neither does the context. -/
structure GenOK (c : Certificate) (Γ : PCtx) (gen : List Nat) : Prop where
  avoid : ∀ v, v ∉ gen → ∀ b, (b ∈ (c.bounds v).upper ∨ b ∈ (c.bounds v).lower) → Av gen b
  ctx : ∀ p ∈ Γ, p.2.Avoids c.bounds gen

/-- A use instantiates `gen` by the renaming `ρ` (the copies `freshen_above`
made): `ρ` fixes every other variable, and the copies have the renamed
bounds. -/
structure InstOK (c : Certificate) (gen : List Nat) (ρ : Nat → Nat) : Prop where
  fix : ∀ v, v ∉ gen → ρ v = v
  up : ∀ α ∈ gen, ∀ u ∈ (c.bounds α).upper, c.Accepts (.var (ρ α)) (u.rename ρ)
  low : ∀ α ∈ gen, ∀ l ∈ (c.bounds α).lower, c.Accepts (l.rename ρ) (.var (ρ α))

/-! ## Typing skeletons with let-polymorphism -/

mutual
inductive PTyp (c : Certificate) : PCtx → Term → SType → Prop where
  | lit : PTyp c Γ (.lit n) (.prim "int")
  | var : Γ.lookup x = some (.mono st) → PTyp c Γ (.var x) st
  /-- A use of a let-bound name, instantiated by the renaming `ρ`. -/
  | inst : Γ.lookup x = some (.poly gen st) → InstOK c gen ρ → PTyp c Γ (.var x) (st.rename ρ)
  | lam : PTyp c ((x, .mono st₁) :: Γ) t st₂ → PTyp c Γ (.lam x t) (.arrow st₁ st₂)
  | app : PTyp c Γ f stf → PTyp c Γ a sta → stf ≠ .abs →
      c.Accepts stf (.arrow sta st) → PTyp c Γ (.app f a) st
  | rcd : PFields c Γ fs F → PTyp c Γ (.rcd fs) (.record F .abs)
  | sel : PTyp c Γ t st₀ → st₀ ≠ .abs →
      c.Accepts st₀ (.record (.cons l st .nil) .abs) → PTyp c Γ (.sel t l) st
  | ext : PTyp c Γ t st₀ → PFields c Γ fs F → st₀ ≠ .abs →
      c.Accepts st₀ (.record F.absOf ρ) → PTyp c Γ (.ext t fs) (.record F ρ)
  | extNil : PTyp c Γ t st → PTyp c Γ (.ext t []) st
  /-- `let`, generalizing `gen` in the right-hand side's type. -/
  | letIn : PTyp c Γ r str → GenOK c Γ gen → PTyp c ((x, .poly gen str) :: Γ) b st →
      PTyp c Γ (.letIn false x r b) st
  /-- `let rec`: `x` is monomorphic in the right-hand side, generalized after. -/
  | letRec : r.IsFun → PTyp c ((x, .mono stx) :: Γ) r inf → inf ≠ .abs → c.Accepts inf stx →
      GenOK c Γ gen → PTyp c ((x, .poly gen stx) :: Γ) b st → PTyp c Γ (.letIn true x r b) st

inductive PFields (c : Certificate) : PCtx → List (String × Term) → SFields → Prop where
  | nil : PFields c Γ [] .nil
  | cons : PTyp c Γ t st → PFields c Γ fs F → PFields c Γ ((l, t) :: fs) (.cons l st F)
end

/-! ## Soundness -/

section
variable {c : Certificate}

/-- Under an instance of the generalized variables, accepted constraints
hold (`solution_gen`). -/
theorem Certificate.Valid.holdsG (hv : c.Valid) {A : List Nat} {I : Nat → Ty}
    (hg : GenHyp c.state A I) (h : c.Accepts a b) :
    (a ≠ .abs → Sub (defsOf c.state) (a.interp I) (b.interp I)) ∧
      ∀ l, Sub (defsOf c.state) ((a.interp I).field l) ((b.interp I).field l) :=
  ⟨fun ha => SolG.holds hv.inv hv.nac hv.final.ranked hg (.ty h (.inl ha)),
   fun _ => SolG.holds hv.inv hv.nac hv.final.ranked hg (.fld h)⟩

/-- Generalizing `gen` under an instance: reading `gen` through `G`, which
satisfies the bounds of `gen`, is again an instance. -/
theorem GenHyp.extend {A gen : List Nat} {I G : Nat → Ty} (hg : GenHyp c.state A I)
    (hok : GenOK c Γ gen)
    (hcs : ∀ q ∈ genCs c.bounds gen,
      (q.1 ≠ .abs → Sub (defsOf c.state) (q.1.interp (withGen gen G I)) (q.2.interp (withGen gen G I))) ∧
        ∀ l, Sub (defsOf c.state) ((q.1.interp (withGen gen G I)).field l)
          ((q.2.interp (withGen gen G I)).field l)) :
    GenHyp c.state (A ++ gen) (withGen gen G I) := by
  have same : ∀ v, v ∉ gen → ∀ b, (b ∈ (c.bounds v).upper ∨ b ∈ (c.bounds v).lower) →
      b.interp (withGen gen G I) = b.interp I := fun v hv b hb =>
    SType.interp_congr b fun w hw => by simp [withGen, hok.avoid v hv b hb w hw]
  refine ⟨fun v hv => ?_, fun v hv b hb w hw => ?_, fun α hα u hu => ?_, fun α hα l hl => ?_⟩
  · simp only [List.mem_append, not_or] at hv
    simp only [withGen, hv.2, ite_false]
    exact hg.out v hv.1
  · simp only [List.mem_append, not_or] at hv ⊢
    exact ⟨hg.avoid v hv.1 b hb w hw, hok.avoid v hv.2 b hb w hw⟩
  · by_cases hαg : α ∈ gen
    · have := hcs (.var α, u) (List.mem_flatMap.mpr ⟨α, hαg, List.mem_append_left _
        (List.mem_map.mpr ⟨u, hu, rfl⟩)⟩)
      exact ⟨this.1 (fun h => nomatch h), this.2⟩
    · have hαA : α ∈ A := by
        simp only [List.mem_append] at hα; exact hα.resolve_right hαg
      have hI : withGen gen G I α = I α := by simp [withGen, hαg]
      show Holds _ (withGen gen G I α) (u.interp (withGen gen G I))
      rw [hI, same α hαg u (.inl hu)]
      exact hg.up α hαA u hu
  · by_cases hαg : α ∈ gen
    · have := hcs (l, .var α) (List.mem_flatMap.mpr ⟨α, hαg, List.mem_append_right _
        (List.mem_map.mpr ⟨l, hl, rfl⟩)⟩)
      exact this
    · have hαA : α ∈ A := by
        simp only [List.mem_append] at hα; exact hα.resolve_right hαg
      have hI : withGen gen G I α = I α := by simp [withGen, hαg]
      show (l ≠ .abs → Sub _ (l.interp (withGen gen G I)) (withGen gen G I α)) ∧ _
      rw [hI, same α hαg l (.inr hl)]
      exact hg.low α hαA l hl

/-- The bounds of `gen` hold of the solution itself: the scheme has an
instance. -/
theorem bounds_hold (hv : c.Valid) {A : List Nat} {I : Nat → Ty} (hg : GenHyp c.state A I)
    {gen : List Nat} :
    ∀ q ∈ genCs c.bounds gen,
      (q.1 ≠ .abs → Sub (defsOf c.state) (q.1.interp (withGen gen I I)) (q.2.interp (withGen gen I I))) ∧
        ∀ l, Sub (defsOf c.state) ((q.1.interp (withGen gen I I)).field l)
          ((q.2.interp (withGen gen I I)).field l) := by
  intro q hq
  have hI : withGen gen I I = I := funext fun v => by simp [withGen]
  rw [hI]
  obtain ⟨α, _, ⟨u, hu, rfl⟩ | ⟨l, hl, rfl⟩⟩ := mem_genCs hq
  · exact hv.holdsG hg (.inr (hv.inLog.1 α u hu))
  · exact hv.holdsG hg (.inr (hv.inLog.2 α l hl))

mutual
/-- **Soundness of polymorphic skeletons**: under an instance `I` of the
variables generalized so far, a skeleton checked against a valid
certificate gives a declarative typing with constrained schemes. -/
theorem PTyp.sound (hv : c.Valid) {A : List Nat} {I : Nat → Ty} (hg : GenHyp c.state A I) :
    PTyp c Γ t st → Typ (defsOf c.state) (Γ.toCtx c.bounds I) t (st.interp I)
  | .lit => .lit
  | .var hx => Typ.var_mono (PCtx.lookup_toCtx hx)
  | .inst (gen := gen) (st := st) (ρ := ρ) hx hok => by
    -- the copies' solution is an instance of the scheme
    have hK : withGen gen (fun v => I (ρ v)) I = fun v => I (ρ v) := funext fun v => by
      simp only [withGen]; split
      · rfl
      · next hg' => rw [hok.fix v hg']
    have hinst := mkScheme_instance (σ := c.bounds) (I := I) (st := st) (E := defsOf c.state)
      (G := fun v => I (ρ v)) (by
        intro q hq
        rw [hK, SType.rename_interp ρ I q.1 |>.symm, SType.rename_interp ρ I q.2 |>.symm]
        obtain ⟨α, hα, ⟨u, hu, rfl⟩ | ⟨l, hl, rfl⟩⟩ := mem_genCs hq
        · have := hv.holdsG hg (hok.up α hα u hu)
          exact ⟨fun _ => this.1 (fun h => nomatch h), this.2⟩
        · have := hv.holdsG hg (hok.low α hα l hl)
          exact ⟨fun h => this.1 (SType.rename_ne_abs h), this.2⟩)
    rw [hK, ← SType.rename_interp] at hinst
    exact .var (PCtx.lookup_toCtx hx) hinst
  | .lam h => .lam (h.sound hv hg)
  | .app h₁ h₂ ha hc => .app (.sub (h₁.sound hv hg) ((hv.holdsG hg hc).1 ha)) (h₂.sound hv hg)
  | .rcd h => .rcd (h.sound hv hg)
  | .sel h ha hc => .sel (.sub (h.sound hv hg) ((hv.holdsG hg hc).1 ha))
  | .ext h₁ h₂ ha hc => by
    have hs := (hv.holdsG hg hc).1 ha
    simp only [SType.interp, SFields.interp_absOf] at hs
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
        ((x, Scheme.mono (stx.interp (withGen gen G I))) :: Γ.toCtx c.bounds (withGen gen G I)) _ _ :=
      h₁.sound hv hg'
    rw [PCtx.toCtx_withGen hok.ctx] at ih
    exact .sub ih ((hv.holdsG hg' hc).1 ha)

theorem PFields.sound (hv : c.Valid) {A : List Nat} {I : Nat → Ty} (hg : GenHyp c.state A I) :
    PFields c Γ fs F → TypFields (defsOf c.state) (Γ.toCtx c.bounds I) fs (F.interp I)
  | .nil => .nil
  | .cons h₁ h₂ => .cons (h₁.sound hv hg) (h₂.sound hv hg)
end

/-- No variable is generalized yet: the solution itself is an instance. -/
theorem GenHyp.top (c : Certificate) : GenHyp c.state [] .gvar :=
  ⟨fun _ _ => rfl, (fun _ _ _ _ _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-- **Theorem 1 with let-polymorphism, for certificates**: a polymorphic
skeleton checked against a valid certificate gives a declarative typing
with constrained schemes. -/
theorem PTyp.sound_top (hv : c.Valid) (h : PTyp c Γ t st) :
    Typ (defsOf c.state) (Γ.toCtx c.bounds .gvar) t st.toTy := by
  have := h.sound hv (GenHyp.top c)
  rwa [SType.interp_gvar] at this

end

end SimpleSub.Alg
