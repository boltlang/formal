import BoltCore.Extrusion

/-!
# Locality

A set `X` of variables is *closed* in a state when the bounds of its
variables only mention its variables (`XClosed`). A run of the algorithm
on types in a closed set, which contains the variables the run allocates,
keeps the set closed and does not touch the bounds of a variable outside
it (`Extrude.local`).

No levels are involved. Two instances matter:

* **scope** (`Scoped`): `X` is the variables below the counter at the end
  of the run. So every variable in play is allocated, and a variable that
  is not has no bounds: a fresh variable is fresh;
* with levels, `X` is the variables of level at most `lvl` and those the
  run allocates: a run at level `lvl` leaves the variables above it alone,
  which is why generalizing them is sound.
-/

namespace BoltCore.Alg

open State

/-! ## The variables of a type -/

/-- Every variable of the type is in `X`. -/
def SType.In (X : Nat → Prop) (t : SType) : Prop := ∀ w ∈ t.vars, X w

def SFields.In (X : Nat → Prop) (fs : SFields) : Prop := ∀ w ∈ fs.vars, X w

def SParams.In (X : Nat → Prop) (P : SParams) : Prop := ∀ w ∈ P.vars, X w

section
variable {X : Nat → Prop}

theorem SType.in_var {v : Nat} : (SType.var v).In X ↔ X v := by simp [SType.In, SType.vars]

theorem SType.in_arrow {a b : SType} : (SType.arrow a b).In X ↔ a.In X ∧ b.In X := by
  simp only [SType.In, SType.vars, List.mem_append]
  exact ⟨fun h => ⟨fun w hw => h w (.inl hw), fun w hw => h w (.inr hw)⟩,
    fun h w hw => hw.elim (h.1 w) (h.2 w)⟩

theorem SType.in_record {fs : SFields} {t : SType} :
    (SType.record fs t).In X ↔ fs.In X ∧ t.In X := by
  simp only [SType.In, SFields.In, SType.vars, List.mem_append]
  exact ⟨fun h => ⟨fun w hw => h w (.inl hw), fun w hw => h w (.inr hw)⟩,
    fun h w hw => hw.elim (h.1 w) (h.2 w)⟩

theorem SType.in_opt {t : SType} : (SType.opt t).In X ↔ t.In X := by simp [SType.In, SType.vars]

theorem SType.in_sig {P : SParams} : (SType.sig P).In X ↔ P.In X := by
  simp [SType.In, SParams.In, SType.vars]

theorem SFields.in_nil : SFields.nil.In X := fun _ h => by simp [SFields.vars] at h

theorem SFields.in_cons {n : String} {f : SType} {fs : SFields} :
    (SFields.cons n f fs).In X ↔ f.In X ∧ fs.In X := by
  simp only [SType.In, SFields.In, SFields.vars, List.mem_append]
  exact ⟨fun h => ⟨fun w hw => h w (.inl hw), fun w hw => h w (.inr hw)⟩,
    fun h w hw => hw.elim (h.1 w) (h.2 w)⟩

theorem SParams.in_nil : SParams.nil.In X := fun _ h => by simp [SParams.vars] at h

theorem SParams.in_cons {n : String} {k : PKind} {o : Bool} {τ : SType} {P : SParams} :
    (SParams.cons n k o τ P).In X ↔ τ.In X ∧ P.In X := by
  simp only [SType.In, SParams.In, SParams.vars, List.mem_append]
  exact ⟨fun h => ⟨fun w hw => h w (.inl hw), fun w hw => h w (.inr hw)⟩,
    fun h w hw => hw.elim (h.1 w) (h.2 w)⟩

theorem SType.In.mono {Y : Nat → Prop} {t : SType} (h : ∀ w, X w → Y w) (ht : t.In X) : t.In Y :=
  fun w hw => h w (ht w hw)

end

/-! ## Closed sets -/

/-- The bounds of the variables of `X` only mention variables of `X`. -/
def XClosed (X : Nat → Prop) (s : State) : Prop :=
  ∀ v, X v → ∀ b, (b ∈ (s.bounds v).upper ∨ b ∈ (s.bounds v).lower) → b.In X

section
variable {X : Nat → Prop}

theorem XClosed.addUpper {s : State} {v : Nat} {t : SType} (h : XClosed X s) (ht : t.In X) :
    XClosed X (s.addUpper v t) := by
  intro w hw b hb
  by_cases e : w = v
  · subst e
    simp only [State.addUpper, ite_true, List.mem_cons] at hb
    rcases hb with (rfl | hb) | hb
    · exact ht
    · exact h w hw b (.inl hb)
    · exact h w hw b (.inr hb)
  · rw [bounds_addUpper_ne e] at hb; exact h w hw b hb

theorem XClosed.addLower {s : State} {v : Nat} {t : SType} (h : XClosed X s) (ht : t.In X) :
    XClosed X (s.addLower v t) := by
  intro w hw b hb
  by_cases e : w = v
  · subst e
    simp only [State.addLower, ite_true, List.mem_cons] at hb
    rcases hb with hb | rfl | hb
    · exact h w hw b (.inl hb)
    · exact ht
    · exact h w hw b (.inr hb)
  · rw [bounds_addLower_ne e] at hb; exact h w hw b hb

theorem XClosed.addUppers {s : State} {v : Nat} {ts : List SType} (h : XClosed X s)
    (ht : ∀ t ∈ ts, t.In X) : XClosed X (s.addUppers v ts) := by
  intro w hw b hb
  by_cases e : w = v
  · subst e
    simp only [State.addUppers, ite_true, List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · exact ht b hb
    · exact h w hw b (.inl hb)
    · exact h w hw b (.inr hb)
  · rw [bounds_addUppers_ne e] at hb; exact h w hw b hb

theorem XClosed.addLowers {s : State} {v : Nat} {ts : List SType} (h : XClosed X s)
    (ht : ∀ t ∈ ts, t.In X) : XClosed X (s.addLowers v ts) := by
  intro w hw b hb
  by_cases e : w = v
  · subst e
    simp only [State.addLowers, ite_true, List.mem_append] at hb
    rcases hb with hb | hb | hb
    · exact h w hw b (.inl hb)
    · exact ht b hb
    · exact h w hw b (.inr hb)
  · rw [bounds_addLowers_ne e] at hb; exact h w hw b hb

/-- What a run does to a closed set: its result is in the set, the set
stays closed, and the bounds of the variables outside it are untouched. -/
structure Local (X : Nat → Prop) (s s' : State) : Prop where
  closed : XClosed X s'
  frame : ∀ v, ¬ X v → s'.bounds v = s.bounds v

theorem Local.refl {s : State} (h : XClosed X s) : Local X s s := ⟨h, fun _ _ => rfl⟩

theorem Local.trans {s₁ s₂ s₃ : State} (h₁ : Local X s₁ s₂) (h₂ : Local X s₂ s₃) : Local X s₁ s₃ :=
  ⟨h₂.closed, fun v hv => (h₂.frame v hv).trans (h₁.frame v hv)⟩

/-- Logging does not change the bounds. -/
theorem Local.logAll {s s' : State} {ps : List (SType × SType)} (h : Local X s s') :
    Local X s (s'.logAll ps) := ⟨h.closed, h.frame⟩

/-- The variables allocated between two states are in `X`. -/
def Alloc (X : Nat → Prop) (s s' : State) : Prop := ∀ w, s.next ≤ w → w < s'.next → X w

theorem Alloc.sub {s s₁ s₂ s' : State} (h : Alloc X s s') (h₁ : s.next ≤ s₁.next)
    (h₂ : s₂.next ≤ s'.next) : Alloc X s₁ s₂ :=
  fun w hw hw' => h w (Nat.le_trans h₁ hw) (Nat.lt_of_lt_of_le hw' h₂)

/-- Every copy is in `X`. -/
def CopiesIn (X : Nat → Prop) (c : Copies) : Prop := ∀ e ∈ c, X e.2

theorem CopiesIn.cons {c : Copies} {k : Nat × Bool} {w : Nat} (h : CopiesIn X c) (hw : X w) :
    CopiesIn X ((k, w) :: c) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hw
  · exact h e he

mutual
/-- **Locality of extrusion.** -/
theorem Extrude.local : Extrude s c pol lvl t t' s' c' → Alloc X s s' → t.In X → CopiesIn X c →
    XClosed X s → t'.In X ∧ CopiesIn X c' ∧ Local X s s'
  | .low _, _, ht, hc, hx => ⟨ht, hc, .refl hx⟩
  | .arrow _ h₁ h₂, ha, ht, hc, hx => by
    have ht' := SType.in_arrow.mp ht
    have r₁ := h₁.local (ha.sub (Nat.le_refl _) (h₂.same.next)) ht'.1 hc hx
    have r₂ := h₂.local (ha.sub h₁.same.next (Nat.le_refl _)) ht'.2 r₁.2.1 r₁.2.2.closed
    exact ⟨SType.in_arrow.mpr ⟨r₁.1, r₂.1⟩, r₂.2.1, (r₁.2.2.trans r₂.2.2).logAll⟩
  | .record _ h₁ h₂, ha, ht, hc, hx => by
    have ht' := SType.in_record.mp ht
    have r₁ := h₁.local (ha.sub (Nat.le_refl _) (h₂.same.next)) ht'.1 hc hx
    have r₂ := h₂.local (ha.sub h₁.same.next (Nat.le_refl _)) ht'.2 r₁.2.1 r₁.2.2.closed
    exact ⟨SType.in_record.mpr ⟨r₁.1, r₂.1⟩, r₂.2.1, (r₁.2.2.trans r₂.2.2).logAll⟩
  | .sig _ h, ha, ht, hc, hx => by
    have r := h.local ha (SType.in_sig.mp ht) hc hx
    exact ⟨SType.in_sig.mpr r.1, r.2.1, r.2.2.logAll⟩
  | .varCopied _ hw, _, _, hc, hx => ⟨SType.in_var.mpr (hc _ (lookup_mem hw)), hc, (Local.refl hx).logAll⟩
  | .varPos (s := s) (v := v) _ _ _ _ h, ha, ht, hc, hx => by
    have hv : X v := SType.in_var.mp ht
    have hn : X s.next := ha _ (Nat.le_refl _) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h.same.next)
    have hx₀ : XClosed X ((s.fresh.addUpper v (.var s.next)).logAll [(.var v, .var s.next)]) :=
      XClosed.addUpper (s := s.fresh) hx (SType.in_var.mpr hn)
    have r := h.local (fun w hw hw' => ha w (Nat.le_of_succ_le hw) hw')
      (fun b hb => hx v hv b (.inr hb)) (hc.cons hn) hx₀
    refine ⟨SType.in_var.mpr hn, r.2.1, XClosed.addLowers (s := _) r.2.2.closed r.1, fun w hw => ?_⟩
    have e₁ : w ≠ s.next := fun e => hw (e ▸ hn)
    have e₂ : w ≠ v := fun e => hw (e ▸ hv)
    show ((_ : State).addLowers s.next _).bounds w = _
    rw [bounds_addLowers_ne e₁, r.2.2.frame w hw]
    exact bounds_addUpper_ne e₂
  | .varNeg (s := s) (v := v) _ _ _ _ h, ha, ht, hc, hx => by
    have hv : X v := SType.in_var.mp ht
    have hn : X s.next := ha _ (Nat.le_refl _) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h.same.next)
    have hx₀ : XClosed X ((s.fresh.addLower v (.var s.next)).logAll [(.var s.next, .var v)]) :=
      XClosed.addLower (s := s.fresh) hx (SType.in_var.mpr hn)
    have r := h.local (fun w hw hw' => ha w (Nat.le_of_succ_le hw) hw')
      (fun b hb => hx v hv b (.inl hb)) (hc.cons hn) hx₀
    refine ⟨SType.in_var.mpr hn, r.2.1, XClosed.addUppers (s := _) r.2.2.closed r.1, fun w hw => ?_⟩
    have e₁ : w ≠ s.next := fun e => hw (e ▸ hn)
    have e₂ : w ≠ v := fun e => hw (e ▸ hv)
    show ((_ : State).addUppers s.next _).bounds w = _
    rw [bounds_addUppers_ne e₁, r.2.2.frame w hw]
    exact bounds_addLower_ne e₂

theorem ExtrudeFields.local : ExtrudeFields s c pol lvl fs fs' s' c' → Alloc X s s' → fs.In X →
    CopiesIn X c → XClosed X s → fs'.In X ∧ CopiesIn X c' ∧ Local X s s'
  | .nil, _, ht, hc, hx => ⟨ht, hc, .refl hx⟩
  | .opt h₁ h₂, ha, ht, hc, hx => by
    have ht' := SFields.in_cons.mp ht
    have r₁ := h₁.local (ha.sub (Nat.le_refl _) (h₂.same.next)) (SType.in_opt.mp ht'.1) hc hx
    have r₂ := h₂.local (ha.sub h₁.same.next (Nat.le_refl _)) ht'.2 r₁.2.1 r₁.2.2.closed
    exact ⟨SFields.in_cons.mpr ⟨SType.in_opt.mpr r₁.1, r₂.1⟩, r₂.2.1, r₁.2.2.trans r₂.2.2⟩
  | .cons _ h₁ h₂, ha, ht, hc, hx => by
    have ht' := SFields.in_cons.mp ht
    have r₁ := h₁.local (ha.sub (Nat.le_refl _) (h₂.same.next)) ht'.1 hc hx
    have r₂ := h₂.local (ha.sub h₁.same.next (Nat.le_refl _)) ht'.2 r₁.2.1 r₁.2.2.closed
    exact ⟨SFields.in_cons.mpr ⟨r₁.1, r₂.1⟩, r₂.2.1, r₁.2.2.trans r₂.2.2⟩

theorem ExtrudeParams.local : ExtrudeParams s c pol lvl P P' s' c' → Alloc X s s' → P.In X →
    CopiesIn X c → XClosed X s → P'.In X ∧ CopiesIn X c' ∧ Local X s s'
  | .nil, _, ht, hc, hx => ⟨ht, hc, .refl hx⟩
  | .cons h₁ h₂, ha, ht, hc, hx => by
    have ht' := SParams.in_cons.mp ht
    have r₁ := h₁.local (ha.sub (Nat.le_refl _) (h₂.same.next)) ht'.1 hc hx
    have r₂ := h₂.local (ha.sub h₁.same.next (Nat.le_refl _)) ht'.2 r₁.2.1 r₁.2.2.closed
    exact ⟨SParams.in_cons.mpr ⟨r₁.1, r₂.1⟩, r₂.2.1, r₁.2.2.trans r₂.2.2⟩

theorem ExtrudeEach.local : ExtrudeEach s c pol lvl ts ts' s' c' → Alloc X s s' →
    (∀ t ∈ ts, t.In X) → CopiesIn X c → XClosed X s →
    (∀ t' ∈ ts', t'.In X) ∧ CopiesIn X c' ∧ Local X s s'
  | .nil, _, _, hc, hx => ⟨(fun _ h => nomatch h), hc, .refl hx⟩
  | .cons h₁ h₂, ha, ht, hc, hx => by
    have r₁ := h₁.local (ha.sub (Nat.le_refl _) (h₂.same.next)) (ht _ (List.mem_cons_self ..)) hc hx
    have r₂ := h₂.local (ha.sub h₁.same.next (Nat.le_refl _))
      (fun t h => ht t (List.mem_cons_of_mem _ h)) r₁.2.1 r₁.2.2.closed
    refine ⟨fun t' h => ?_, r₂.2.1, r₁.2.2.trans r₂.2.2⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact r₁.1
    · exact r₂.1 t' h
end

end

/-! ## Scope -/

/-- Every variable with a bound is allocated, and so are the variables of
its bounds. So a variable that is not allocated has no bounds. -/
def Scoped (s : State) : Prop :=
  ∀ v b, (b ∈ (s.bounds v).upper ∨ b ∈ (s.bounds v).lower) → v < s.next ∧ b.In (· < s.next)

/-- The copies are allocated. -/
abbrev CopiesScoped (s : State) (c : Copies) : Prop := CopiesIn (· < s.next) c

/-- A scoped state is closed for the variables below any later counter. -/
theorem Scoped.closed {s : State} (h : Scoped s) {n : Nat} (hn : s.next ≤ n) :
    XClosed (· < n) s :=
  fun v _ b hb => (h v b hb).2.mono fun _ hw => Nat.lt_of_lt_of_le hw hn

/-- A state that is closed for the variables below its counter, and came
from a scoped one without touching the others, is scoped. -/
theorem Scoped.of_local {s s' : State} (h : Scoped s) (hn : s.next ≤ s'.next)
    (l : Local (· < s'.next) s s') : Scoped s' := by
  intro v b hb
  by_cases hv : v < s'.next
  · exact ⟨hv, l.closed v hv b hb⟩
  · rw [l.frame v hv] at hb
    exact absurd (Nat.lt_of_lt_of_le (h v b hb).1 hn) hv

/-- A variable that is not allocated has no bounds. -/
theorem Scoped.fresh_upper {s : State} (h : Scoped s) {v : Nat} (hv : s.next ≤ v) :
    (s.bounds v).upper = [] := by
  cases e : (s.bounds v).upper with
  | nil => rfl
  | cons x _ => exact absurd (h v x (.inl (e ▸ List.mem_cons_self ..))).1 (Nat.not_lt.mpr hv)

theorem Scoped.fresh_lower {s : State} (h : Scoped s) {v : Nat} (hv : s.next ≤ v) :
    (s.bounds v).lower = [] := by
  cases e : (s.bounds v).lower with
  | nil => rfl
  | cons x _ => exact absurd (h v x (.inr (e ▸ List.mem_cons_self ..))).1 (Nat.not_lt.mpr hv)

/-- **Extrusion keeps the state scoped.** -/
theorem Extrude.scoped (h : Extrude s c pol lvl t t' s' c') (hs : Scoped s)
    (ht : t.In (· < s.next)) (hc : CopiesScoped s c) :
    Scoped s' ∧ t'.In (· < s'.next) ∧ CopiesScoped s' c' := by
  have hn := h.same.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw)
    (ht.mono fun _ hw => Nat.lt_of_lt_of_le hw hn)
    (fun e he => Nat.lt_of_lt_of_le (hc e he) hn) (hs.closed hn)
  exact ⟨hs.of_local hn r.2.2, r.1, r.2.1⟩

theorem ExtrudeEach.scoped (h : ExtrudeEach s c pol lvl ts ts' s' c') (hs : Scoped s)
    (ht : ∀ t ∈ ts, t.In (· < s.next)) (hc : CopiesScoped s c) :
    Scoped s' ∧ (∀ t' ∈ ts', t'.In (· < s'.next)) ∧ CopiesScoped s' c' := by
  have hn := h.same.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw)
    (fun t h' => (ht t h').mono fun _ hw => Nat.lt_of_lt_of_le hw hn)
    (fun e he => Nat.lt_of_lt_of_le (hc e he) hn) (hs.closed hn)
  exact ⟨hs.of_local hn r.2.2, r.1, r.2.1⟩

theorem ExtrudeFields.scoped (h : ExtrudeFields s c pol lvl fs fs' s' c') (hs : Scoped s)
    (ht : fs.In (· < s.next)) (hc : CopiesScoped s c) :
    Scoped s' ∧ fs'.In (· < s'.next) ∧ CopiesScoped s' c' := by
  have hn := h.same.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw)
    (fun w hw => Nat.lt_of_lt_of_le (ht w hw) hn)
    (fun e he => Nat.lt_of_lt_of_le (hc e he) hn) (hs.closed hn)
  exact ⟨hs.of_local hn r.2.2, r.1, r.2.1⟩

theorem ExtrudeParams.scoped (h : ExtrudeParams s c pol lvl P P' s' c') (hs : Scoped s)
    (ht : P.In (· < s.next)) (hc : CopiesScoped s c) :
    Scoped s' ∧ P'.In (· < s'.next) ∧ CopiesScoped s' c' := by
  have hn := h.same.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw)
    (fun w hw => Nat.lt_of_lt_of_le (ht w hw) hn)
    (fun e he => Nat.lt_of_lt_of_le (hc e he) hn) (hs.closed hn)
  exact ⟨hs.of_local hn r.2.2, r.1, r.2.1⟩

end BoltCore.Alg
