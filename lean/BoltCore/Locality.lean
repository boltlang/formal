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

/-! ## What constraining keeps -/

/-- The levels and kinds are the same, and no variable was freed. -/
structure Keeps (s s' : State) : Prop where
  level : s'.level = s.level
  kind : s'.kind = s.kind
  next : s.next ≤ s'.next

namespace Keeps

theorem refl : Keeps s s := ⟨rfl, rfl, Nat.le_refl _⟩

theorem trans (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.level.trans h₁.level, h₂.kind.trans h₁.kind, Nat.le_trans h₁.next h₂.next⟩

theorem of_same (h : Same s s') : Keeps s s' := ⟨h.level, h.kind, h.next⟩

theorem remember : Keeps s (s.remember a b) := ⟨rfl, rfl, Nat.le_refl _⟩
theorem fresh : Keeps s s.fresh := ⟨rfl, rfl, Nat.le_succ _⟩
theorem addUpper : Keeps s (s.addUpper v t) := ⟨rfl, rfl, Nat.le_refl _⟩
theorem addLower : Keeps s (s.addLower v t) := ⟨rfl, rfl, Nat.le_refl _⟩

end Keeps

mutual
theorem Constrain.keeps : Constrain s a b s' → Keeps s s'
  | .cached _ => .refl
  | .refl => .refl
  | .arrow _ h₁ h₂ => Keeps.remember.trans (h₁.keeps.trans h₂.keeps)
  | .absR _ => .remember
  | .absRecord _ h₁ h₂ => Keeps.remember.trans (h₁.keeps.trans h₂.keeps)
  | .nilRecord _ h₁ h₂ => Keeps.remember.trans (h₁.keeps.trans h₂.keeps)
  | .recordNil _ _ h₁ h₂ => Keeps.remember.trans (h₁.keeps.trans h₂.keeps)
  | .record _ _ _ h₁ h₂ h₃ => Keeps.remember.trans (h₁.keeps.trans (h₂.keeps.trans h₃.keeps))
  | .varL _ _ _ h => (Keeps.remember.trans .addUpper).trans h.keeps
  | .varR _ _ _ h => (Keeps.remember.trans .addLower).trans h.keeps
  | .extLHit _ _ _ hx _ => Keeps.remember.trans (.of_same hx.same)
  | .extLNew _ _ _ hx _ h =>
    (Keeps.remember.trans (.of_same hx.same)).trans ((Keeps.remember.trans .addUpper).trans h.keeps)
  | .extRHit _ _ _ hx _ => Keeps.remember.trans (.of_same hx.same)
  | .extRNew _ _ _ hx _ h =>
    (Keeps.remember.trans (.of_same hx.same)).trans ((Keeps.remember.trans .addLower).trans h.keeps)
  | .recordSig _ _ _ _ _ h => Keeps.remember.trans h.keeps
  | .sigL _ _ h => Keeps.remember.trans h.keeps

theorem ConstrainEach.keeps : ConstrainEach s ps s' → Keeps s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.keeps.trans h₂.keeps

theorem ConstrainField.keeps : ConstrainField s a b s' → Keeps s s'
  | .toAbs | .misMis | .misOpt => .refl
  | .optOpt _ h | .preOpt _ h | .pre _ _ h => h.keeps

theorem FieldsEach.keeps : FieldsEach s ps s' → Keeps s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.keeps.trans h₂.keeps

theorem Expand.keeps : Expand s t ms t' s' → Keeps s s'
  | .none => .refl
  | .abs _ h | .nil _ h => h.keeps
  | .allAbsent _ _ h => h.keeps
  | .memo _ _ h₁ _ h₂ => h₁.keeps.trans h₂.keeps
  | .fresh _ _ h₁ _ _ _ h₂ =>
    h₁.keeps.trans
      ⟨h₂.keeps.level, h₂.keeps.kind, Nat.le_trans (Nat.le_succ _) h₂.keeps.next⟩
end

/-! ## The variables of the types constraining builds -/

section
variable {X : Nat → Prop}

theorem SType.in_abs : SType.abs.In X := fun _ h => by simp [SType.vars] at h
theorem SType.in_missing : SType.missing.In X := fun _ h => by simp [SType.vars] at h
theorem SType.in_nil : SType.nil.In X := fun _ h => by simp [SType.vars] at h

theorem SFields.In.append : ∀ {fs gs : SFields}, fs.In X → gs.In X → (fs.append gs).In X
  | .nil, _, _, h => h
  | .cons _ _ _, _, h₁, h₂ =>
    have h := SFields.in_cons.mp h₁
    SFields.in_cons.mpr ⟨h.1, SFields.In.append h.2 h₂⟩

theorem rowView_in : ∀ t : SType, t.In X → (rowView t).1.In X ∧ (rowView t).2.In X
  | .record fs t, h => by
    have h' := SType.in_record.mp h
    have ih := rowView_in t h'.2
    simp only [rowView]
    exact ⟨h'.1.append ih.1, ih.2⟩
  | .var _, h | .prim _, h | .abs, h | .missing, h | .nil, h | .arrow _ _, h | .opt _, h
  | .sig _, h => ⟨SFields.in_nil, h⟩

theorem SFields.In.lookup {l : String} {f : SType} : ∀ {fs : SFields}, fs.In X →
    fs.lookup l = some f → f.In X
  | .nil, _, h => by simp [SFields.lookup] at h
  | .cons n g rest, hfs, h => by
    have h' := SFields.in_cons.mp hfs
    simp only [SFields.lookup] at h
    split at h
    · cases h; exact h'.1
    · exact h'.2.lookup h

theorem SFields.In.common {fs₀ : SFields} (h₀ : fs₀.In X) : ∀ {fs₁ : SFields}, fs₁.In X →
    ∀ p ∈ fs₀.common fs₁, p.1.In X ∧ p.2.In X
  | .nil, _, _, h => nomatch h
  | .cons n g rest, hfs, p, hp => by
    have h' := SFields.in_cons.mp hfs
    simp only [SFields.common] at hp
    split at hp
    · next f hf =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨h₀.lookup hf, h'.1⟩
      · exact h₀.common h'.2 p hp
    · exact h₀.common h'.2 p hp

theorem SFields.In.missing {fs₀ : SFields} : ∀ {fs₁ : SFields}, fs₁.In X → (fs₀.missing fs₁).In X
  | .nil, _ => SFields.in_nil
  | .cons n g rest, hfs => by
    have h' := SFields.in_cons.mp hfs
    simp only [SFields.missing]
    split
    · exact h'.2.missing
    · exact SFields.in_cons.mpr ⟨h'.1, h'.2.missing⟩

theorem SFields.In.absPairs : ∀ {fs : SFields}, fs.In X →
    ∀ p ∈ fs.absPairs, p.1.In X ∧ p.2.In X
  | .nil, _, _, h => nomatch h
  | .cons _ f rest, hfs, p, hp => by
    have h' := SFields.in_cons.mp hfs
    simp only [SFields.absPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨SType.in_abs, h'.1⟩
    · exact h'.2.absPairs p hp

theorem SFields.In.misPairs : ∀ {fs : SFields}, fs.In X →
    ∀ p ∈ fs.misPairs, p.1.In X ∧ p.2.In X
  | .nil, _, _, h => nomatch h
  | .cons _ f rest, hfs, p, hp => by
    have h' := SFields.in_cons.mp hfs
    simp only [SFields.misPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨SType.in_missing, h'.1⟩
    · exact h'.2.misPairs p hp

theorem SFields.In.toMisPairs : ∀ {fs : SFields}, fs.In X →
    ∀ p ∈ fs.toMisPairs, p.1.In X ∧ p.2.In X
  | .nil, _, _, h => nomatch h
  | .cons _ f rest, hfs, p, hp => by
    have h' := SFields.in_cons.mp hfs
    simp only [SFields.toMisPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨h'.1, SType.in_missing⟩
    · exact h'.2.toMisPairs p hp

theorem SFields.In.absentIn {K : List String} : ∀ {fs : SFields}, fs.In X → (fs.absentIn K).In X
  | .nil, _ => SFields.in_nil
  | .cons n _ _, hfs => by
    have h' := SFields.in_cons.mp hfs
    simp only [SFields.absentIn]; split
    · exact SFields.in_cons.mpr ⟨h'.1, h'.2.absentIn⟩
    · exact h'.2.absentIn

theorem SFields.In.presentIn {K : List String} : ∀ {fs : SFields}, fs.In X → (fs.presentIn K).In X
  | .nil, _ => SFields.in_nil
  | .cons n _ _, hfs => by
    have h' := SFields.in_cons.mp hfs
    simp only [SFields.presentIn]; split
    · exact h'.2.presentIn
    · exact SFields.in_cons.mpr ⟨h'.1, h'.2.presentIn⟩

theorem SFields.In.absOf : ∀ {fs : SFields}, (fs.absOf).In X
  | .nil => SFields.in_nil
  | .cons _ _ _ => SFields.in_cons.mpr ⟨SType.in_abs, SFields.In.absOf⟩

theorem restRow_in {ex : SFields} {t : SType} (he : ex.In X) (ht : t.In X) : (restRow ex t).In X := by
  cases ex with
  | nil => exact ht
  | cons => exact SType.in_record.mpr ⟨he, ht⟩

theorem SParams.In.mem : ∀ {P : SParams}, P.In X → ∀ p ∈ P.toList, p.ty.In X
  | .nil, _, _, h => nomatch h
  | .cons _ _ _ _ _, hP, p, hp => by
    have h' := SParams.in_cons.mp hP
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h'.1
    · exact h'.2.mem p hp

theorem SType.list_in : ∀ {τs : List SType}, (∀ τ ∈ τs, τ.In X) → (SType.list τs).In X
  | [], _ => SType.in_record.mpr ⟨SFields.in_nil, SType.in_nil⟩
  | τ :: _, h =>
    SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨h τ (List.mem_cons_self ..),
      SFields.in_cons.mpr ⟨SType.list_in fun σ hσ => h σ (List.mem_cons_of_mem _ hσ),
        SFields.in_nil⟩⟩, SType.in_nil⟩

theorem SFields.ofParams_in : ∀ {ps : List (Param SType)}, (∀ p ∈ ps, p.ty.In X) →
    (SFields.ofParams ps).In X
  | [], _ => SFields.in_nil
  | p :: _, h => by
    refine SFields.in_cons.mpr ⟨?_, SFields.ofParams_in fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
    have := h p (List.mem_cons_self ..)
    cases ho : p.opt
    · simpa using this
    · simpa using SType.in_opt.mpr this

/-- The variables of an argument record are those of the signature. -/
theorem SParams.In.domain {P : SParams} (h : P.In X) (k : Nat) : (P.domain k).In X :=
  SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨SType.list_in fun _ hτ => by
      obtain ⟨p, hp, rfl⟩ := Param.mem_pos hτ
      exact h.mem p hp,
    SFields.ofParams_in fun p hp => h.mem p (Param.mem_named hp)⟩, SType.in_nil⟩

/-! ## Locality of constraining -/

/-- An expansion variable of a row variable of `X` is in `X`. -/
def ExpsIn (X : Nat → Prop) (s : State) : Prop := ∀ v L r, ((v, L), r) ∈ s.exps → X v → X r

/-- The expansion variables added between two states are in `X`. -/
def ExpsNew (X : Nat → Prop) (s s' : State) : Prop :=
  ∀ e ∈ s'.exps, e ∈ s.exps ∨ (X e.1.1 ∧ X e.2)

theorem ExpsNew.refl {s : State} : ExpsNew X s s := fun _ h => .inl h

theorem ExpsNew.trans {s₁ s₂ s₃ : State} (h₁ : ExpsNew X s₁ s₂) (h₂ : ExpsNew X s₂ s₃) :
    ExpsNew X s₁ s₃ := fun e he => (h₂ e he).elim (h₁ e) .inr

theorem ExpsNew.of_eq {s s' : State} (h : s'.exps = s.exps) : ExpsNew X s s' :=
  fun _ he => .inl (h ▸ he)

theorem ExpsNew.addExp {s : State} {k : Nat × List String} {r n : Nat} (hk : X k.1) (hr : X r) :
    ExpsNew X s { s with next := n, exps := (k, r) :: s.exps } :=
  fun _ he => (List.mem_cons.mp he).elim (fun e' => .inr (e' ▸ ⟨hk, hr⟩)) .inl

theorem ExpsIn.of_new {s s' : State} (h : ExpsIn X s) (hn : ExpsNew X s s') : ExpsIn X s' :=
  fun v L r hm hv => (hn _ hm).elim (fun hm' => h v L r hm' hv) (·.2)

theorem Local.addUpper {s : State} {v : Nat} {t : SType} (hx : XClosed X s) (hv : X v)
    (ht : t.In X) : Local X s (s.addUpper v t) :=
  ⟨hx.addUpper ht, fun _ hw => bounds_addUpper_ne fun e => hw (e ▸ hv)⟩

theorem Local.addLower {s : State} {v : Nat} {t : SType} (hx : XClosed X s) (hv : X v)
    (ht : t.In X) : Local X s (s.addLower v t) :=
  ⟨hx.addLower ht, fun _ hw => bounds_addLower_ne fun e => hw (e ▸ hv)⟩

/-- Remembering a constraint does not change the bounds. -/
theorem Local.of_remember {s s' : State} {a b : SType} (h : Local X (s.remember a b) s') :
    Local X s s' := ⟨h.closed, h.frame⟩

theorem ExpsNew.of_remember {s s' : State} {a b : SType} (h : ExpsNew X (s.remember a b) s') :
    ExpsNew X s s' := h

mutual
/-- **Locality of constraining.** -/
theorem Constrain.local : Constrain s a b s' → Alloc X s s' → a.In X → b.In X → XClosed X s →
    ExpsIn X s → Local X s s' ∧ ExpsNew X s s'
  | .cached _, _, _, _, hx, _ => ⟨.refl hx, .refl⟩
  | .refl, _, _, _, hx, _ => ⟨.refl hx, .refl⟩
  | .arrow _ h₁ h₂, hal, ha, hb, hx, he => by
    have ha' := SType.in_arrow.mp ha
    have hb' := SType.in_arrow.mp hb
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) h₂.keeps.next) hb'.1 ha'.1 hx he
    have r₂ := h₂.local (hal.sub h₁.keeps.next (Nat.le_refl _)) ha'.2 hb'.2 r₁.1.closed
      (he.of_new r₁.2)
    exact ⟨Local.of_remember (r₁.1.trans r₂.1), r₁.2.trans r₂.2⟩
  | .absR _, _, _, _, hx, _ => ⟨⟨hx, fun _ _ => rfl⟩, .refl⟩
  | .absRecord _ h₁ h₂, hal, _, hb, hx, he => by
    have hb' := SType.in_record.mp hb
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) h₂.keeps.next) hb'.1.absPairs hx he
    have r₂ := h₂.local (hal.sub h₁.keeps.next (Nat.le_refl _)) SType.in_abs hb'.2 r₁.1.closed
      (he.of_new r₁.2)
    exact ⟨Local.of_remember (r₁.1.trans r₂.1), r₁.2.trans r₂.2⟩
  | .nilRecord _ h₁ h₂, hal, _, hb, hx, he => by
    have hb' := SType.in_record.mp hb
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) h₂.keeps.next) hb'.1.misPairs hx he
    have r₂ := h₂.local (hal.sub h₁.keeps.next (Nat.le_refl _)) SType.in_nil hb'.2 r₁.1.closed
      (he.of_new r₁.2)
    exact ⟨Local.of_remember (r₁.1.trans r₂.1), r₁.2.trans r₂.2⟩
  | .recordNil _ e₀ h₁ h₂, hal, ha, _, hx, he => by
    have hv := rowView_in _ ha
    rw [e₀] at hv
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) h₂.keeps.next) hv.1.toMisPairs hx he
    have r₂ := h₂.local (hal.sub h₁.keeps.next (Nat.le_refl _)) hv.2 SType.in_nil r₁.1.closed
      (he.of_new r₁.2)
    exact ⟨Local.of_remember (r₁.1.trans r₂.1), r₁.2.trans r₂.2⟩
  | .record _ e₀ e₁ h₁ h₂ h₃, hal, ha, hb, hx, he => by
    have v₀ := rowView_in _ ha
    have v₁ := rowView_in _ hb
    rw [e₀] at v₀
    rw [e₁] at v₁
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) (Nat.le_trans h₂.keeps.next h₃.keeps.next))
      (v₀.1.common v₁.1) hx he
    have r₂ := h₂.local (hal.sub h₁.keeps.next h₃.keeps.next) v₀.2 v₁.1.missing r₁.1.closed
      (he.of_new r₁.2)
    have r₃ := h₃.local (hal.sub (Nat.le_trans h₁.keeps.next h₂.keeps.next) (Nat.le_refl _))
      (restRow_in v₀.1.missing r₂.1) v₁.2 r₂.2.1.closed (he.of_new (r₁.2.trans r₂.2.2))
    exact ⟨Local.of_remember (r₁.1.trans (r₂.2.1.trans r₃.1)), r₁.2.trans (r₂.2.2.trans r₃.2)⟩
  | .varL (s := s) (v := v) (b := b) _ _ _ h, hal, ha, hb, hx, he => by
    have hv : X v := SType.in_var.mp ha
    have l₀ := Local.of_remember (Local.addUpper (s := s.remember (.var v) b) hx hv hb)
    have r := h.local hal (fun p hp => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
      exact ⟨hx v hv l (.inr hl), hb⟩) l₀.closed he
    exact ⟨l₀.trans r.1, r.2⟩
  | .varR (s := s) (v := v) (a := a) _ _ _ h, hal, ha, hb, hx, he => by
    have hv : X v := SType.in_var.mp hb
    have l₀ := Local.of_remember (Local.addLower (s := s.remember a (.var v)) hx hv ha)
    have r := h.local hal (fun p hp => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
      exact ⟨ha, hx v hv u (.inl hu)⟩) l₀.closed he
    exact ⟨l₀.trans r.1, r.2⟩
  | .extLHit _ _ _ hx' _, hal, _, hb, hx, _ => by
    have r := hx'.local hal hb (fun _ h => nomatch h) hx
    exact ⟨Local.of_remember r.2.2, .of_eq hx'.same.exps⟩
  | .extLNew (s₁ := s₁) (v := v) (b' := b') _ _ _ hx' _ h, hal, ha, hb, hx, he => by
    have hv : X v := SType.in_var.mp ha
    have r := hx'.local (hal.sub (Nat.le_refl _) h.keeps.next) hb (fun _ h => nomatch h) hx
    have l₀ := Local.of_remember
      (Local.addUpper (s := s₁.remember (.var v) b') r.2.2.closed hv r.1)
    have hn : ExpsNew X s s₁ := .of_eq hx'.same.exps
    have r' := h.local (hal.sub hx'.same.next (Nat.le_refl _)) (fun p hp => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
      exact ⟨r.2.2.closed v hv l (.inr hl), r.1⟩) l₀.closed (he.of_new hn)
    exact ⟨(Local.of_remember r.2.2).trans (l₀.trans r'.1), hn.trans r'.2⟩
  | .extRHit _ _ _ hx' _, hal, ha, _, hx, _ => by
    have r := hx'.local hal ha (fun _ h => nomatch h) hx
    exact ⟨Local.of_remember r.2.2, .of_eq hx'.same.exps⟩
  | .extRNew (s₁ := s₁) (v := v) (a' := a') _ _ _ hx' _ h, hal, ha, hb, hx, he => by
    have hv : X v := SType.in_var.mp hb
    have r := hx'.local (hal.sub (Nat.le_refl _) h.keeps.next) ha (fun _ h => nomatch h) hx
    have l₀ := Local.of_remember
      (Local.addLower (s := s₁.remember a' (.var v)) r.2.2.closed hv r.1)
    have hn : ExpsNew X s s₁ := .of_eq hx'.same.exps
    have r' := h.local (hal.sub hx'.same.next (Nat.le_refl _)) (fun p hp => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
      exact ⟨r.1, r.2.2.closed v hv u (.inl hu)⟩) l₀.closed (he.of_new hn)
    exact ⟨(Local.of_remember r.2.2).trans (l₀.trans r'.1), hn.trans r'.2⟩
  | .recordSig (k := k) _ _ _ _ _ h, hal, ha, hb, hx, he => by
    have r := h.local hal ha ((SType.in_sig.mp hb).domain k) hx he
    exact ⟨Local.of_remember r.1, r.2⟩
  | .sigL _ _ h, hal, ha, hb, hx, he => by
    have r := h.local hal (fun p hp => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
      exact ⟨(SType.in_sig.mp ha).domain k, hb⟩) hx he
    exact ⟨Local.of_remember r.1, r.2⟩

theorem ConstrainEach.local : ConstrainEach s ps s' → Alloc X s s' →
    (∀ p ∈ ps, p.1.In X ∧ p.2.In X) → XClosed X s → ExpsIn X s → Local X s s' ∧ ExpsNew X s s'
  | .nil, _, _, hx, _ => ⟨.refl hx, .refl⟩
  | .cons h₁ h₂, hal, hp, hx, he => by
    have p₁ := hp _ (List.mem_cons_self ..)
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) h₂.keeps.next) p₁.1 p₁.2 hx he
    have r₂ := h₂.local (hal.sub h₁.keeps.next (Nat.le_refl _))
      (fun p h => hp p (List.mem_cons_of_mem _ h)) r₁.1.closed (he.of_new r₁.2)
    exact ⟨r₁.1.trans r₂.1, r₁.2.trans r₂.2⟩

theorem ConstrainField.local : ConstrainField s a b s' → Alloc X s s' → a.In X → b.In X →
    XClosed X s → ExpsIn X s → Local X s s' ∧ ExpsNew X s s'
  | .toAbs, _, _, _, hx, _ | .misMis, _, _, _, hx, _ | .misOpt, _, _, _, hx, _ =>
    ⟨.refl hx, .refl⟩
  | .optOpt _ h, hal, ha, hb, hx, he =>
    h.local hal (SType.in_opt.mp ha) (SType.in_opt.mp hb) hx he
  | .preOpt _ h, hal, ha, hb, hx, he => h.local hal ha (SType.in_opt.mp hb) hx he
  | .pre _ _ h, hal, ha, hb, hx, he => h.local hal ha hb hx he

theorem FieldsEach.local : FieldsEach s ps s' → Alloc X s s' →
    (∀ p ∈ ps, p.1.In X ∧ p.2.In X) → XClosed X s → ExpsIn X s → Local X s s' ∧ ExpsNew X s s'
  | .nil, _, _, hx, _ => ⟨.refl hx, .refl⟩
  | .cons h₁ h₂, hal, hp, hx, he => by
    have p₁ := hp _ (List.mem_cons_self ..)
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) h₂.keeps.next) p₁.1 p₁.2 hx he
    have r₂ := h₂.local (hal.sub h₁.keeps.next (Nat.le_refl _))
      (fun p h => hp p (List.mem_cons_of_mem _ h)) r₁.1.closed (he.of_new r₁.2)
    exact ⟨r₁.1.trans r₂.1, r₁.2.trans r₂.2⟩

theorem Expand.local : Expand s t ms t' s' → Alloc X s s' → t.In X → ms.In X → XClosed X s →
    ExpsIn X s → t'.In X ∧ Local X s s' ∧ ExpsNew X s s'
  | .none, _, ht, _, hx, _ => ⟨ht, .refl hx, .refl⟩
  | .abs _ h, hal, ht, hm, hx, he => ⟨ht, h.local hal hm.absPairs hx he⟩
  | .nil _ h, hal, ht, hm, hx, he => ⟨ht, h.local hal hm.misPairs hx he⟩
  | .allAbsent _ _ h, hal, ht, hm, hx, he => ⟨ht, h.local hal hm.absentIn.absPairs hx he⟩
  | .memo (v := v) _ _ h₁ hl h₂, hal, ht, hm, hx, he => by
    have hv : X v := SType.in_var.mp ht
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) h₂.keeps.next) hm.absentIn.absPairs hx he
    have he₁ := he.of_new r₁.2
    have hr := he₁ _ _ _ (lookup_mem hl) hv
    have r₂ := h₂.local (hal.sub h₁.keeps.next (Nat.le_refl _)) ht
      (SType.in_record.mpr ⟨hm.presentIn, SType.in_var.mpr hr⟩) r₁.1.closed he₁
    exact ⟨SType.in_var.mpr hr, r₁.1.trans r₂.1, r₁.2.trans r₂.2⟩
  | .fresh (s := s) (v := v) (s₁ := s₁) (ms := ms) _ _ h₁ _ _ _ h₂, hal, ht, hm, hx, he => by
    have r₁ := h₁.local (hal.sub (Nat.le_refl _) (Nat.le_trans (Nat.le_succ _) h₂.keeps.next))
      hm.absentIn.absPairs hx he
    have hr : X s₁.next :=
      hal _ h₁.keeps.next (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h₂.keeps.next)
    have hn := ExpsNew.addExp (s := s₁) (k := (v, (ms.presentIn (s.kind v)).labels))
      (n := s₁.next + 1) (SType.in_var.mp ht) hr
    have r₂ := h₂.local (fun w hw hw' => hal w (Nat.le_trans h₁.keeps.next (Nat.le_of_succ_le hw)) hw')
      ht (SType.in_record.mpr ⟨hm.presentIn, SType.in_var.mpr hr⟩) r₁.1.closed
      ((he.of_new r₁.2).of_new hn)
    exact ⟨SType.in_var.mpr hr, r₁.1.trans ⟨r₂.1.closed, r₂.1.frame⟩, r₁.2.trans (hn.trans r₂.2)⟩
end

end

/-! ## Expansion variables -/

/-- An expansion variable has the level of its row variable. -/
def ExpLevel (s : State) : Prop := ∀ v L r, ((v, L), r) ∈ s.exps → s.level r = s.level v

theorem Same.expLevel {s s' : State} (hs : Same s s') (h : ExpLevel s) : ExpLevel s' :=
  fun v L r hm => by rw [hs.level]; exact h v L r (hs.exps ▸ hm)

mutual
theorem Constrain.expLevel : Constrain s a b s' → ExpLevel s → ExpLevel s'
  | .cached _, h | .refl, h | .absR _, h => h
  | .arrow _ h₁ h₂, h | .absRecord _ h₁ h₂, h | .nilRecord _ h₁ h₂, h
  | .recordNil _ _ h₁ h₂, h => h₂.expLevel (h₁.expLevel h)
  | .record _ _ _ h₁ h₂ h₃, h => h₃.expLevel (h₂.expLevel (h₁.expLevel h))
  | .varL _ _ _ h', h | .varR _ _ _ h', h | .recordSig _ _ _ _ _ h', h | .sigL _ _ h', h =>
    h'.expLevel h
  | .extLHit _ _ _ hx _, h | .extRHit _ _ _ hx _, h => hx.same.expLevel h
  | .extLNew _ _ _ hx _ h', h | .extRNew _ _ _ hx _ h', h => h'.expLevel (hx.same.expLevel h)

theorem ConstrainEach.expLevel : ConstrainEach s ps s' → ExpLevel s → ExpLevel s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.expLevel (h₁.expLevel h)

theorem ConstrainField.expLevel : ConstrainField s a b s' → ExpLevel s → ExpLevel s'
  | .toAbs, h | .misMis, h | .misOpt, h => h
  | .optOpt _ h', h | .preOpt _ h', h | .pre _ _ h', h => h'.expLevel h

theorem FieldsEach.expLevel : FieldsEach s ps s' → ExpLevel s → ExpLevel s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.expLevel (h₁.expLevel h)

theorem Expand.expLevel : Expand s t ms t' s' → ExpLevel s → ExpLevel s'
  | .none, h => h
  | .abs _ h', h | .nil _ h', h | .allAbsent _ _ h', h => h'.expLevel h
  | .memo _ _ h₁ _ h₂, h => h₂.expLevel (h₁.expLevel h)
  | .fresh _ _ h₁ _ _ hl h₂, h =>
    h₂.expLevel fun v L r hm => by
      rcases List.mem_cons.mp hm with e | hm
      · cases e
        show (_ : State).level _ = (_ : State).level _
        rw [h₁.keeps.level]; exact hl
      · exact h₁.expLevel h v L r hm
end

/-! ## Scope of constraining -/

/-- The allocation invariants of a state: it only mentions allocated
variables, and an expansion variable has the level of its row variable. -/
structure Scope (s : State) : Prop where
  bounds : Scoped s
  exps : ∀ e ∈ s.exps, e.1.1 < s.next ∧ e.2 < s.next
  expLevel : ExpLevel s

theorem Scope.expsIn {s : State} (h : Scope s) {n : Nat} (hn : s.next ≤ n) : ExpsIn (· < n) s :=
  fun _ _ _ hm _ => Nat.lt_of_lt_of_le (h.exps _ hm).2 hn

theorem Scope.of_local {s s' : State} (h : Scope s) (hn : s.next ≤ s'.next)
    (l : Local (· < s'.next) s s') (he : ExpsNew (· < s'.next) s s') (hl : ExpLevel s') :
    Scope s' :=
  ⟨h.bounds.of_local hn l, fun e hm =>
    (he e hm).elim (fun hm' => ⟨Nat.lt_of_lt_of_le (h.exps e hm').1 hn,
      Nat.lt_of_lt_of_le (h.exps e hm').2 hn⟩) id, hl⟩

theorem Scope.remember {s : State} {a b : SType} (h : Scope s) : Scope (s.remember a b) :=
  ⟨h.bounds, h.exps, h.expLevel⟩

theorem Scope.fresh {s : State} (h : Scope s) : Scope s.fresh :=
  ⟨fun v b hb => ⟨Nat.lt_succ_of_lt (h.bounds v b hb).1,
      (h.bounds v b hb).2.mono fun _ hw => Nat.lt_succ_of_lt hw⟩,
    fun e he => ⟨Nat.lt_succ_of_lt (h.exps e he).1, Nat.lt_succ_of_lt (h.exps e he).2⟩,
    h.expLevel⟩

/-- A type in scope stays in scope. -/
theorem SType.In.scope_mono {t : SType} {n m : Nat} (h : t.In (· < n)) (hnm : n ≤ m) :
    t.In (· < m) := h.mono fun _ hw => Nat.lt_of_lt_of_le hw hnm

theorem SFields.In.scope_mono {fs : SFields} {n m : Nat} (h : fs.In (· < n)) (hnm : n ≤ m) :
    fs.In (· < m) := fun w hw => Nat.lt_of_lt_of_le (h w hw) hnm

theorem pairs_scope_mono {ps : List (SType × SType)} {n m : Nat}
    (h : ∀ p ∈ ps, p.1.In (· < n) ∧ p.2.In (· < n)) (hnm : n ≤ m) :
    ∀ p ∈ ps, p.1.In (· < m) ∧ p.2.In (· < m) :=
  fun p hp => ⟨(h p hp).1.scope_mono hnm, (h p hp).2.scope_mono hnm⟩

/-- Extrusion keeps the allocation invariants. -/
theorem Extrude.scope (h : Extrude s c pol lvl t t' s' c') (hs : Scope s)
    (ht : t.In (· < s.next)) (hc : CopiesScoped s c) : Scope s' ∧ t'.In (· < s'.next) :=
  have r := h.scoped hs.bounds ht hc
  ⟨⟨r.1, fun e he => ⟨Nat.lt_of_lt_of_le (hs.exps e (h.same.exps ▸ he)).1 h.same.next,
      Nat.lt_of_lt_of_le (hs.exps e (h.same.exps ▸ he)).2 h.same.next⟩,
    h.same.expLevel hs.expLevel⟩, r.2.1⟩

/-- **Constraining keeps the state in scope.** -/
theorem Constrain.scope (h : Constrain s a b s') (hs : Scope s) (ha : a.In (· < s.next))
    (hb : b.In (· < s.next)) : Scope s' := by
  have hn := h.keeps.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw) (ha.scope_mono hn) (hb.scope_mono hn)
    (hs.bounds.closed hn) (hs.expsIn hn)
  exact hs.of_local hn r.1 r.2 (h.expLevel hs.expLevel)

theorem ConstrainEach.scope (h : ConstrainEach s ps s') (hs : Scope s)
    (hp : ∀ p ∈ ps, p.1.In (· < s.next) ∧ p.2.In (· < s.next)) : Scope s' := by
  have hn := h.keeps.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw) (pairs_scope_mono hp hn)
    (hs.bounds.closed hn) (hs.expsIn hn)
  exact hs.of_local hn r.1 r.2 (h.expLevel hs.expLevel)

theorem FieldsEach.scope (h : FieldsEach s ps s') (hs : Scope s)
    (hp : ∀ p ∈ ps, p.1.In (· < s.next) ∧ p.2.In (· < s.next)) : Scope s' := by
  have hn := h.keeps.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw) (pairs_scope_mono hp hn)
    (hs.bounds.closed hn) (hs.expsIn hn)
  exact hs.of_local hn r.1 r.2 (h.expLevel hs.expLevel)

theorem ConstrainField.scope (h : ConstrainField s a b s') (hs : Scope s)
    (ha : a.In (· < s.next)) (hb : b.In (· < s.next)) : Scope s' := by
  have hn := h.keeps.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw) (ha.scope_mono hn) (hb.scope_mono hn)
    (hs.bounds.closed hn) (hs.expsIn hn)
  exact hs.of_local hn r.1 r.2 (h.expLevel hs.expLevel)

theorem Expand.scope (h : Expand s t ms t' s') (hs : Scope s) (ht : t.In (· < s.next))
    (hm : ms.In (· < s.next)) : Scope s' ∧ t'.In (· < s'.next) := by
  have hn := h.keeps.next
  have r := h.local (X := (· < s'.next)) (fun _ _ hw => hw) (ht.scope_mono hn)
    (hm.scope_mono hn) (hs.bounds.closed hn) (hs.expsIn hn)
  exact ⟨hs.of_local hn r.2.1 r.2.2 (h.expLevel hs.expLevel), r.1⟩

theorem ConstrainTop.keeps {s s' : State} {a b : SType} (h : ConstrainTop s a b s') : Keeps s s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact ⟨hc.keeps.level, hc.keeps.kind, hc.keeps.next⟩

theorem ConstrainTop.scope {s s' : State} {a b : SType} (h : ConstrainTop s a b s') (hs : Scope s)
    (ha : a.In (· < s.next)) (hb : b.In (· < s.next)) : Scope s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  have r := hc.scope ⟨hs.bounds, hs.exps, hs.expLevel⟩ ha hb
  exact ⟨r.bounds, r.exps, r.expLevel⟩

end BoltCore.Alg
