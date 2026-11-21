import BoltCore.Algorithm

/-!
# Extrusion: what it leaves alone

Facts about `Extrude` that do not involve the log: it only allocates
variables and adds bounds (`Same`), its result has level at most the
target level (`Extrude.level_le`), it has the shape of the original
(`Extrude.con`), and it does not touch the bounds of a variable whose
level is low enough (`Extrude.frame`).
-/

namespace BoltCore.Alg

open State

/-! ## What extrusion does not change -/

/-- The levels, kinds, cache and expansion table are the same, and no
variable was freed. -/
structure Same (s s' : State) : Prop where
  level : s'.level = s.level
  kind : s'.kind = s.kind
  cache : s'.cache = s.cache
  exps : s'.exps = s.exps
  next : s.next ≤ s'.next

namespace Same

theorem refl : Same s s := ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem trans (h₁ : Same s₁ s₂) (h₂ : Same s₂ s₃) : Same s₁ s₃ :=
  ⟨h₂.level.trans h₁.level, h₂.kind.trans h₁.kind, h₂.cache.trans h₁.cache,
    h₂.exps.trans h₁.exps, Nat.le_trans h₁.next h₂.next⟩

theorem logAll : Same s (s.logAll ps) := ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩
theorem addUpper : Same s (s.addUpper v t) := ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩
theorem addLower : Same s (s.addLower v t) := ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩
theorem addUppers : Same s (s.addUppers v ts) := ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩
theorem addLowers : Same s (s.addLowers v ts) := ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩
theorem fresh : Same s s.fresh := ⟨rfl, rfl, rfl, rfl, Nat.le_succ _⟩

end Same

mutual
theorem Extrude.same : Extrude s c pol lvl t t' s' c' → Same s s'
  | .low _ => .refl
  | .arrow _ h₁ h₂ => (h₁.same.trans h₂.same).trans .logAll
  | .record _ h₁ h₂ => (h₁.same.trans h₂.same).trans .logAll
  | .sig _ h => h.same.trans .logAll
  | .varCopied _ _ => .logAll
  | .varPos _ _ _ _ h =>
    ((Same.fresh.trans (Same.addUpper.trans .logAll)).trans h.same).trans
      (Same.addLowers.trans .logAll)
  | .varNeg _ _ _ _ h =>
    ((Same.fresh.trans (Same.addLower.trans .logAll)).trans h.same).trans
      (Same.addUppers.trans .logAll)

theorem ExtrudeFields.same : ExtrudeFields s c pol lvl fs fs' s' c' → Same s s'
  | .nil => .refl
  | .opt h₁ h₂ => h₁.same.trans h₂.same
  | .cons _ h₁ h₂ => h₁.same.trans h₂.same

theorem ExtrudeParams.same : ExtrudeParams s c pol lvl P P' s' c' → Same s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.same.trans h₂.same

theorem ExtrudeEach.same : ExtrudeEach s c pol lvl ts ts' s' c' → Same s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.same.trans h₂.same
end

/-! ## The level of the result -/

/-- Every copy has level at most `lvl`. -/
def CopiesLow (L : Nat → Nat) (lvl : Nat) (c : Copies) : Prop := ∀ e ∈ c, L e.2 ≤ lvl

theorem CopiesLow.nil : CopiesLow L lvl [] := fun _ h => nomatch h

theorem CopiesLow.cons (h : CopiesLow L lvl c) (hw : L w ≤ lvl) : CopiesLow L lvl ((k, w) :: c) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hw
  · exact h e he

mutual
/-- The result of an extrusion has level at most the target level. -/
theorem Extrude.level_le : Extrude s c pol lvl t t' s' c' → s.level = L → CopiesLow L lvl c →
    t'.level L ≤ lvl ∧ CopiesLow L lvl c'
  | .low h, e, hc => ⟨e ▸ h, hc⟩
  | .arrow _ h₁ h₂, e, hc => by
    have r₁ := h₁.level_le e hc
    have r₂ := h₂.level_le (h₁.same.level.trans e) r₁.2
    exact ⟨Nat.max_le.mpr ⟨r₁.1, r₂.1⟩, r₂.2⟩
  | .record _ h₁ h₂, e, hc => by
    have r₁ := h₁.level_le e hc
    have r₂ := h₂.level_le (h₁.same.level.trans e) r₁.2
    exact ⟨Nat.max_le.mpr ⟨r₁.1, r₂.1⟩, r₂.2⟩
  | .sig _ h, e, hc => h.level_le e hc
  | .varCopied _ hw, _, hc => ⟨hc _ (lookup_mem hw), hc⟩
  | .varPos _ _ hl _ h, e, hc =>
    ⟨e ▸ Nat.le_of_eq hl, (h.level_le e (hc.cons (e ▸ Nat.le_of_eq hl))).2⟩
  | .varNeg _ _ hl _ h, e, hc =>
    ⟨e ▸ Nat.le_of_eq hl, (h.level_le e (hc.cons (e ▸ Nat.le_of_eq hl))).2⟩

theorem ExtrudeFields.level_le : ExtrudeFields s c pol lvl fs fs' s' c' → s.level = L →
    CopiesLow L lvl c → fs'.level L ≤ lvl ∧ CopiesLow L lvl c'
  | .nil, _, hc => ⟨Nat.zero_le _, hc⟩
  | .opt h₁ h₂, e, hc => by
    have r₁ := h₁.level_le e hc
    have r₂ := h₂.level_le (h₁.same.level.trans e) r₁.2
    exact ⟨Nat.max_le.mpr ⟨r₁.1, r₂.1⟩, r₂.2⟩
  | .cons _ h₁ h₂, e, hc => by
    have r₁ := h₁.level_le e hc
    have r₂ := h₂.level_le (h₁.same.level.trans e) r₁.2
    exact ⟨Nat.max_le.mpr ⟨r₁.1, r₂.1⟩, r₂.2⟩

theorem ExtrudeParams.level_le : ExtrudeParams s c pol lvl P P' s' c' → s.level = L →
    CopiesLow L lvl c → P'.level L ≤ lvl ∧ CopiesLow L lvl c'
  | .nil, _, hc => ⟨Nat.zero_le _, hc⟩
  | .cons h₁ h₂, e, hc => by
    have r₁ := h₁.level_le e hc
    have r₂ := h₂.level_le (h₁.same.level.trans e) r₁.2
    exact ⟨Nat.max_le.mpr ⟨r₁.1, r₂.1⟩, r₂.2⟩

theorem ExtrudeEach.level_le : ExtrudeEach s c pol lvl ts ts' s' c' → s.level = L →
    CopiesLow L lvl c → (∀ t' ∈ ts', t'.level L ≤ lvl) ∧ CopiesLow L lvl c'
  | .nil, _, hc => ⟨(fun _ h => nomatch h), hc⟩
  | .cons h₁ h₂, e, hc => by
    have r₁ := h₁.level_le e hc
    have r₂ := h₂.level_le (h₁.same.level.trans e) r₁.2
    refine ⟨fun t' ht' => ?_, r₂.2⟩
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact r₁.1
    · exact r₂.1 t' ht'
end

/-! ## The shape of the result -/

/-- The same type constructor, among those extrusion rebuilds. -/
def SType.SameCon : SType → SType → Prop
  | .arrow _ _, .arrow _ _ | .record _ _, .record _ _ | .sig _, .sig _ | .var _, .var _ => True
  | _, _ => False

/-- An extruded type is the original, or a copy with the same
constructor. -/
theorem Extrude.con : Extrude s c pol lvl t t' s' c' → t' = t ∨ t.SameCon t'
  | .low _ => .inl rfl
  | .arrow .. | .record .. | .sig .. | .varCopied .. | .varPos .. | .varNeg .. => .inr trivial

theorem SType.SameCon.isPre : ∀ {t t' : SType}, t.SameCon t' → t.IsPre ∧ t'.IsPre
  | .arrow _ _, .arrow _ _, _ | .record _ _, .record _ _, _ | .sig _, .sig _, _
  | .var _, .var _, _ => ⟨trivial, trivial⟩

theorem SType.SameCon.nonvar : ∀ {t t' : SType}, t.SameCon t' → (∀ w, t ≠ .var w) →
    ∀ w, t' ≠ .var w
  | .arrow _ _, .arrow _ _, _, _ | .record _ _, .record _ _, _, _ | .sig _, .sig _, _, _ =>
    fun _ h => nomatch h
  | .var v, .var _, _, h => absurd rfl (h v)

theorem Extrude.ne_abs (h : Extrude s c pol lvl t t' s' c') (ht : t ≠ .abs) : t' ≠ .abs := by
  rcases h.con with rfl | hc
  · exact ht
  · exact hc.isPre.2.ne_abs

theorem Extrude.isPre (h : Extrude s c pol lvl t t' s' c') (ht : t.IsPre) : t'.IsPre := by
  rcases h.con with rfl | hc
  · exact ht
  · exact hc.isPre.2

/-- The copies of fields have their labels. -/
theorem ExtrudeFields.labels : ExtrudeFields s c pol lvl fs fs' s' c' → fs'.labels = fs.labels
  | .nil => rfl
  | .opt _ h => by simp [SFields.labels, h.labels]
  | .cons _ _ h => by simp [SFields.labels, h.labels]

/-! ## Variables of low level are not touched -/

theorem bounds_addUpper_ne {s : State} {v w : Nat} {t : SType} (h : w ≠ v) :
    (s.addUpper v t).bounds w = s.bounds w := by simp [State.addUpper, h]

theorem bounds_addLower_ne {s : State} {v w : Nat} {t : SType} (h : w ≠ v) :
    (s.addLower v t).bounds w = s.bounds w := by simp [State.addLower, h]

theorem bounds_addUppers_ne {s : State} {v w : Nat} {ts : List SType} (h : w ≠ v) :
    (s.addUppers v ts).bounds w = s.bounds w := by simp [State.addUppers, h]

theorem bounds_addLowers_ne {s : State} {v w : Nat} {ts : List SType} (h : w ≠ v) :
    (s.addLowers v ts).bounds w = s.bounds w := by simp [State.addLowers, h]

mutual
/-- Extrusion to `lvl` only adds bounds to the variables it copies, whose
level is above `lvl`, and to the copies, which are fresh. -/
theorem Extrude.frame : Extrude s c pol lvl t t' s' c' →
    ∀ w, w < s.next → s.level w ≤ lvl → s'.bounds w = s.bounds w
  | .low _, _, _, _ => rfl
  | .arrow _ h₁ h₂, w, hw, hl =>
    (h₂.frame w (Nat.lt_of_lt_of_le hw h₁.same.next) (h₁.same.level ▸ hl)).trans (h₁.frame w hw hl)
  | .record _ h₁ h₂, w, hw, hl =>
    (h₂.frame w (Nat.lt_of_lt_of_le hw h₁.same.next) (h₁.same.level ▸ hl)).trans (h₁.frame w hw hl)
  | .sig _ h, w, hw, hl => h.frame w hw hl
  | .varCopied _ _, _, _, _ => rfl
  | .varPos (s := s) (v := v) hv _ _ _ h, w, hw, hl => by
    have hwv : w ≠ v := fun e => absurd (e ▸ hl) (Nat.not_le.mpr hv)
    have := h.frame w (Nat.lt_succ_of_lt hw) hl
    show ((_ : State).addLowers s.next _).bounds w = _
    rw [bounds_addLowers_ne (Nat.ne_of_lt hw), this]
    exact bounds_addUpper_ne hwv
  | .varNeg (s := s) (v := v) hv _ _ _ h, w, hw, hl => by
    have hwv : w ≠ v := fun e => absurd (e ▸ hl) (Nat.not_le.mpr hv)
    have := h.frame w (Nat.lt_succ_of_lt hw) hl
    show ((_ : State).addUppers s.next _).bounds w = _
    rw [bounds_addUppers_ne (Nat.ne_of_lt hw), this]
    exact bounds_addLower_ne hwv

theorem ExtrudeFields.frame : ExtrudeFields s c pol lvl fs fs' s' c' →
    ∀ w, w < s.next → s.level w ≤ lvl → s'.bounds w = s.bounds w
  | .nil, _, _, _ => rfl
  | .opt h₁ h₂, w, hw, hl =>
    (h₂.frame w (Nat.lt_of_lt_of_le hw h₁.same.next) (h₁.same.level ▸ hl)).trans (h₁.frame w hw hl)
  | .cons _ h₁ h₂, w, hw, hl =>
    (h₂.frame w (Nat.lt_of_lt_of_le hw h₁.same.next) (h₁.same.level ▸ hl)).trans (h₁.frame w hw hl)

theorem ExtrudeParams.frame : ExtrudeParams s c pol lvl P P' s' c' →
    ∀ w, w < s.next → s.level w ≤ lvl → s'.bounds w = s.bounds w
  | .nil, _, _, _ => rfl
  | .cons h₁ h₂, w, hw, hl =>
    (h₂.frame w (Nat.lt_of_lt_of_le hw h₁.same.next) (h₁.same.level ▸ hl)).trans (h₁.frame w hw hl)

theorem ExtrudeEach.frame : ExtrudeEach s c pol lvl ts ts' s' c' →
    ∀ w, w < s.next → s.level w ≤ lvl → s'.bounds w = s.bounds w
  | .nil, _, _, _ => rfl
  | .cons h₁ h₂, w, hw, hl =>
    (h₂.frame w (Nat.lt_of_lt_of_le hw h₁.same.next) (h₁.same.level ▸ hl)).trans (h₁.frame w hw hl)
end

end BoltCore.Alg
