import BoltCore.Rename

/-!
# Levels

A bound of a variable has at most the variable's level (`LevelInv`).
Constraining keeps this: a bound is only installed when its level is low
enough, and otherwise its extrusion to the variable's level is. So a
variable of level at most `lvl` only reaches variables of level at most
`lvl`, which is what makes generalizing the others sound.
-/

namespace BoltCore.Alg

open State

/-- A bound of a variable has at most its level. -/
def LevelInv (s : State) : Prop :=
  ∀ v b, (b ∈ (s.bounds v).upper ∨ b ∈ (s.bounds v).lower) → b.level s.level ≤ s.level v

theorem LevelInv.addUpper {s : State} {v : Nat} {t : SType} (h : LevelInv s)
    (ht : t.level s.level ≤ s.level v) : LevelInv (s.addUpper v t) := by
  intro w b hb
  rcases hb with hb | hb
  · rcases mem_upper_addUpper_inv hb with ⟨rfl, rfl⟩ | hb
    · exact ht
    · exact h w b (.inl hb)
  · rw [lower_addUpper] at hb; exact h w b (.inr hb)

theorem LevelInv.addLower {s : State} {v : Nat} {t : SType} (h : LevelInv s)
    (ht : t.level s.level ≤ s.level v) : LevelInv (s.addLower v t) := by
  intro w b hb
  rcases hb with hb | hb
  · rw [upper_addLower] at hb; exact h w b (.inl hb)
  · rcases mem_lower_addLower_inv hb with ⟨rfl, rfl⟩ | hb
    · exact ht
    · exact h w b (.inr hb)

theorem LevelInv.addLowers {s : State} {v : Nat} {ts : List SType} (h : LevelInv s)
    (ht : ∀ t ∈ ts, t.level s.level ≤ s.level v) : LevelInv (s.addLowers v ts) := by
  intro w b hb
  by_cases e : w = v
  · subst e
    simp only [State.addLowers, ite_true, List.mem_append] at hb
    rcases hb with hb | hb | hb
    · exact h w b (.inl hb)
    · exact ht b hb
    · exact h w b (.inr hb)
  · rw [bounds_addLowers_ne e] at hb; exact h w b hb

theorem LevelInv.addUppers {s : State} {v : Nat} {ts : List SType} (h : LevelInv s)
    (ht : ∀ t ∈ ts, t.level s.level ≤ s.level v) : LevelInv (s.addUppers v ts) := by
  intro w b hb
  by_cases e : w = v
  · subst e
    simp only [State.addUppers, ite_true, List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · exact ht b hb
    · exact h w b (.inl hb)
    · exact h w b (.inr hb)
  · rw [bounds_addUppers_ne e] at hb; exact h w b hb

mutual
/-- Extrusion keeps the levels of bounds: a copy is below the level of its
original, and its bounds are extruded to its level. -/
theorem Extrude.levels : Extrude s c pol lvl t t' s' c' → s.level = L → CopiesLow L lvl c →
    LevelInv s → LevelInv s'
  | .low _, _, _, h => h
  | .arrow _ h₁ h₂, e, hc, h =>
    h₂.levels (h₁.same.level.trans e) (h₁.level_le e hc).2 (h₁.levels e hc h)
  | .record _ h₁ h₂, e, hc, h =>
    h₂.levels (h₁.same.level.trans e) (h₁.level_le e hc).2 (h₁.levels e hc h)
  | .sig _ h', e, hc, h => h'.levels e hc h
  | .varCopied _ _, _, _, h => h
  | .varPos (s := s) (v := v) hv _ hl _ h', e, hc, h => by
    have hn : L s.next ≤ lvl := e ▸ Nat.le_of_eq hl
    have h₀ : LevelInv ((s.fresh.addUpper v (.var s.next)).logAll [(.var v, .var s.next)]) :=
      LevelInv.addUpper (s := s.fresh) h (by
        show s.level s.next ≤ s.level v
        rw [hl]; exact Nat.le_of_lt hv)
    have r := h'.levels e (hc.cons hn) h₀
    have hls := (h'.level_le e (hc.cons hn)).1
    have el := h'.same.level
    exact LevelInv.addLowers r fun t ht => by
      rw [el]
      show t.level s.level ≤ s.level s.next
      rw [hl, e]; exact hls t ht
  | .varNeg (s := s) (v := v) hv _ hl _ h', e, hc, h => by
    have hn : L s.next ≤ lvl := e ▸ Nat.le_of_eq hl
    have h₀ : LevelInv ((s.fresh.addLower v (.var s.next)).logAll [(.var s.next, .var v)]) :=
      LevelInv.addLower (s := s.fresh) h (by
        show s.level s.next ≤ s.level v
        rw [hl]; exact Nat.le_of_lt hv)
    have r := h'.levels e (hc.cons hn) h₀
    have hus := (h'.level_le e (hc.cons hn)).1
    have el := h'.same.level
    exact LevelInv.addUppers r fun t ht => by
      rw [el]
      show t.level s.level ≤ s.level s.next
      rw [hl, e]; exact hus t ht

theorem ExtrudeFields.levels : ExtrudeFields s c pol lvl fs fs' s' c' → s.level = L →
    CopiesLow L lvl c → LevelInv s → LevelInv s'
  | .nil, _, _, h => h
  | .opt h₁ h₂, e, hc, h =>
    h₂.levels (h₁.same.level.trans e) (h₁.level_le e hc).2 (h₁.levels e hc h)
  | .cons _ h₁ h₂, e, hc, h =>
    h₂.levels (h₁.same.level.trans e) (h₁.level_le e hc).2 (h₁.levels e hc h)

theorem ExtrudeParams.levels : ExtrudeParams s c pol lvl P P' s' c' → s.level = L →
    CopiesLow L lvl c → LevelInv s → LevelInv s'
  | .nil, _, _, h => h
  | .cons h₁ h₂, e, hc, h =>
    h₂.levels (h₁.same.level.trans e) (h₁.level_le e hc).2 (h₁.levels e hc h)

theorem ExtrudeEach.levels : ExtrudeEach s c pol lvl ts ts' s' c' → s.level = L →
    CopiesLow L lvl c → LevelInv s → LevelInv s'
  | .nil, _, _, h => h
  | .cons h₁ h₂, e, hc, h =>
    h₂.levels (h₁.same.level.trans e) (h₁.level_le e hc).2 (h₁.levels e hc h)
end

mutual
/-- **Constraining keeps the levels of bounds.** -/
theorem Constrain.levels : Constrain s a b s' → LevelInv s → LevelInv s'
  | .cached _, h | .refl, h | .absR _, h => h
  | .arrow _ h₁ h₂, h | .absRecord _ h₁ h₂, h | .nilRecord _ h₁ h₂, h
  | .recordNil _ _ h₁ h₂, h => h₂.levels (h₁.levels h)
  | .record _ _ _ h₁ h₂ h₃, h => h₃.levels (h₂.levels (h₁.levels h))
  | .varL (s := s) (v := v) (b := b) _ _ hlv h', h =>
    h'.levels (LevelInv.addUpper (s := s.remember (.var v) b) h hlv)
  | .varR (s := s) (v := v) (a := a) _ _ hlv h', h =>
    h'.levels (LevelInv.addLower (s := s.remember a (.var v)) h hlv)
  | .extLHit _ _ _ hx _, h | .extRHit _ _ _ hx _, h => hx.levels rfl .nil h
  | .extLNew (s₁ := s₁) (v := v) (b' := b') _ _ _ hx _ h', h =>
    h'.levels (LevelInv.addUpper (s := s₁.remember (.var v) b') (hx.levels rfl .nil h) (by
      show b'.level s₁.level ≤ s₁.level v
      rw [hx.same.level]; exact (hx.level_le rfl .nil).1))
  | .extRNew (s₁ := s₁) (v := v) (a' := a') _ _ _ hx _ h', h =>
    h'.levels (LevelInv.addLower (s := s₁.remember a' (.var v)) (hx.levels rfl .nil h) (by
      show a'.level s₁.level ≤ s₁.level v
      rw [hx.same.level]; exact (hx.level_le rfl .nil).1))
  | .recordSig _ _ _ _ _ h', h | .sigL _ _ h', h => h'.levels h

theorem ConstrainEach.levels : ConstrainEach s ps s' → LevelInv s → LevelInv s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.levels (h₁.levels h)

theorem ConstrainField.levels : ConstrainField s a b s' → LevelInv s → LevelInv s'
  | .toAbs, h | .misMis, h | .misOpt, h => h
  | .optOpt _ h', h | .preOpt _ h', h | .pre _ _ h', h => h'.levels h

theorem FieldsEach.levels : FieldsEach s ps s' → LevelInv s → LevelInv s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.levels (h₁.levels h)

theorem Expand.levels : Expand s t ms t' s' → LevelInv s → LevelInv s'
  | .none, h => h
  | .abs _ h', h | .nil _ h', h | .allAbsent _ _ h', h => h'.levels h
  | .memo _ _ h₁ _ h₂, h => h₂.levels (h₁.levels h)
  | .fresh _ _ h₁ _ _ _ h₂, h => h₂.levels (h₁.levels h)
end

theorem ConstrainTop.levels {s s' : State} {a b : SType} (h : ConstrainTop s a b s')
    (hl : LevelInv s) : LevelInv s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact hc.levels hl

end BoltCore.Alg
