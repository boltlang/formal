import BoltCore.Sorted.Sub

/-!
# The MLsub lattice equations, sorted

As in `Lattice.lean`: the minimal rules do not derive the equations the
simplifier relies on. Sorting adds one more: `pre τ₁ ∪ pre τ₂ ≤ pre (τ₁ ∪ τ₂)`
holds, but `pre (τ₁ ∪ τ₂) ≤ pre τ₁ ∪ pre τ₂` does not (`not_pre_union`),
so merging the fields of two rows needs the equations too.
-/

namespace BoltCore.Sorted

section Gap

variable {E : Defs}

private def P : Ty .ty := .prim "p"
private def Q : Ty .ty := .prim "q"
private def R' : Ty .ty := .prim "r"
private def S : Ty .ty := .prim "s"

private theorem step_prim_prim {R : Rel} {a b : String} (h : a ≠ b) :
    ¬ Step E R (.prim a) (.prim b) := by
  intro hs
  cases hs
  exact h rfl

/-- `(p→q) ∧ (r→s) ≤ (p∨r) → (q∧s)` is not derivable. -/
theorem not_fun_merge :
    ¬ Sub E (.inter (.arrow P Q) (.arrow R' S)) (.arrow (.union P R') (.inter Q S)) := by
  rintro ⟨R, hR, h⟩
  cases hR _ _ _ h with
  | interL₁ h₁ =>
    cases h₁ with
    | arrow hp _ =>
      cases hR _ _ _ hp with
      | unionL _ h₂ => exact step_prim_prim (by decide) h₂
  | interL₂ h₁ =>
    cases h₁ with
    | arrow hp _ =>
      cases hR _ _ _ hp with
      | unionL h₂ _ => exact step_prim_prim (by decide) h₂

theorem pre_union_le {τ₁ τ₂ : Ty .ty} : Sub E (.union (.pre τ₁) (.pre τ₂)) (.pre (.union τ₁ τ₂)) :=
  Sub.of_step (.unionL (.pre (.unionR₁ Sub.refl.step)) (.pre (.unionR₂ Sub.refl.step)))

/-- `pre (p ∪ q) ≤ pre p ∪ pre q` is not derivable. -/
theorem not_pre_union : ¬ Sub E (.pre (.union P Q)) (.union (.pre P) (.pre Q)) := by
  intro h
  cases h.step with
  | unionR₁ h₁ => cases h₁ with | pre h₂ => cases h₂ with | unionL _ h₃ => exact step_prim_prim (by decide) h₃
  | unionR₂ h₁ => cases h₁ with | pre h₂ => cases h₂ with | unionL h₃ _ => exact step_prim_prim (by decide) h₃

end Gap

end BoltCore.Sorted
