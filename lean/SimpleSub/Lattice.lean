import SimpleSub.Sub

/-!
# The MLsub lattice equations: where the current rules stop

The OCaml implementation relies on five equations that the rules of
`Sub.lean` derive in one direction only:

1. `(a→b) ∧ (c→d) ≤ (a∨c) → (b∧d)` (merging intersections of functions)
2. `(a∧c) → (b∨d) ≤ (a→b) ∨ (c→d)` (merging unions of functions)
3. `{x: a} ∧ {y: b} ≤ {x: a, y: b}` (merging intersections of records)
4. `{x: a∨c} ≤ {x: a, y: b} ∨ {x: c}` (merging unions of records)
5. `{fs | t₁ ∨ t₂} ≤ {fs | t₁} ∨ {fs | t₂}` (rows over tail unions; an
   instance of 4 since rows are compared fieldwise)

`not_fun_merge` proves that the first one is genuinely missing. Distributivity
(`(a ∨ b) ∧ c ≤ (a ∧ c) ∨ (b ∧ c)`) is missing for the same reason, though
this is not proved here: the left rules for `∧` and the right rules for
`∨` each pick a single component, so nothing can combine information from
two of them.

## Plan: sequent-style rules

Adding the equations as binary rules does not survive cut elimination:
composing `(a→b) ∧ (c→d) ≤ e→f` with `e→f ≤ (g₁→h₁) ∨ (g₂→h₂)` needs a
judgement "meet of arrows ≤ join of arrows". The cut-closed formulation
works on judgements `⋀Γ ≤ ⋁Δ` over lists of types:

* invertible rules: flatten `∧` on the left and `∨` on the right; split
  `∨` on the left and `∧` on the right (distributivity); unfold `μ` on
  either side; `⊤`/`⊥` neutral or absorbing;
* atomic rules, which are the only ones using the coinductive hypothesis:
  a shared atom (`prim`, `fvar`, `proj`); arrows `As ⊆ Γ`, `Bs ⊆ Δ`
  merged as `⋀Bs.params ≤ ⋁As.params` and `⋀As.results ≤ ⋁Bs.results`;
  records `Rs ⊆ Γ`, `Ss ⊆ Δ` compared fieldwise as
  `field l (⋀Rs) ≤ field l (⋁Ss)` for every label.

This mirrors `lib/subsume.ml` (flatten, distribute rows, merge, then pick
atoms). Transitivity becomes cut admissibility for a positive sequent
calculus (as for the `∧`/`∨` fragment of LK); the new obligation is that
the coinductive hypothesis must be closed under lattice reasoning, since
the guarded premises of a cut combine big meets and joins of parameter and
result types.
-/

namespace SimpleSub

section Gap

variable {E : Defs}

private def P : Ty := .prim "p"
private def Q : Ty := .prim "q"
private def R' : Ty := .prim "r"
private def S : Ty := .prim "s"

/-- Different primitive types are unrelated, at any layer. -/
private theorem step_prim_prim {R : Ty → Ty → Prop} {a b : String} (h : a ≠ b) :
    ¬ Step E R (.prim a) (.prim b) := by
  intro hs
  cases hs
  exact h rfl

/-- **Gap 1**: `(p→q) ∧ (r→s) ≤ (p∨r) → (q∧s)` is not derivable with the
current rules, although MLsub (and the simplifier) treat both sides as
equal. -/
theorem not_fun_merge :
    ¬ Sub E (.inter (.arrow P Q) (.arrow R' S)) (.arrow (.union P R') (.inter Q S)) := by
  rintro ⟨R, hR, h⟩
  cases hR _ _ h with
  | interL₁ h₁ =>
    cases h₁ with
    | arrow hp _ =>
      cases hR _ _ hp with
      | unionL _ h₂ => exact step_prim_prim (by decide) h₂
  | interL₂ h₁ =>
    cases h₁ with
    | arrow hp _ =>
      cases hR _ _ hp with
      | unionL h₂ _ => exact step_prim_prim (by decide) h₂

end Gap

end SimpleSub
