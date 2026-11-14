import SimpleSub.SolutionRows
import SimpleSub.Typing

/-!
# Theorem 1: soundness of type inference

If the algorithm types a term, the term has the inferred type, translated
through the solution, in the declarative type system (`Typ`, over `Sub`).
This is the paper's Theorem 1 for our model (monomorphic `let`, rows, and
the contractive and `Abs` conventions of the previous files).

The solution is the one for the *final* state: every constraint accepted
along the way is still logged there (the log only grows), so
`solution_rows` relates all of them at once. Each `constrain` the
algorithm performed becomes a subsumption step; the side condition that
its left side is not `Abs` holds because it is always the inferred type of
a subterm (`TypeTerm.nac`).
-/

namespace SimpleSub.Alg

open State

/-! ## Contexts and logs -/

/-- The algorithm's (monomorphic) context as a declarative one. -/
def SCtx.toCtx (Γ : SCtx) : Ctx := Γ.map fun p => (p.1, Scheme.mono p.2.toTy)

theorem SCtx.lookup_toCtx : ∀ {Γ : SCtx} {x : String} {st : SType},
    Γ.lookup x = some st → Γ.toCtx.lookup x = some (.mono st.toTy)
  | [], _, _, h => by simp [SCtx.lookup] at h
  | (y, t) :: Γ, x, st, h => by
    simp only [SCtx.lookup, List.find?_cons] at h
    simp only [SCtx.toCtx, List.map_cons, Ctx.lookup, List.find?_cons]
    by_cases hy : y = x
    · simp only [hy, decide_true] at h ⊢
      simp at h
      subst h
      rfl
    · simp only [hy, decide_false] at h ⊢
      have := SCtx.lookup_toCtx (Γ := Γ) h
      simpa [SCtx.toCtx, Ctx.lookup] using this

theorem SFields.toFields_absOf : ∀ F : SFields, F.absOf.toFields = F.toFields.absOf
  | .nil => rfl
  | .cons _ _ F => by
    simp only [SFields.absOf, SFields.toFields, Fields.absOf, SType.toTy]
    rw [SFields.toFields_absOf F]

/-- A top-level `constrain` call accepts its constraint (no invariant needed). -/
theorem ConstrainTop.logged {s s' : State} (h : ConstrainTop s a b s') : Logged s' a b := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact (hc.logged fun _ h => nomatch h).2

theorem ConstrainTop.log_grows {s s' : State} (h : ConstrainTop s a b s') :
    ∀ p, p ∈ s.log → p ∈ s'.log := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact hc.grows.log

mutual
theorem TypeTerm.log_grows : TypeTerm Γ s t st s' → ∀ p, p ∈ s.log → p ∈ s'.log
  | .lit => fun _ h => h
  | .var _ => fun _ h => h
  | .lam h => h.log_grows
  | .app h₁ h₂ hc => fun p hp => hc.log_grows p (h₂.log_grows p (h₁.log_grows p hp))
  | .rcd h => h.log_grows
  | .sel h hc => fun p hp => hc.log_grows p (h.log_grows p hp)
  | .ext h₁ h₂ hc => fun p hp => hc.log_grows p (h₂.log_grows p (h₁.log_grows p hp))
  | .letIn h₁ h₂ => fun p hp => h₂.log_grows p (h₁.log_grows p hp)
  | .letRec h₁ hc h₂ => fun p hp => h₂.log_grows p (hc.log_grows p (h₁.log_grows p hp))

theorem TypeFields.log_grows : TypeFields Γ s fs F s' → ∀ p, p ∈ s.log → p ∈ s'.log
  | .nil => fun _ h => h
  | .cons h₁ h₂ => fun p hp => h₂.log_grows p (h₁.log_grows p hp)
end

/-! ## The theorem -/

/-- What the final state provides: the invariants the solution theorem
needs. -/
structure Final (sf : State) (rank : Nat → Nat) : Prop where
  inv : Inv sf
  inv₂ : Inv₂ sf
  nac : LogNAC sf
  ranked : TailRanked sf rank

theorem Logged.of_log {s s' : State} (hlog : ∀ p, p ∈ s.log → p ∈ s'.log) :
    Logged s a b → Logged s' a b
  | .inl h => .inl h
  | .inr h => .inr (hlog _ h)

/-- An accepted constraint whose left side is an inferred type (so not
`Abs`) holds of the final solution. -/
theorem Final.sub {s sf : State} {rank : Nat → Nat} (hf : Final sf rank)
    (hl : Logged s a b) (hlog : ∀ p, p ∈ s.log → p ∈ sf.log) (ha : a ≠ .abs) :
    Sub (defsOf sf) a.toTy b.toTy :=
  solution_rows hf.inv hf.inv₂ hf.nac hf.ranked (hl.of_log hlog) (.inl ha)

mutual
/-- **Theorem 1** (soundness of inference): if the algorithm types `t` with
`st`, starting from a state and context satisfying the invariants, then `t`
has type `θ(st)` in the declarative system, for the solution `θ` of any
later state `sf` (in particular the final one). -/
theorem TypeTerm.sound {rank : Nat → Nat} {sf : State} (hf : Final sf rank) :
    TypeTerm Γ s t st s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ sf.log) → Typ (defsOf sf) Γ.toCtx t st.toTy
  | .lit, _, _, _, _ => .lit
  | .var hx, _, _, _, _ => Typ.var_mono (SCtx.lookup_toCtx hx)
  | .lam h, hΓ, i, n, hlog =>
    .lam (h.sound hf (hΓ.cons trivial (fun h => nomatch h)) i.fresh n hlog)
  | .app h₁ h₂ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i.fresh
    have r₁ := h₁.nac hΓ i.fresh n
    have r₂ := h₂.nac hΓ i₁ r₁.1
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .app (.sub (h₁.sound hf hΓ i.fresh n hlog₁) (hf.sub hc.logged hlog r₁.2.2))
      (h₂.sound hf hΓ i₁ r₁.1 hlog₂)
  | .rcd h, hΓ, i, n, hlog => .rcd (h.sound hf hΓ i n hlog)
  | .sel h hc, hΓ, i, n, hlog => by
    have r := h.nac hΓ i.fresh n
    exact .sel (.sub (h.sound hf hΓ i.fresh n fun p hp => hlog p (hc.log_grows p hp))
      (hf.sub hc.logged hlog r.2.2))
  | .ext h₁ h₂ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i
    have r₁ := h₁.nac hΓ i n
    have r₂ := h₂.nac hΓ i₁ r₁.1
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    have hs := hf.sub hc.logged hlog r₁.2.2
    simp only [SType.toTy, SFields.toFields_absOf] at hs
    exact .ext (.sub (h₁.sound hf hΓ i n hlog₁) hs) (h₂.sound hf hΓ i₁ r₁.1 hlog₂)
  | .letIn h₁ h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac hΓ i n
    exact .letIn (h₁.sound hf hΓ i n fun p hp => hlog p (h₂.log_grows p hp))
      (h₂.sound hf (hΓ.cons r₁.2.1 r₁.2.2) (h₁.inv₂ i) r₁.1 hlog)
  | .letRec h₁ hc h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac (hΓ.cons trivial (fun h => nomatch h)) i.fresh n
    have i₁ := h₁.inv₂ i.fresh
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (h₂.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact .letRec
      (.sub (h₁.sound hf (hΓ.cons trivial (fun h => nomatch h)) i.fresh n hlog₁)
        (hf.sub hc.logged hlog₂ r₁.2.2))
      (h₂.sound hf (hΓ.cons trivial (fun h => nomatch h)) (hc.inv₂ i₁)
        (hc.nac i₁ r₁.2.1 trivial r₁.1) hlog)

theorem TypeFields.sound {rank : Nat → Nat} {sf : State} (hf : Final sf rank) :
    TypeFields Γ s fs F s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ sf.log) → TypFields (defsOf sf) Γ.toCtx fs F.toFields
  | .nil, _, _, _, _ => .nil
  | .cons h₁ h₂, hΓ, i, n, hlog =>
    have r₁ := h₁.nac hΓ i n
    .cons (h₁.sound hf hΓ i n fun p hp => hlog p (h₂.log_grows p hp))
      (h₂.sound hf hΓ (h₁.inv₂ i) r₁.1 hlog)
end

/-- **Theorem 1, from scratch**: if the algorithm types `t` with `st` in the
built-in context, ending in state `s'`, and the row-variable tails of `s'`
are acyclic, then `t : θ(st)` in the declarative system, where `θ` is the
solution of `s'`. -/
theorem soundness {rank : Nat → Nat} (h : TypeTerm builtins State.init t st s')
    (hr : TailRanked s' rank) : Typ (defsOf s') builtins.toCtx t st.toTy := by
  have hn := h.nac builtins_NAC Inv₂.init LogNAC.init
  exact h.sound ⟨h.inv_init, h.inv₂ Inv₂.init, hn.1, hr⟩ builtins_NAC Inv₂.init LogNAC.init
    fun _ hp => hp

end SimpleSub.Alg
