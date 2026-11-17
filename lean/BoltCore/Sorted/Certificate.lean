import BoltCore.Sorted.PolyLet

/-!
# Adequacy, sorted (step 3)

Every accepted run of the algorithm model yields a valid certificate and a
polymorphic skeleton (`SPTyp`) for its term (`TypeTerm.scertificate`), so
the sorted checker never rejects a correct run of the model. The model has
no let-polymorphism: its `let` becomes a generalization of no variables,
and a use of a `let`-bound name an instantiation by the identity. So the
skeleton's context relates to the algorithm's entry by entry (`PRel`): a
plain entry, or a scheme with no generalized variables.

With `SPTyp.sound_top`, this gives Theorem 1 through certificates, in the
sorted system (`stheorem1_cert`).
-/

namespace BoltCore.Alg

open State

/-- The skeleton's context against the algorithm's: each entry is the same
type, plainly or as a scheme with no generalized variables. -/
inductive PRel : SCtx → PCtx → Prop where
  | nil : PRel [] []
  | mono : PRel Γ Δ → PRel ((x, st) :: Γ) ((x, .mono st) :: Δ)
  | poly : PRel Γ Δ → PRel ((x, st) :: Γ) ((x, .poly [] st) :: Δ)

theorem PRel.lookup : ∀ {Γ : SCtx} {Δ : PCtx}, PRel Γ Δ → ∀ {x : String} {st : SType},
    Γ.lookup x = some st → Δ.lookup x = some (.mono st) ∨ Δ.lookup x = some (.poly [] st)
  | _, _, .nil, _, _, h => by simp [SCtx.lookup] at h
  | _, _, .mono (x := y) (st := t) r, x, st, h
  | _, _, .poly (x := y) (st := t) r, x, st, h => by
    simp only [SCtx.lookup, List.find?_cons] at h
    simp only [PCtx.lookup, List.find?_cons]
    by_cases hy : y = x
    · simp only [hy, decide_true] at h ⊢
      simp at h; subst h; simp
    · simp only [hy, decide_false] at h ⊢
      exact r.lookup h

/-- Nothing mentions the empty list of variables: generalizing none is
always allowed. -/
theorem GenOK.nil (c : Certificate) (Δ : PCtx) : GenOK c Δ [] :=
  ⟨fun _ _ _ _ _ _ h => (nomatch h), fun p _ => by
    cases p.2 with
    | mono => exact fun _ _ h => (nomatch h)
    | poly => exact fun _ _ _ h => (nomatch h)⟩

theorem SInstOK.nil (c : Certificate) : SInstOK c [] id :=
  ⟨fun _ _ => rfl, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem SPTyp.of_lookup {c : Certificate} {Γ : SCtx} {Δ : PCtx} (r : PRel Γ Δ) {x : String}
    {st : SType} (h : Γ.lookup x = some st) : SPTyp c Δ (.var x) st := by
  rcases r.lookup h with h | h
  · exact .var h
  · have := SPTyp.inst (c := c) h (SInstOK.nil c)
    rwa [SType.rename_id] at this

mutual
/-- A run of the algorithm gives a sorted typing skeleton, checked against
any certificate that accepts the constraints it logged. -/
theorem TypeTerm.sskeleton {c : Certificate} {Δ : PCtx} (r : PRel Γ Δ) :
    TypeTerm Γ s t st s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ c.log) → SPTyp c Δ t st
  | .lit, _, _, _, _ => .lit
  | .var hx, _, _, _, _ => SPTyp.of_lookup r hx
  | .lam _ h, hΓ, i, n, hlog =>
    .lam (h.sskeleton r.mono (hΓ.cons trivial (fun h => nomatch h)) i.fresh n hlog)
  | .app _ h₁ h₂ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i.fresh
    have r₁ := h₁.nac hΓ i.fresh n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .app (h₁.sskeleton r hΓ i.fresh n hlog₁) (h₂.sskeleton r hΓ i₁ r₁.1 hlog₂) r₁.2.2
      (hc.logged.accepts hlog)
  | .rcd h, hΓ, i, n, hlog => .rcd (h.sskeleton r hΓ i n hlog)
  | .sel _ h hc, hΓ, i, n, hlog => by
    have r' := h.nac hΓ i.fresh n
    exact .sel (h.sskeleton r hΓ i.fresh n (fun p hp => hlog p (hc.log_grows p hp))) r'.2.2
      (hc.logged.accepts hlog) (fun h => nomatch h)
  | .extNil h, hΓ, i, n, hlog => .extNil (h.sskeleton r hΓ i n hlog)
  | .ext _ h₁ h₂ _ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i
    have r₁ := h₁.nac hΓ i n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .ext (h₁.sskeleton r hΓ i n hlog₁) (h₂.sskeleton r hΓ i₁ r₁.1 hlog₂) r₁.2.2
      (hc.logged.accepts hlog)
  | .letIn h₁ h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac hΓ i n
    exact .letIn (h₁.sskeleton r hΓ i n (fun p hp => hlog p (h₂.log_grows p hp))) (GenOK.nil c Δ)
      (h₂.sskeleton r.poly (hΓ.cons r₁.2.1 r₁.2.2) (h₁.inv₂ i) r₁.1 hlog)
  | .letRec hf _ h₁ hc h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac (hΓ.cons trivial (fun h => nomatch h)) i.fresh n
    have i₁ := h₁.inv₂ i.fresh
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (h₂.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact .letRec hf (h₁.sskeleton r.mono (hΓ.cons trivial (fun h => nomatch h)) i.fresh n hlog₁)
      r₁.2.2 (hc.logged.accepts hlog₂) (GenOK.nil c Δ)
      (h₂.sskeleton r.poly (hΓ.cons trivial (fun h => nomatch h)) (hc.inv₂ i₁)
        (hc.nac i₁ r₁.2.1 trivial r₁.1) hlog)

theorem TypeFields.sskeleton {c : Certificate} {Δ : PCtx} (r : PRel Γ Δ) :
    TypeFields Γ s fs F s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ c.log) → SPFields c Δ fs F
  | .nil, _, _, _, _ => .nil
  | .cons h₁ h₂, hΓ, i, n, hlog =>
    have r₁ := h₁.nac hΓ i n
    .cons (h₁.sskeleton r hΓ i n (fun p hp => hlog p (h₂.log_grows p hp))) r₁.2.2
      (h₂.sskeleton r hΓ (h₁.inv₂ i) r₁.1 hlog)
end

/-- The built-ins as a skeleton context. -/
def pbuiltinsMono : PCtx := builtins.map fun p => (p.1, .mono p.2)

theorem PRel.builtins : PRel builtins pbuiltinsMono :=
  .mono (.mono (.mono (.mono (.mono .nil))))

/-- **Adequacy, sorted**: an accepted run yields a valid certificate, with a
sorted typing skeleton for the term at the inferred type. -/
theorem TypeTerm.scertificate (h : TypeTerm builtins (State.initK K) t st s')
    (hr : StructRanked s'.bounds r) :
    (s'.certificate r).Valid ∧ SPTyp (s'.certificate r) pbuiltinsMono t st :=
  ⟨(h.certificate hr).1,
    h.sskeleton PRel.builtins builtins_NAC Inv₂.init LogNAC.init (fun _ hp => hp)⟩

/-- Theorem 1 again, through certificates, sorted: an accepted run has a
valid certificate whose skeleton gives the sorted declarative typing, over a
solution without recursive types. -/
theorem stheorem1_cert (h : Infers K t st s') :
    ∃ c : Certificate,
      Sorted.Typ (sdefsOf c.state) (pbuiltinsMono.toSCtx c.bounds .gv) t st.sTy ∧
        ∃ r, Sorted.Defs.Ranked (sdefsOf c.state) r := by
  obtain ⟨h, r, hr⟩ := h
  have hc := h.scertificate hr
  exact ⟨_, SPTyp.sound_top hc.1 hc.2, _, hc.1.snonrec⟩

end BoltCore.Alg
