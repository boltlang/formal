import BoltCore.PolyLet

/-!
# Adequacy

Every accepted run of the algorithm model yields a valid certificate and a
polymorphic skeleton (`PTyp`) for its term (`TypeTerm.certificate`), so
the checker never rejects a correct run of the model. The model has
no let-polymorphism: its `let` becomes a generalization of no variables,
and a use of a `let`-bound name an instantiation by the identity. So the
skeleton's context relates to the algorithm's entry by entry (`PRel`): a
plain entry, or a scheme with no generalized variables.

With `PTyp.sound_top`, this gives Theorem 1 through certificates
(`theorem1_cert`).
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

theorem InstOK.nil (c : Certificate) : InstOK c [] id :=
  ⟨fun _ _ => rfl, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem PTyp.of_lookup {c : Certificate} {Γ : SCtx} {Δ : PCtx} (r : PRel Γ Δ) {x : String}
    {st : SType} (h : Γ.lookup x = some st) : PTyp c Δ (.var x) st := by
  rcases r.lookup h with h | h
  · exact .var h
  · have := PTyp.inst (c := c) h (InstOK.nil c)
    rwa [SType.rename_id] at this

mutual
/-- A run of the algorithm gives a typing skeleton, checked against
any certificate that accepts the constraints it logged. -/
theorem TypeTerm.skeleton {c : Certificate} {Δ : PCtx} (r : PRel Γ Δ) :
    TypeTerm Γ s t st s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ c.log) → PTyp c Δ t st
  | .lit, _, _, _, _ => .lit
  | .var hx, _, _, _, _ => PTyp.of_lookup r hx
  | .lam _ h, hΓ, i, n, hlog =>
    .lam (h.skeleton r.mono (hΓ.cons trivial trivial) i.fresh n hlog)
  | .app _ h₁ h₂ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i.fresh
    have r₁ := h₁.nac hΓ i.fresh n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .app (h₁.skeleton r hΓ i.fresh n hlog₁) (h₂.skeleton r hΓ i₁ r₁.1 hlog₂) r₁.2.2.ne_abs
      (hc.logged.accepts hlog)
  | .rcd h, hΓ, i, n, hlog => .rcd (h.skeleton r hΓ i n hlog)
  | .sel _ h hc, hΓ, i, n, hlog => by
    have r' := h.nac hΓ i.fresh n
    exact .sel (h.skeleton r hΓ i.fresh n (fun p hp => hlog p (hc.log_grows p hp))) r'.2.2.ne_abs
      (hc.logged.accepts hlog) trivial
  | .ite _ hc h₁ ha h₂ hb h₃, hΓ, i, n, hlog => by
    have rc := hc.nac hΓ i.fresh n
    have i₁ := hc.inv₂ i.fresh
    have n₁ := h₁.nac i₁ rc.2.1 trivial rc.1
    have i₂ := h₁.inv₂ i₁
    have ra := ha.nac hΓ i₂ n₁
    have i₃ := ha.inv₂ i₂
    have n₂ := h₂.nac i₃ ra.2.1 trivial ra.1
    have i₄ := h₂.inv₂ i₃
    have rb := hb.nac hΓ i₄ n₂
    have hlog₅ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (h₃.log_grows p hp)
    have hlog₄ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₅ p (hb.log_grows p hp)
    have hlog₃ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₄ p (h₂.log_grows p hp)
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₃ p (ha.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (h₁.log_grows p hp)
    exact .ite (hc.skeleton r hΓ i.fresh n hlog₁) rc.2.2.ne_abs (h₁.logged.accepts hlog₂)
      (ha.skeleton r hΓ i₂ n₁ hlog₃) ra.2.2.ne_abs (h₂.logged.accepts hlog₄)
      (hb.skeleton r hΓ i₄ n₂ hlog₅) rb.2.2.ne_abs (h₃.logged.accepts hlog)
  | .selOr _ h hc hd hc', hΓ, i, n, hlog => by
    have r' := h.nac hΓ i.fresh n
    have i₁ := h.inv₂ i.fresh
    have n₂ := hc.nac i₁ r'.2.1 ⟨⟨trivial, trivial⟩, trivial⟩ r'.1
    have i₂ := hc.inv₂ i₁
    have rd := hd.nac hΓ i₂ n₂
    have hlog₃ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (hc'.log_grows p hp)
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₃ p (hd.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact .selOr (h.skeleton r hΓ i.fresh n hlog₁) r'.2.2.ne_abs (hc.logged.accepts hlog₂)
      (hd.skeleton r hΓ i₂ n₂ hlog₃) rd.2.2.ne_abs (hc'.logged.accepts hlog)
  | .extNil h, hΓ, i, n, hlog => .extNil (h.skeleton r hΓ i n hlog)
  | .ext _ h₁ h₂ _ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i
    have r₁ := h₁.nac hΓ i n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .ext (h₁.skeleton r hΓ i n hlog₁) (h₂.skeleton r hΓ i₁ r₁.1 hlog₂) r₁.2.2.ne_abs
      (hc.logged.accepts hlog)
  | .letIn h₁ h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac hΓ i n
    exact .letIn (h₁.skeleton r hΓ i n (fun p hp => hlog p (h₂.log_grows p hp))) (GenOK.nil c Δ)
      (h₂.skeleton r.poly (hΓ.cons r₁.2.1 r₁.2.2) (h₁.inv₂ i) r₁.1 hlog)
  | .letRec hf _ h₁ hc h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac (hΓ.cons trivial trivial) i.fresh n
    have i₁ := h₁.inv₂ i.fresh
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (h₂.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact .letRec hf (h₁.skeleton r.mono (hΓ.cons trivial trivial) i.fresh n hlog₁)
      r₁.2.2.ne_abs (hc.logged.accepts hlog₂) (GenOK.nil c Δ)
      (h₂.skeleton r.poly (hΓ.cons trivial trivial) (hc.inv₂ i₁)
        (hc.nac i₁ r₁.2.1 trivial r₁.1) hlog)
  | .fn hw hp h, hΓ, i, n, hlog => by
    have rp := hp.nac hΓ i n
    obtain ⟨Δ', hP, r'⟩ := hp.skeleton r hΓ i n (fun p hp' => hlog p (h.log_grows p hp'))
    exact .fn hw hP (h.skeleton r' rp.2.2 (hp.inv₂ i) rp.1 hlog)

theorem TypeFields.skeleton {c : Certificate} {Δ : PCtx} (r : PRel Γ Δ) :
    TypeFields Γ s fs F s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ c.log) → PFields c Δ fs F
  | .nil, _, _, _, _ => .nil
  | .cons h₁ h₂, hΓ, i, n, hlog =>
    have r₁ := h₁.nac hΓ i n
    .cons (h₁.skeleton r hΓ i n (fun p hp => hlog p (h₂.log_grows p hp))) r₁.2.2
      (h₂.skeleton r hΓ (h₁.inv₂ i) r₁.1 hlog)

/-- Parameters: their skeleton, and the context of the body. -/
theorem TypeParams.skeleton {c : Certificate} {Δ : PCtx} (r : PRel Γ Δ) :
    TypeParams Γ s ps P Γ' s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ c.log) → ∃ Δ', PParams c Δ ps P Δ' ∧ PRel Γ' Δ'
  | .nil, _, _, _, _ => ⟨Δ, .nil, r⟩
  | .req _ h, hΓ, i, n, hlog => by
    obtain ⟨Δ', hP, r'⟩ := h.skeleton r.mono (hΓ.cons trivial trivial) i.fresh n hlog
    exact ⟨Δ', .req hP, r'⟩
  | .dflt _ hd hc h, hΓ, i, n, hlog => by
    have rd := hd.nac hΓ i.fresh n
    have i₁ := hd.inv₂ i.fresh
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (h.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    obtain ⟨Δ', hP, r'⟩ := h.skeleton r.mono (hΓ.cons trivial trivial) (hc.inv₂ i₁)
      (hc.nac i₁ rd.2.1 trivial rd.1) hlog
    exact ⟨Δ', .dflt (hd.skeleton r hΓ i.fresh n hlog₁) rd.2.2.ne_abs
      (hc.logged.accepts hlog₂) hP, r'⟩
end

/-- The built-ins as a skeleton context. -/
def pbuiltinsMono : PCtx := builtins.map fun p => (p.1, .mono p.2)

theorem PRel.builtins : PRel builtins pbuiltinsMono :=
  .mono (.mono (.mono (.mono (.mono .nil))))

/-- **Adequacy**: an accepted run yields a valid certificate, with a
typing skeleton for the term at the inferred type. -/
theorem TypeTerm.certificate (h : TypeTerm builtins (State.initK K) t st s')
    (hr : StructRanked s'.bounds r) :
    (s'.certificate r).Valid ∧ PTyp (s'.certificate r) pbuiltinsMono t st :=
  ⟨h.certificateValid hr,
    h.skeleton PRel.builtins builtins_NAC Inv₂.init LogNAC.init (fun _ hp => hp)⟩

/-- Theorem 1 again, through certificates: an accepted run has a valid
certificate whose skeleton gives the declarative typing, over a solution
without recursive types. -/
theorem theorem1_cert (h : Infers K t st s') :
    ∃ c : Certificate,
      Typ (defsOf c.state) (pbuiltinsMono.toCtx c.bounds .gv) t st.toTy ∧
        ∃ r, Defs.Ranked (defsOf c.state) r := by
  obtain ⟨h, r, hr⟩ := h
  have hc := h.certificate hr
  exact ⟨_, PTyp.sound_top hc.1 hc.2, _, hc.1.nonrec⟩

end BoltCore.Alg
