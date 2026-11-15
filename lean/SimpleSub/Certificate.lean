import SimpleSub.Kinds

/-!
# Certificates

The plan for running the proofs on real code: the inferencer (`lib/typer.ml`
now, Bolt's compiler later) emits a *certificate* of its result, and a
checker decides whether it is valid. This file states what a certificate
is, what validity means, and proves the two theorems a checker rests on:

* **Soundness** (`CTyp.sound`): a valid certificate with a typing
  skeleton for `t` gives `t` its type in the declarative system. This is
  Theorem 1 for certificates; nothing about how the certificate was
  produced is assumed.
* **Adequacy** (`TypeTerm.certificate`): every run of the algorithm model
  yields a valid certificate and a skeleton for its term. So the format
  can express everything the algorithm does, and a correct inferencer is
  never rejected.

A certificate holds the accepted constraints, the bounds of each variable,
and the kinds of the variables, as finite lists (variables not listed have
no bounds and lack no labels). Validity collects the invariants of the
soundness proofs: justification and consistency (`Inv`), bounds recorded as
accepted constraints with no variable lower bounds (`Inv₂`), `Abs` never a
function component (`LogNAC`), and the kind discipline (`KLog`). Each one
quantifies only over the certificate's lists, so it is decidable; the
executable checker will come with proofs that it decides them.

The typing skeleton (`CTyp`) gives each node of the term a simple type and
requires, at each place where the algorithm constrains, that the
constraint is accepted by the certificate. It mirrors `TypeTerm` without
the state: `let` is monomorphic, as in the model.
-/

namespace SimpleSub.Alg

open State

/-! ## Certificates and validity -/

structure Certificate where
  /-- The accepted constraints. -/
  log : List (SType × SType)
  /-- The bounds of each variable with bounds. -/
  vars : List (Nat × Bounds)
  /-- The kind of each variable with a non-empty kind. -/
  kinds : List (Nat × List String)

namespace Certificate

def bounds (c : Certificate) (v : Nat) : Bounds := (c.vars.lookup v).getD {}

def kind (c : Certificate) (v : Nat) : List String := (c.kinds.lookup v).getD []

/-- The certificate as an algorithm state (the counter, cache and
expansion table play no role in validity). -/
def state (c : Certificate) : State := ⟨c.bounds, 0, [], [], c.log, c.kind⟩

/-- The certificate accepts `a ≤ b`: it is reflexive or listed. -/
def Accepts (c : Certificate) (a b : SType) : Prop := a = b ∨ (a, b) ∈ c.log

structure Valid (c : Certificate) : Prop where
  inv : Inv c.state
  inv₂ : Inv₂ c.state
  nac : LogNAC c.state
  kinds : KLog c.kind c.state

end Certificate

/-! ## Typing skeletons -/

mutual
/-- A typing skeleton for a term, checked against a certificate. -/
inductive CTyp (c : Certificate) : SCtx → Term → SType → Prop where
  | lit : CTyp c Γ (.lit n) (.prim "int")
  | var : Γ.lookup x = some st → CTyp c Γ (.var x) st
  | lam : CTyp c ((x, st₁) :: Γ) t st₂ → CTyp c Γ (.lam x t) (.arrow st₁ st₂)
  | app : CTyp c Γ f stf → CTyp c Γ a sta → stf ≠ .abs →
      c.Accepts stf (.arrow sta st) → CTyp c Γ (.app f a) st
  | rcd : CFields c Γ fs F → CTyp c Γ (.rcd fs) (.record F .abs)
  | sel : CTyp c Γ t st₀ → st₀ ≠ .abs →
      c.Accepts st₀ (.record (.cons l st .nil) .abs) → CTyp c Γ (.sel t l) st
  | ext : CTyp c Γ t st₀ → CFields c Γ fs F → st₀ ≠ .abs →
      c.Accepts st₀ (.record F.absOf ρ) → CTyp c Γ (.ext t fs) (.record F ρ)
  | extNil : CTyp c Γ t st → CTyp c Γ (.ext t []) st
  | letIn : CTyp c Γ r str → CTyp c ((x, str) :: Γ) b st → CTyp c Γ (.letIn false x r b) st
  | letRec : CTyp c ((x, stx) :: Γ) r inf → inf ≠ .abs → c.Accepts inf stx →
      CTyp c ((x, stx) :: Γ) b st → CTyp c Γ (.letIn true x r b) st

inductive CFields (c : Certificate) : SCtx → List (String × Term) → SFields → Prop where
  | nil : CFields c Γ [] .nil
  | cons : CTyp c Γ t st → CFields c Γ fs F → CFields c Γ ((l, t) :: fs) (.cons l st F)
end

/-! ## Soundness -/

/-- A valid certificate's state satisfies everything the solution theorem
needs; the kinds give the tail ranking. -/
theorem Certificate.Valid.final {c : Certificate} (hv : c.Valid) :
    Final c.state (kindRank (loggedLabels c.state) c.kind) :=
  ⟨hv.inv, hv.inv₂, hv.nac,
    kinds_tailRanked ⟨rfl, hv.kinds, fun _ _ _ h => nomatch h⟩ hv.inv₂⟩

theorem Certificate.Valid.sub {c : Certificate} (hv : c.Valid) (h : c.Accepts a b)
    (ha : a ≠ .abs) : Sub (defsOf c.state) a.toTy b.toTy :=
  hv.final.sub (s := c.state) h (fun _ h => h) ha

mutual
/-- **Theorem 1 for certificates**: a typing skeleton checked against a
valid certificate gives a declarative typing, at the type the skeleton
assigns translated through the certificate's solution. -/
theorem CTyp.sound {c : Certificate} (hv : c.Valid) :
    CTyp c Γ t st → Typ (defsOf c.state) Γ.toCtx t st.toTy
  | .lit => .lit
  | .var hx => Typ.var_mono (SCtx.lookup_toCtx hx)
  | .lam h => .lam (h.sound hv)
  | .app h₁ h₂ ha hc => .app (.sub (h₁.sound hv) (hv.sub hc ha)) (h₂.sound hv)
  | .rcd h => .rcd (h.sound hv)
  | .sel h ha hc => .sel (.sub (h.sound hv) (hv.sub hc ha))
  | .ext h₁ h₂ ha hc => by
    have hs := hv.sub hc ha
    simp only [SType.toTy, SFields.toFields_absOf] at hs
    exact .ext (.sub (h₁.sound hv) hs) (h₂.sound hv)
  | .extNil h => .extNil (h.sound hv)
  | .letIn h₁ h₂ => Typ.letIn_mono (h₁.sound hv) (h₂.sound hv)
  | .letRec h₁ ha hc h₂ => Typ.letRec_mono (.sub (h₁.sound hv) (hv.sub hc ha)) (h₂.sound hv)

theorem CFields.sound {c : Certificate} (hv : c.Valid) :
    CFields c Γ fs F → TypFields (defsOf c.state) Γ.toCtx fs F.toFields
  | .nil => .nil
  | .cons h₁ h₂ => .cons (h₁.sound hv) (h₂.sound hv)
end

/-! ## Adequacy: every run yields a valid certificate -/

mutual
/-- The variables occurring in a type. -/
def SType.vars : SType → List Nat
  | .var v => [v]
  | .prim _ | .abs => []
  | .arrow a b => a.vars ++ b.vars
  | .record fs t => fs.vars ++ t.vars

def SFields.vars : SFields → List Nat
  | .nil => []
  | .cons _ f fs => f.vars ++ fs.vars
end

/-- The variables occurring in accepted constraints. -/
def logVars (log : List (SType × SType)) : List Nat := log.flatMap fun p => p.1.vars ++ p.2.vars

theorem mem_logVars {log : List (SType × SType)} {p : SType × SType} (hp : p ∈ log) :
    (∀ v ∈ p.1.vars, v ∈ logVars log) ∧ (∀ v ∈ p.2.vars, v ∈ logVars log) :=
  ⟨fun _ hv => List.mem_flatMap.mpr ⟨p, hp, List.mem_append_left _ hv⟩,
   fun _ hv => List.mem_flatMap.mpr ⟨p, hp, List.mem_append_right _ hv⟩⟩

theorem lookup_map_self {β : Type} (f : Nat → β) (v : Nat) :
    ∀ xs : List Nat, (xs.map fun w => (w, f w)).lookup v = if v ∈ xs then some (f v) else none
  | [] => by simp
  | w :: xs => by
    have ih := lookup_map_self f v xs
    by_cases h : v = w
    · subst h; simp
    · simp only [List.map_cons, List.lookup]
      have : (v == w) = false := by simp [h]
      rw [this]; simp [ih, h]

/-- The certificate of a state: its constraints, and the bounds and kinds of
the variables they mention. -/
def State.certificate (s : State) : Certificate where
  log := s.log
  vars := (logVars s.log).map fun v => (v, s.bounds v)
  kinds := (logVars s.log).map fun v => (v, s.kind v)

theorem State.certificate_kind {s : State} {v : Nat} (h : v ∈ logVars s.log) :
    s.certificate.kind v = s.kind v := by
  simp [Certificate.kind, State.certificate, lookup_map_self, h]

theorem State.certificate_bounds {s : State} (i : Inv₂ s) : s.certificate.bounds = s.bounds := by
  funext v
  simp only [Certificate.bounds, State.certificate, lookup_map_self]
  split
  · rfl
  · next h =>
    -- a variable with a bound occurs in an accepted constraint
    have hu : (s.bounds v).upper = [] := by
      cases hb : (s.bounds v).upper with
      | nil => rfl
      | cons x _ =>
        have := i.inLog.1 v x (by rw [hb]; exact List.mem_cons_self ..)
        exact absurd ((mem_logVars this).1 v (by simp [SType.vars])) h
    have hl : (s.bounds v).lower = [] := by
      cases hb : (s.bounds v).lower with
      | nil => rfl
      | cons x _ =>
        have := i.inLog.2 v x (by rw [hb]; exact List.mem_cons_self ..)
        exact absurd ((mem_logVars this).2 v (by simp [SType.vars])) h
    cases hb : s.bounds v with
    | mk lo up => simp only [hb] at hu hl; subst hu hl; rfl

/-! ### Kinds only matter at the variables of a type -/

theorem rowView_tail_mem : ∀ {t : SType} {ρ : Nat}, (rowView t).2 = .var ρ → ρ ∈ t.vars
  | .record fs t, ρ, h => by
    simp only [rowView] at h
    simp only [SType.vars, List.mem_append]
    exact .inr (rowView_tail_mem h)
  | .var w, ρ, h => by simp [rowView] at h; simp [SType.vars, h]
  | .prim _, _, h | .arrow _ _, _, h | .abs, _, h => by simp [rowView] at h

section Congr
variable {K K' : Nat → List String}

/-- `K` and `K'` agree on the variables of `t`. -/
def Agree (K K' : Nat → List String) (t : SType) : Prop := ∀ v ∈ t.vars, K v = K' v

theorem RowKind.congr {fs : SFields} {ρ : Nat} {l : String} (h : K ρ = K' ρ) :
    RowKind K fs ρ l ↔ RowKind K' fs ρ l := by simp [RowKind, h]

theorem KOK.congr {a b : SType} (ha : Agree K K' a) (hb : Agree K K' b) (h : KOK K a b) :
    KOK K' a b := fun ρ σ hρ hσ l =>
  (RowKind.congr (ha ρ (rowView_tail_mem hρ))).symm.trans
    ((h ρ σ hρ hσ l).trans (RowKind.congr (hb σ (rowView_tail_mem hσ))))

theorem KEmpty.congr {t : SType} (ht : Agree K K' t) (h : KEmpty K t) : KEmpty K' t :=
  fun ρ hρ l hl => h ρ hρ l ((RowKind.congr (ht ρ (rowView_tail_mem hρ))).2 hl)

theorem RecOK.congr {t : SType} (ht : Agree K K' t) (h : RecOK K t) : RecOK K' t :=
  fun ρ hρ => by
    have := h ρ hρ
    rw [ht ρ (rowView_tail_mem hρ)] at this
    exact this

mutual
theorem WK.congr : ∀ {t : SType}, Agree K K' t → WK K t → WK K' t
  | .var _, _, _ | .prim _, _, _ | .abs, _, _ => trivial
  | .arrow a b, ht, ⟨wa, ea, wb, eb⟩ =>
    have ha : Agree K K' a := fun v hv => ht v (by simp [SType.vars, hv])
    have hb : Agree K K' b := fun v hv => ht v (by simp [SType.vars, hv])
    ⟨wa.congr ha, ea.congr ha, wb.congr hb, eb.congr hb⟩
  | .record fs t, ht, ⟨wf, wt, hr⟩ =>
    ⟨FWK.congr (fun v hv => ht v (by simp [SType.vars, hv])) wf,
      wt.congr (fun v hv => ht v (by simp [SType.vars, hv])), hr.congr ht⟩

theorem FWK.congr : ∀ {fs : SFields}, (∀ v ∈ fs.vars, K v = K' v) → FWK K fs → FWK K' fs
  | .nil, _, _ => trivial
  | .cons _ f fs, ht, ⟨wf, ef, wr⟩ =>
    have hf : Agree K K' f := fun v hv => ht v (by simp [SFields.vars, hv])
    ⟨wf.congr hf, ef.congr hf, FWK.congr (fun v hv => ht v (by simp [SFields.vars, hv])) wr⟩
end

end Congr

/-- Justification and consistency only depend on the bounds and the log. -/
theorem Inv.congr {s s' : State} (hb : s'.bounds = s.bounds) (hl : s'.log = s.log) (h : Inv s) :
    Inv s' := by
  obtain ⟨b, n, c, e, l, k⟩ := s
  obtain ⟨b', n', c', e', l', k'⟩ := s'
  simp only at hb hl
  subst hb hl
  exact ⟨h.just, h.cons⟩

/-- The certificate of a state satisfying the invariants is valid. -/
theorem State.certificate_valid {s : State} (hi : Inv s) (i : Inv₂ s) (hn : LogNAC s)
    (hk : KInv K s) : s.certificate.Valid := by
  have hb := State.certificate_bounds i
  refine ⟨Inv.congr hb rfl hi, ?_, ?_, ?_⟩
  · exact i.of_bounds hb (fun _ hp => hp)
  · exact hn
  · intro p hp
    have hv := mem_logVars hp
    have h₁ : Agree K s.certificate.kind p.1 := fun v hv' => by
      rw [State.certificate_kind (s := s) (hv.1 v hv'), hk.kind]
    have h₂ : Agree K s.certificate.kind p.2 := fun v hv' => by
      rw [State.certificate_kind (s := s) (hv.2 v hv'), hk.kind]
    have := hk.log p hp
    exact ⟨this.1.congr h₁, this.2.1.congr h₂, this.2.2.congr h₁ h₂⟩

theorem Logged.accepts {s : State} {c : Certificate} (hlog : ∀ p, p ∈ s.log → p ∈ c.log) :
    Logged s a b → c.Accepts a b
  | .inl h => .inl h
  | .inr h => .inr (hlog _ h)

mutual
/-- A run of the algorithm gives a typing skeleton, checked against any
certificate that accepts the constraints it logged. -/
theorem TypeTerm.skeleton {c : Certificate} :
    TypeTerm Γ s t st s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ c.log) → CTyp c Γ t st
  | .lit, _, _, _, _ => .lit
  | .var hx, _, _, _, _ => .var hx
  | .lam _ h, hΓ, i, n, hlog =>
    .lam (h.skeleton (hΓ.cons trivial (fun h => nomatch h)) i.fresh n hlog)
  | .app _ h₁ h₂ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i.fresh
    have r₁ := h₁.nac hΓ i.fresh n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .app (h₁.skeleton hΓ i.fresh n hlog₁) (h₂.skeleton hΓ i₁ r₁.1 hlog₂) r₁.2.2
      (hc.logged.accepts hlog)
  | .rcd h, hΓ, i, n, hlog => .rcd (h.skeleton hΓ i n hlog)
  | .sel _ h hc, hΓ, i, n, hlog => by
    have r := h.nac hΓ i.fresh n
    exact .sel (h.skeleton hΓ i.fresh n fun p hp => hlog p (hc.log_grows p hp)) r.2.2
      (hc.logged.accepts hlog)
  | .extNil h, hΓ, i, n, hlog => .extNil (h.skeleton hΓ i n hlog)
  | .ext _ h₁ h₂ _ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i
    have r₁ := h₁.nac hΓ i n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .ext (h₁.skeleton hΓ i n hlog₁) (h₂.skeleton hΓ i₁ r₁.1 hlog₂) r₁.2.2
      (hc.logged.accepts hlog)
  | .letIn h₁ h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac hΓ i n
    exact .letIn (h₁.skeleton hΓ i n fun p hp => hlog p (h₂.log_grows p hp))
      (h₂.skeleton (hΓ.cons r₁.2.1 r₁.2.2) (h₁.inv₂ i) r₁.1 hlog)
  | .letRec _ h₁ hc h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac (hΓ.cons trivial (fun h => nomatch h)) i.fresh n
    have i₁ := h₁.inv₂ i.fresh
    have hlog₂ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog p (h₂.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ c.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact .letRec (h₁.skeleton (hΓ.cons trivial (fun h => nomatch h)) i.fresh n hlog₁)
      r₁.2.2 (hc.logged.accepts hlog₂)
      (h₂.skeleton (hΓ.cons trivial (fun h => nomatch h)) (hc.inv₂ i₁)
        (hc.nac i₁ r₁.2.1 trivial r₁.1) hlog)

theorem TypeFields.skeleton {c : Certificate} :
    TypeFields Γ s fs F s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ c.log) → CFields c Γ fs F
  | .nil, _, _, _, _ => .nil
  | .cons h₁ h₂, hΓ, i, n, hlog =>
    have r₁ := h₁.nac hΓ i n
    .cons (h₁.skeleton hΓ i n fun p hp => hlog p (h₂.log_grows p hp))
      (h₂.skeleton hΓ (h₁.inv₂ i) r₁.1 hlog)
end

/-- **Adequacy**: a run of the algorithm from scratch yields a valid
certificate, with a typing skeleton for the term at the inferred type. -/
theorem TypeTerm.certificate (h : TypeTerm builtins (State.initK K) t st s') :
    s'.certificate.Valid ∧ CTyp s'.certificate builtins t st :=
  ⟨State.certificate_valid h.inv_init (h.inv₂ Inv₂.init)
      (h.nac builtins_NAC Inv₂.init LogNAC.init).1 (h.kinds builtins_K Inv₂.init KInv.init).1,
    h.skeleton builtins_NAC Inv₂.init LogNAC.init fun _ hp => hp⟩

/-- Theorem 1 again, through certificates: the certificate of a run is
valid, and its skeleton gives the declarative typing. -/
theorem theorem1_cert (h : TypeTerm builtins (State.initK K) t st s') :
    Typ (defsOf s'.certificate.state) builtins.toCtx t st.toTy :=
  have r := h.certificate
  r.2.sound r.1

end SimpleSub.Alg
