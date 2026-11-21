import BoltCore.PolyLet

/-!
# Adequacy

Every accepted run of the algorithm yields a valid certificate and a
typing skeleton with let-polymorphism for its term (`TypeTerm.certificate`),
so the checker never rejects a correct run. With `PTyp.sound_top`, this is
Theorem 1 (`theorem1`): a term the algorithm types has the inferred type in
the declarative system, over a solution without recursive types.

What a `let` generalizes and what a use instantiates are checked against
the certificate, which is the state the *whole* run ends in, while a
derivation only knows its own part of the run. So the proof is relative to
that final state `F`, with three things about the rest of the run:

* `Fin F L lvl s'`: after `s'`, a variable above `lvl` that is allocated
  keeps its bounds, and no other variable gets to mention it. Each part of
  a run has this from the part after it, which is local to a frame
  (`TypeTerm.frame`).
* `Frozen F s gen`, for each `let`-bound name in scope: the generalized
  variables have in `F` the bounds they have now, and no other variable
  mentions them. This is `GenOK`, and what `InstOK` needs.
* `JustLoc F s`: every constraint logged so far is justified by a step
  over the bounds of `F`, from the constraints logged so far. At the end
  this is justification. It cannot be stated of the bounds so far: the
  renamed constraints of an instantiation are justified by the renamed
  steps, which needs that no other variable mentions the generalized ones.
-/

namespace BoltCore.Alg

open State

/-! ## Justification over the final bounds -/

/-- Every constraint logged so far is justified by a step over the bounds
of `F`, from the constraints logged so far. -/
def JustLoc (F s : State) : Prop := ∀ p ∈ s.log, GStep F.bounds (Logged s) p.1 p.2

/-- Across a top-level `constrain`: its constraints are justified when it
returns. -/
theorem JustLoc.constrain {F s s' : State} {a b : SType} (hj : JustLoc F s)
    (hc : ConstrainTop s a b s') (hs : Scope s) (e : Ext s' F) : JustLoc F s' := fun p hp =>
  match hc.justNew hs p hp with
  | .inl h =>
    GStep.imp (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => Logged.of_log hc.to_ext.log h)
      (hj p h)
  | .inr h => GStep.imp e.upper e.lower (fun _ _ h => h) h

/-- The generalized variables `gen` are finished: no other variable
mentions them in `F`, and they have in `F` the bounds they have in `s`. -/
structure Frozen (F s : State) (gen : List Nat) : Prop where
  avoid : ∀ v, v ∉ gen → ∀ b, (b ∈ (F.bounds v).upper ∨ b ∈ (F.bounds v).lower) → Av gen b
  upper : ∀ α ∈ gen, ∀ u ∈ (F.bounds α).upper, u ∈ (s.bounds α).upper
  lower : ∀ α ∈ gen, ∀ l ∈ (F.bounds α).lower, l ∈ (s.bounds α).lower

theorem Frozen.ext {F s s₁ : State} {gen : List Nat} (h : Frozen F s gen) (e : Ext s s₁) :
    Frozen F s₁ gen :=
  ⟨h.avoid, fun α hα u hu => e.upper _ _ (h.upper α hα u hu),
    fun α hα l hl => e.lower _ _ (h.lower α hα l hl)⟩

/-- Across an instantiation: a renamed constraint is justified by the
renamed step. A bound of a generalized variable is a bound it has now,
whose renaming the copy got; a bound of another variable does not mention
the generalized ones, so it is not renamed. -/
theorem JustLoc.instantiate {F s : State} {lvl : Nat} {gen : List Nat} {ρ : Nat → Nat}
    (hj : JustLoc F s) (hi : IsInst s lvl gen ρ) (fz : Frozen F s gen)
    (e : Ext (s.instantiate gen ρ) F) : JustLoc F (s.instantiate gen ρ) := by
  have hfix : ∀ v, v ∉ gen → ∀ b, (b ∈ (F.bounds v).upper ∨ b ∈ (F.bounds v).lower) →
      b.rename ρ = b := fun v hv b hb =>
    SType.rename_fix fun w hw => hi.fix w (fz.avoid v hv b hb w hw)
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    refine GStep.rename (ρ := ρ) (fun v b hb => ?_) (fun v b hb => ?_)
      (fun a b h => h.instantiate) (hj q hq)
    · by_cases hv : v ∈ gen
      · exact e.upper _ _ (mem_upper_copy hi hv (fz.upper v hv b hb))
      · rw [hi.fix v hv, hfix v hv b (.inl hb)]; exact hb
    · by_cases hv : v ∈ gen
      · exact e.lower _ _ (mem_lower_copy hi hv (fz.lower v hv b hb))
      · rw [hi.fix v hv, hfix v hv b (.inr hb)]; exact hb
  · exact GStep.imp (fun _ _ h => h) (fun _ _ h => h)
      (fun _ _ h => Logged.mono .instantiate h) (hj p hp)

/-! ## The rest of a run -/

/-- The final state `F`, seen from `s` at level `lvl`: the frame of `s`
is closed in `F`, and a variable outside it has in `F` the bounds it has
in `s`. -/
structure Fin (F : State) (L : Nat → Nat) (lvl : Nat) (s : State) : Prop where
  ext : Ext s F
  level : F.level = L
  closed : XClosed (Frame L s.next lvl) F
  upper : ∀ v, ¬ Frame L s.next lvl v → ∀ b, b ∈ (F.bounds v).upper → b ∈ (s.bounds v).upper
  lower : ∀ v, ¬ Frame L s.next lvl v → ∀ b, b ∈ (F.bounds v).lower → b ∈ (s.bounds v).lower

/-- At the end of the run. -/
theorem Fin.final {F : State} (w : WF F) (lvl : Nat) : Fin F F.level lvl F :=
  ⟨.refl, rfl, w.closed lvl, fun _ _ _ h => h, fun _ _ _ h => h⟩

/-- From the end of a part of a run to its start, when that part is local
to the frame of its start. -/
theorem Fin.before {F s s' : State} {L : Nat → Nat} {lvl : Nat} (hf : Fin F L lvl s')
    (e : Ext s s') (l : Local (Frame L s.next lvl) s s') : Fin F L lvl s := by
  have sub : ∀ v, Frame L s'.next lvl v → Frame L s.next lvl v := fun v hv =>
    hv.elim (fun h => .inl (Nat.le_trans e.next h)) .inr
  refine ⟨e.trans hf.ext, hf.level, fun v hv b hb => ?_, fun v hv b hb => ?_, fun v hv b hb => ?_⟩
  · by_cases hv' : Frame L s'.next lvl v
    · exact (hf.closed v hv' b hb).mono sub
    · exact l.closed v hv b (hb.imp (hf.upper v hv' b) (hf.lower v hv' b))
  · have := hf.upper v (fun h => hv (sub v h)) b hb
    rwa [l.frame v hv] at this
  · have := hf.lower v (fun h => hv (sub v h)) b hb
    rwa [l.frame v hv] at this

/-- One level up: a variable of the next level that is allocated has the
bounds it has now, of at most its level. -/
theorem Fin.up {F s : State} {L : Nat → Nat} {lvl : Nat} (hf : Fin F L lvl s) (hl : LevelInv s)
    (hL : s.level = L) : Fin F L (lvl + 1) s := by
  have sub : ∀ v, Frame L s.next lvl v → Frame L s.next (lvl + 1) v := fun v hv =>
    hv.elim .inl fun h => .inr (Nat.le_succ_of_le h)
  refine ⟨hf.ext, hf.level, fun v hv b hb => ?_, fun v hv b hb => hf.upper v (fun h => hv (sub v h)) b hb,
    fun v hv b hb => hf.lower v (fun h => hv (sub v h)) b hb⟩
  by_cases hv' : Frame L s.next lvl v
  · exact (hf.closed v hv' b hb).mono sub
  · have hb' := hb.imp (hf.upper v hv' b) (hf.lower v hv' b)
    have hvl : L v ≤ lvl + 1 := hv.elim (fun h => absurd (.inl h) hv') id
    have := hl v b hb'
    rw [hL] at this
    exact (SType.level_le.mp (Nat.le_trans this hvl)).mono fun _ hw => .inr hw

/-! ## What a run keeps -/

/-- The invariants of a state that do not depend on the rest of the run. -/
structure Good (L : Nat → Nat) (s : State) : Prop where
  level : s.level = L
  wf : WF s
  inv₂ : Inv₂ s
  nac : LogNAC s

theorem Good.fresh {L : Nat → Nat} {s : State} (g : Good L s) : Good L s.fresh :=
  ⟨g.level, g.wf.fresh, g.inv₂.fresh, g.nac⟩

/-- What is known of an inferred type. -/
structure TyOk (L : Nat → Nat) (lvl : Nat) (s : State) (st : SType) : Prop where
  scope : st.In (· < s.next)
  low : st.In (fun w => L w ≤ lvl)
  nac : st.NAC
  pre : st.IsPre

section
variable {L : Nat → Nat} {lvl : Nat}

theorem TypeTerm.good (h : TypeTerm Γ lvl s t st s') (g : Good L s) (hΓ : CtxWF L lvl s Γ)
    (hn : CtxNAC Γ) : Good L s' ∧ TyOk L lvl s' st ∧ CtxWF L lvl s' Γ := by
  have r := h.wf g.level g.wf hΓ
  have n := h.nac hn g.inv₂ g.nac
  exact ⟨⟨h.to_ext.level.trans g.level, r.1, h.inv₂ g.inv₂, n.1⟩, ⟨r.2.1, r.2.2, n.2.1, n.2.2⟩,
    hΓ.run g.level g.wf h r.1⟩

theorem TypeFields.good (h : TypeFields Γ lvl s fs Fd s') (g : Good L s) (hΓ : CtxWF L lvl s Γ)
    (hn : CtxNAC Γ) :
    Good L s' ∧ Fd.In (fun w => L w ≤ lvl) ∧ CtxWF L lvl s' Γ := by
  have r := h.wf g.level g.wf hΓ
  have n := h.nac hn g.inv₂ g.nac
  exact ⟨⟨h.to_ext.level.trans g.level, r.1, h.inv₂ g.inv₂, n.1⟩, r.2.2,
    hΓ.runFields g.level g.wf h r.1⟩

theorem TypeParams.good (h : TypeParams Γ lvl s ps P Γ' s') (g : Good L s)
    (hΓ : CtxWF L lvl s Γ) (hn : CtxNAC Γ) : Good L s' ∧ CtxWF L lvl s' Γ' ∧ CtxNAC Γ' := by
  have r := h.wf g.level g.wf hΓ
  have n := h.nac hn g.inv₂ g.nac
  exact ⟨⟨h.to_ext.level.trans g.level, r.1, h.inv₂ g.inv₂, n.1⟩, r.2.2.2, n.2.2⟩

theorem ConstrainTop.good {s s' : State} {a b : SType} {Γ : PCtx} (h : ConstrainTop s a b s')
    (g : Good L s) (hΓ : CtxWF L lvl s Γ) (ha : a.In (· < s.next)) (hb : b.In (· < s.next))
    (hal : a.In (fun w => L w ≤ lvl)) (hbl : b.In (fun w => L w ≤ lvl)) (han : a.NAC)
    (hbn : b.NAC) : Good L s' ∧ CtxWF L lvl s' Γ := by
  have w' := h.wf g.wf ha hb
  exact ⟨⟨h.to_ext.level.trans g.level, w', h.inv₂ g.inv₂, h.nac g.inv₂ han hbn g.nac⟩,
    hΓ.constrain g.level g.wf h w' hal hbl⟩

/-- The fresh variable of a state, allocated at `lvl`. -/
theorem fresh_ty {s : State} (g : Good L s) (hlv : s.level s.next = lvl) :
    (SType.var s.next).In (· < s.fresh.next) ∧ (SType.var s.next).In (fun w => L w ≤ lvl) :=
  ⟨in_fresh s, SType.in_var.mpr (by rw [← g.level]; exact Nat.le_of_eq hlv)⟩

/-- The frame of a run, for the levels of the run. -/
theorem TypeTerm.frameL {s s' : State} (h : TypeTerm Γ lvl' s t st s') (g : Good L s)
    (hΓ : CtxWF L lvl s Γ) : Local (Frame L s.next lvl) s s' := by
  have hL := g.level
  subst hL
  exact (h.frame g.wf hΓ.ctxIn).1

/-! ### The rest of a run, from a part of it -/

theorem Fin.beforeRun {F s s' : State} (hf : Fin F L lvl s') (h : TypeTerm Γ lvl' s t st s')
    (g : Good L s) (hΓ : CtxWF L lvl s Γ) : Fin F L lvl s := by
  have hL := g.level
  subst hL
  exact hf.before h.to_ext (h.frame g.wf hΓ.ctxIn).1

theorem Fin.beforeFields {F s s' : State} (hf : Fin F L lvl s')
    (h : TypeFields Γ lvl' s fs Fd s') (g : Good L s) (hΓ : CtxWF L lvl s Γ) : Fin F L lvl s := by
  have hL := g.level
  subst hL
  exact hf.before h.to_ext (h.frame g.wf hΓ.ctxIn)

theorem Fin.beforeParams {F s s' : State} (hf : Fin F L lvl s')
    (h : TypeParams Γ lvl' s ps P Γ' s') (g : Good L s) (hΓ : CtxWF L lvl s Γ) :
    Fin F L lvl s := by
  have hL := g.level
  subst hL
  exact hf.before h.to_ext (h.frame g.wf hΓ.ctxIn)

theorem Fin.beforeConstrain {F s s' : State} {a b : SType} (hf : Fin F L lvl s')
    (h : ConstrainTop s a b s') (g : Good L s) (ha : a.In (fun w => L w ≤ lvl))
    (hb : b.In (fun w => L w ≤ lvl)) : Fin F L lvl s := by
  have hL := g.level
  subst hL
  exact hf.before h.to_ext (h.frame g.wf ha hb)

theorem Fin.beforeFresh {F s : State} (hf : Fin F L lvl s.fresh) (g : Good L s) :
    Fin F L lvl s := by
  have hL := g.level
  subst hL
  exact hf.before .fresh (Local.fresh (g.wf.closed lvl))

/-- A constraint accepted on the way is accepted by the certificate. -/
theorem accepts {c : Certificate} {F s : State} {a b : SType}
    (hcl : ∀ p, p ∈ F.log → p ∈ c.log) (e : Ext s F) (h : Logged s a b) : c.Accepts a b :=
  h.elim .inl fun h => .inr (hcl _ (e.log _ h))

/-! ## Contexts and the final state -/

/-- An entry is in scope, and the variables it generalizes are finished. -/
def CEntry.Ok (F s : State) : CEntry → Prop
  | .mono st => st.In (· < s.next)
  | .poly gen st => st.In (· < s.next) ∧ Frozen F s gen

/-- Every entry of the context, shadowed or not. -/
def CtxOk (F s : State) (Γ : PCtx) : Prop := ∀ p ∈ Γ, p.2.Ok F s

theorem CtxOk.cons {F s : State} {Γ : PCtx} {x : String} {e : CEntry} (h : CtxOk F s Γ)
    (he : e.Ok F s) : CtxOk F s ((x, e) :: Γ) := fun p hp =>
  (List.mem_cons.mp hp).elim (fun e' => e' ▸ he) (h p)

theorem CtxOk.ext {F s s₁ : State} {Γ : PCtx} (h : CtxOk F s Γ) (e : Ext s s₁) :
    CtxOk F s₁ Γ := fun p hp => by
  have := h p hp
  obtain ⟨x, en⟩ := p
  cases en with
  | mono st => exact SType.In.scope_mono this e.next
  | poly gen st => exact ⟨this.1.scope_mono e.next, this.2.ext e⟩

/-- No entry mentions the variables a `let` generalizes: they are
allocated after everything the entries mention. -/
theorem CtxOk.avoids {c : Certificate} {F s : State} {Γ : PCtx} (hcb : c.bounds = F.bounds)
    (hok : CtxOk F s Γ) (hs : Scope s) (m : Nat) :
    ∀ p ∈ Γ, p.2.Avoids c.bounds (genVars L s.next m lvl) := fun p hp => by
  have := hok p hp
  obtain ⟨x, en⟩ := p
  have out : ∀ v, v < s.next → v ∉ genVars L s.next m lvl := fun v hv hg =>
    absurd hv (Nat.not_lt.mpr (mem_genVars.mp hg).1)
  cases en with
  | mono st => exact fun w hw => out w (this w hw)
  | poly gen st =>
    intro v hv hg
    refine out v ?_
    simp only [schemeVars, List.mem_append, List.mem_flatMap] at hv
    rcases hv with hv | ⟨q, hq, hv⟩
    · exact this.1 v hv
    · obtain ⟨α, hα, ⟨u, hu, rfl⟩ | ⟨l, hl, rfl⟩⟩ := mem_genCs hq
      · rw [hcb] at hu
        rcases hv with hv | hv
        · simp only [SType.vars, List.mem_singleton] at hv
          exact absurd (hv ▸ hα) hg
        · exact (hs.bounds α u (.inl (this.2.upper α hα u hu))).2 v hv
      · rw [hcb] at hl
        rcases hv with hv | hv
        · exact (hs.bounds α l (.inr (this.2.lower α hα l hl))).2 v hv
        · simp only [SType.vars, List.mem_singleton] at hv
          exact absurd (hv ▸ hα) hg

/-- **What a `let` generalizes is finished**, once its right-hand side is
typed: the rest of the run is local to frames that do not contain it. -/
theorem frozen_let {F s s₁ s' : State} (hf : Fin F L lvl s') (hs : Scope s)
    (llet : Local (Frame L s.next lvl) s s') (lbody : Local (Frame L s₁.next lvl) s₁ s')
    (hm : s₁.next ≤ s'.next) : Frozen F s₁ (genVars L s.next s₁.next lvl) := by
  have out : ∀ w, w ∈ genVars L s.next s₁.next lvl → ¬ Frame L s'.next lvl w ∧
      ¬ Frame L s₁.next lvl w := fun w hw => by
    obtain ⟨_, h₂, h₃⟩ := mem_genVars.mp hw
    exact ⟨fun h => h.elim (fun h => absurd (Nat.lt_of_lt_of_le h₂ hm) (Nat.not_lt.mpr h))
        (fun h => absurd h (Nat.not_le.mpr h₃)),
      fun h => h.elim (fun h => absurd h₂ (Nat.not_lt.mpr h)) (fun h => absurd h (Nat.not_le.mpr h₃))⟩
  refine ⟨fun v hv b hb w hw hg => ?_, fun α hα u hu => ?_, fun α hα l hl => ?_⟩
  · by_cases hvF : Frame L s'.next lvl v
    · exact (out w hg).1 (hf.closed v hvF b hb w hw)
    · have hb' := hb.imp (hf.upper v hvF b) (hf.lower v hvF b)
      have hvl : lvl < L v := Nat.lt_of_not_le fun h => hvF (.inr h)
      by_cases h₀ : v < s.next
      · have hn : ¬ Frame L s.next lvl v := fun h =>
          h.elim (fun h => absurd h₀ (Nat.not_lt.mpr h)) (fun h => absurd h (Nat.not_le.mpr hvl))
        rw [llet.frame v hn] at hb'
        exact absurd ((hs.bounds v b hb').2 w hw) (Nat.not_lt.mpr (mem_genVars.mp hg).1)
      · by_cases h₁ : v < s₁.next
        · exact hv (mem_genVars.mpr ⟨Nat.le_of_not_lt h₀, h₁, hvl⟩)
        · exact (out w hg).2 (lbody.closed v (.inl (Nat.le_of_not_lt h₁)) b hb' w hw)
  · have := hf.upper α (out α hα).1 u hu
    rwa [lbody.frame α (out α hα).2] at this
  · have := hf.lower α (out α hα).1 l hl
    rwa [lbody.frame α (out α hα).2] at this

end

/-! ## Adequacy -/

section
variable {c : Certificate} {F : State}

mutual
/-- **A run of the algorithm gives a typing skeleton**, and justifies its
constraints over the final bounds. -/
theorem TypeTerm.cert (hcb : c.bounds = F.bounds) (hcl : ∀ p, p ∈ F.log → p ∈ c.log) :
    TypeTerm Γ lvl s t st s' → Good L s → CtxWF L lvl s Γ → CtxNAC Γ → CtxOk F s Γ →
    Fin F L lvl s' → JustLoc F s → JustLoc F s' ∧ PTyp c Γ t st
  | .lit, _, _, _, _, _, hj => ⟨hj, .lit⟩
  | .var hl, _, _, _, _, _, hj => ⟨hj, .var hl⟩
  | .inst (ρ := ρ) hl hi, g, _, _, hok, hf, hj => by
    have ok := hok _ (PCtx.lookup_mem hl)
    refine ⟨hj.instantiate hi ok.2 hf.ext, .inst hl ⟨hi.fix, fun α hα u hu => ?_, fun α hα l hl' => ?_⟩⟩
    · rw [hcb] at hu
      exact .inr (hcl _ (hf.ext.log _ (List.mem_append_left _ (List.mem_map.mpr
        ⟨(.var α, u), g.inv₂.inLog.1 α u (ok.2.upper α hα u hu), rfl⟩))))
    · rw [hcb] at hl'
      exact .inr (hcl _ (hf.ext.log _ (List.mem_append_left _ (List.mem_map.mpr
        ⟨(l, .var α), g.inv₂.inLog.2 α l (ok.2.lower α hα l hl'), rfl⟩))))
  | .lam (x := x) _ hlv h, g, hΓ, hn, hok, hf, hj => by
    have hv := fresh_ty g hlv
    have r := h.cert hcb hcl g.fresh (hΓ.fresh.cons (x := x) (e := .mono _) hv)
      (hn.cons (x := x) (e := .mono (.var _)) trivial trivial)
      ((hok.ext .fresh).cons (x := x) (e := .mono _) hv.1) hf hj
    exact ⟨r.1, .lam r.2⟩
  | .app _ hlv h₁ h₂ hc, g, hΓ, hn, hok, hf, hj => by
    have hv := fresh_ty g hlv
    have f₁ := h₁.good g.fresh hΓ.fresh hn
    have f₂ := h₂.good f₁.1 f₁.2.2 hn
    have hf₂ := hf.beforeConstrain hc f₂.1 f₁.2.1.low (SType.in_arrow.mpr ⟨f₂.2.1.low, hv.2⟩)
    have hf₁ := hf₂.beforeRun h₂ f₁.1 f₁.2.2
    have r₁ := h₁.cert hcb hcl g.fresh hΓ.fresh hn (hok.ext .fresh) hf₁ hj
    have r₂ := h₂.cert hcb hcl f₁.1 f₁.2.2 hn (hok.ext (Ext.fresh.trans h₁.to_ext)) hf₂ r₁.1
    exact ⟨r₂.1.constrain hc f₂.1.wf.scope hf.ext,
      .app r₁.2 r₂.2 f₁.2.1.pre.ne_abs (accepts hcl hf.ext hc.logged)⟩
  | .rcd h, g, hΓ, hn, hok, hf, hj => by
    have r := h.cert hcb hcl g hΓ hn hok hf hj
    exact ⟨r.1, .rcd r.2⟩
  | .sel _ hlv h hc, g, hΓ, hn, hok, hf, hj => by
    have hv := fresh_ty g hlv
    have f := h.good g.fresh hΓ.fresh hn
    have hf₁ := hf.beforeConstrain hc f.1 f.2.1.low
      (SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨hv.2, SFields.in_nil⟩, SType.in_abs⟩)
    have r := h.cert hcb hcl g.fresh hΓ.fresh hn (hok.ext .fresh) hf₁ hj
    exact ⟨r.1.constrain hc f.1.wf.scope hf.ext,
      .sel r.2 f.2.1.pre.ne_abs (accepts hcl hf.ext hc.logged) trivial⟩
  | .selOr (s := s₀) (l := l) _ hlv h hc hd hc', g, hΓ, hn, hok, hf, hj => by
    have hv := fresh_ty g hlv
    have f := h.good g.fresh hΓ.fresh hn
    have hres := hv.1.scope_mono h.to_ext.next
    have blow : (SType.record (.cons l (.opt (.var s₀.next)) .nil) .abs).In
        (fun w => L w ≤ lvl) :=
      SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨SType.in_opt.mpr hv.2, SFields.in_nil⟩,
        SType.in_abs⟩
    have fc := hc.good f.1 f.2.2 f.2.1.scope
      (SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨SType.in_opt.mpr hres, SFields.in_nil⟩,
        SType.in_abs⟩) f.2.1.low blow f.2.1.nac ⟨⟨trivial, trivial⟩, trivial⟩
    have fd := hd.good fc.1 fc.2 hn
    have hf₃ := hf.beforeConstrain hc' fd.1 fd.2.1.low hv.2
    have hf₂ := hf₃.beforeRun hd fc.1 fc.2
    have hf₁ := hf₂.beforeConstrain hc f.1 f.2.1.low blow
    have r := h.cert hcb hcl g.fresh hΓ.fresh hn (hok.ext .fresh) hf₁ hj
    have rd := hd.cert hcb hcl fc.1 fc.2 hn
      (hok.ext (Ext.fresh.trans (h.to_ext.trans hc.to_ext))) hf₃
      (r.1.constrain hc f.1.wf.scope hf₂.ext)
    exact ⟨rd.1.constrain hc' fd.1.wf.scope hf.ext,
      .selOr r.2 f.2.1.pre.ne_abs (accepts hcl hf₂.ext hc.logged) rd.2 fd.2.1.pre.ne_abs
        (accepts hcl hf.ext hc'.logged)⟩
  | .ext (s₂ := s₂) _ h₁ h₂ _ hlv hc, g, hΓ, hn, hok, hf, hj => by
    have f₁ := h₁.good g hΓ hn
    have f₂ := h₂.good f₁.1 f₁.2.2 hn
    have hρ := fresh_ty f₂.1 hlv
    have hf₂ := (hf.beforeConstrain hc f₂.1.fresh f₁.2.1.low
      (SType.in_record.mpr ⟨SFields.In.absOf, hρ.2⟩)).beforeFresh f₂.1
    have hf₁ := hf₂.beforeFields h₂ f₁.1 f₁.2.2
    have r₁ := h₁.cert hcb hcl g hΓ hn hok hf₁ hj
    have r₂ := h₂.cert hcb hcl f₁.1 f₁.2.2 hn (hok.ext h₁.to_ext) hf₂ r₁.1
    exact ⟨JustLoc.constrain (s := s₂.fresh) r₂.1 hc f₂.1.wf.scope.fresh hf.ext,
      .ext r₁.2 r₂.2 f₁.2.1.pre.ne_abs (accepts hcl hf.ext hc.logged)⟩
  | .extNil h, g, hΓ, hn, hok, hf, hj => by
    have r := h.cert hcb hcl g hΓ hn hok hf hj
    exact ⟨r.1, .extNil r.2⟩
  | .letIn (s := s₀) (s₁ := s₁) (x := x) h₁ h₂, g, hΓ, hn, hok, hf, hj => by
    have hL := g.level
    subst hL
    have f₁ := h₁.good g (hΓ.mono_lvl (Nat.le_succ lvl)) hn
    have fr := h₁.frame (lvl := lvl) g.wf hΓ.ctxIn
    -- the context of the body
    have hΓ₁ := (hΓ.run rfl g.wf h₁ f₁.1.wf).cons (x := x)
      (let_entry f₁.1.wf f₁.2.1.scope fr.2 fr.1.closed)
    have hn₁ := hn.cons (x := x) (e := .poly (genVars s₀.level s₀.next s₁.next lvl) _)
      f₁.2.1.nac f₁.2.1.pre
    -- the rest of the run, from the end of the right-hand side
    have hf₁ := hf.beforeRun h₂ f₁.1 hΓ₁
    have r₁ := h₁.cert hcb hcl g (hΓ.mono_lvl (Nat.le_succ lvl)) hn hok
      (hf₁.up f₁.1.wf.levels f₁.1.level) hj
    -- what is generalized is finished
    have fz := frozen_let hf g.wf.scope ((TypeTerm.letIn h₁ h₂).frame (lvl := lvl) g.wf hΓ.ctxIn).1
      (h₂.frameL f₁.1 hΓ₁) h₂.to_ext.next
    have r₂ := h₂.cert hcb hcl f₁.1 hΓ₁ hn₁
      ((hok.ext h₁.to_ext).cons (x := x) (e := .poly _ _) ⟨f₁.2.1.scope, fz⟩) hf r₁.1
    exact ⟨r₂.1, .letIn r₁.2 ⟨hcb ▸ fz.avoid, hok.avoids hcb g.wf.scope _⟩ r₂.2⟩
  | .letRec (s := s₀) (s₁ := s₁) (s₂ := s₂) (x := x) hfun _ hlv h₁ hc h₂, g, hΓ, hn, hok, hf, hj => by
    have hL := g.level
    subst hL
    have hv := fresh_ty g hlv
    have hΓr := ((hΓ.mono_lvl (Nat.le_succ lvl)).fresh).cons (x := x) (e := .mono _) hv
    have hnr := hn.cons (x := x) (e := .mono (.var s₀.next)) trivial trivial
    have f₁ := h₁.good g.fresh hΓr hnr
    have hvs := hv.1.scope_mono h₁.to_ext.next
    have win := letRec_window h₁ hc g.wf hΓ f₁.1.wf f₁.2.1.scope
    have g₂ : Good s₀.level s₂ := ⟨hc.to_ext.level.trans f₁.1.level, win.1, hc.inv₂ f₁.1.inv₂,
      hc.nac f₁.1.inv₂ f₁.2.1.nac trivial f₁.1.nac⟩
    have hn₂ := hn.cons (x := x)
      (e := .poly (genVars s₀.level s₀.next s₂.next lvl) (.var s₀.next)) trivial trivial
    -- the rest of the run, from the end of the right-hand side
    have hf₂ := hf.beforeRun h₂ g₂ win.2.2
    have hf₁ := (hf₂.up g₂.wf.levels g₂.level).beforeConstrain hc f₁.1 f₁.2.1.low hv.2
    have r₁ := h₁.cert hcb hcl g.fresh hΓr hnr
      ((hok.ext .fresh).cons (x := x) (e := .mono _) hv.1) hf₁ hj
    have j₂ := r₁.1.constrain hc f₁.1.wf.scope hf₂.ext
    -- what is generalized is finished
    have fz := frozen_let hf g.wf.scope
      ((TypeTerm.letRec hfun ‹_› hlv h₁ hc h₂).frame (lvl := lvl) g.wf hΓ.ctxIn).1
      (h₂.frameL g₂ win.2.2) h₂.to_ext.next
    have e₂ : Ext s₀ s₂ := Ext.fresh.trans (h₁.to_ext.trans hc.to_ext)
    have r₂ := h₂.cert hcb hcl g₂ win.2.2 hn₂
      ((hok.ext e₂).cons (x := x) (e := .poly _ _) ⟨hvs.scope_mono hc.to_ext.next, fz⟩) hf j₂
    exact ⟨r₂.1, .letRec hfun r₁.2 f₁.2.1.pre.ne_abs (accepts hcl hf₂.ext hc.logged)
      ⟨hcb ▸ fz.avoid, hok.avoids hcb g.wf.scope _⟩ r₂.2⟩
  | .ite _ hlv hc h₁ ha h₂ hb h₃, g, hΓ, hn, hok, hf, hj => by
    have hv := fresh_ty g hlv
    have fc := hc.good g.fresh hΓ.fresh hn
    have c₁ := h₁.good fc.1 fc.2.2 fc.2.1.scope SType.in_prim fc.2.1.low SType.in_prim fc.2.1.nac
      trivial
    have fa := ha.good c₁.1 c₁.2 hn
    have k₃ := Nat.le_trans hc.to_ext.next (Nat.le_trans h₁.to_ext.next ha.to_ext.next)
    have c₂ := h₂.good fa.1 fa.2.2 fa.2.1.scope (hv.1.scope_mono k₃) fa.2.1.low hv.2 fa.2.1.nac
      trivial
    have fb := hb.good c₂.1 c₂.2 hn
    have hf₅ := hf.beforeConstrain h₃ fb.1 fb.2.1.low hv.2
    have hf₄ := hf₅.beforeRun hb c₂.1 c₂.2
    have hf₃ := hf₄.beforeConstrain h₂ fa.1 fa.2.1.low hv.2
    have hf₂ := hf₃.beforeRun ha c₁.1 c₁.2
    have hf₁ := hf₂.beforeConstrain h₁ fc.1 fc.2.1.low SType.in_prim
    have e₂ := Ext.fresh.trans (hc.to_ext.trans h₁.to_ext)
    have rc := hc.cert hcb hcl g.fresh hΓ.fresh hn (hok.ext .fresh) hf₁ hj
    have ra := ha.cert hcb hcl c₁.1 c₁.2 hn (hok.ext e₂) hf₃
      (rc.1.constrain h₁ fc.1.wf.scope hf₂.ext)
    have rb := hb.cert hcb hcl c₂.1 c₂.2 hn (hok.ext (e₂.trans (ha.to_ext.trans h₂.to_ext))) hf₅
      (ra.1.constrain h₂ fa.1.wf.scope hf₄.ext)
    exact ⟨rb.1.constrain h₃ fb.1.wf.scope hf.ext,
      .ite rc.2 fc.2.1.pre.ne_abs (accepts hcl hf₂.ext h₁.logged) ra.2 fa.2.1.pre.ne_abs
        (accepts hcl hf₄.ext h₂.logged) rb.2 fb.2.1.pre.ne_abs (accepts hcl hf.ext h₃.logged)⟩
  | .fn hw hp h, g, hΓ, hn, hok, hf, hj => by
    have fp := hp.good g hΓ hn
    have rp := hp.cert hcb hcl g hΓ hn hok (hf.beforeRun h fp.1 fp.2.1) hj
    have r := h.cert hcb hcl fp.1 fp.2.1 fp.2.2 rp.2.2 hf rp.1
    exact ⟨r.1, .fn hw rp.2.1 r.2⟩

theorem TypeFields.cert (hcb : c.bounds = F.bounds) (hcl : ∀ p, p ∈ F.log → p ∈ c.log) :
    TypeFields Γ lvl s fs Fd s' → Good L s → CtxWF L lvl s Γ → CtxNAC Γ → CtxOk F s Γ →
    Fin F L lvl s' → JustLoc F s → JustLoc F s' ∧ PFields c Γ fs Fd
  | .nil, _, _, _, _, _, hj => ⟨hj, .nil⟩
  | .cons h₁ h₂, g, hΓ, hn, hok, hf, hj => by
    have f₁ := h₁.good g hΓ hn
    have r₁ := h₁.cert hcb hcl g hΓ hn hok (hf.beforeFields h₂ f₁.1 f₁.2.2) hj
    have r₂ := h₂.cert hcb hcl f₁.1 f₁.2.2 hn (hok.ext h₁.to_ext) hf r₁.1
    exact ⟨r₂.1, .cons r₁.2 f₁.2.1.pre r₂.2⟩

/-- Parameters: their skeleton, and the context of the body. -/
theorem TypeParams.cert (hcb : c.bounds = F.bounds) (hcl : ∀ p, p ∈ F.log → p ∈ c.log) :
    TypeParams Γ lvl s ps P Γ' s' → Good L s → CtxWF L lvl s Γ → CtxNAC Γ → CtxOk F s Γ →
    Fin F L lvl s' → JustLoc F s → JustLoc F s' ∧ PParams c Γ ps P Γ' ∧ CtxOk F s' Γ'
  | .nil, _, _, _, hok, _, hj => ⟨hj, .nil, hok⟩
  | .req (x := x) _ hlv h, g, hΓ, hn, hok, hf, hj => by
    have hv := fresh_ty g hlv
    have r := h.cert hcb hcl g.fresh (hΓ.fresh.cons (x := x) (e := .mono _) hv)
      (hn.cons (x := x) (e := .mono (.var _)) trivial trivial)
      ((hok.ext .fresh).cons (x := x) (e := .mono _) hv.1) hf hj
    exact ⟨r.1, .req r.2.1, r.2.2⟩
  | .dflt (x := x) _ hlv hd hc h, g, hΓ, hn, hok, hf, hj => by
    have hv := fresh_ty g hlv
    have fd := hd.good g.fresh hΓ.fresh hn
    have hvs := hv.1.scope_mono hd.to_ext.next
    have fc := hc.good fd.1 fd.2.2 fd.2.1.scope hvs fd.2.1.low hv.2 fd.2.1.nac trivial
    have hΓ₂ := fc.2.cons (x := x) (e := .mono _) ⟨hvs.scope_mono hc.to_ext.next, hv.2⟩
    have hf₂ := hf.beforeParams h fc.1 hΓ₂
    have hf₁ := hf₂.beforeConstrain hc fd.1 fd.2.1.low hv.2
    have rd := hd.cert hcb hcl g.fresh hΓ.fresh hn (hok.ext .fresh) hf₁ hj
    have r := h.cert hcb hcl fc.1 hΓ₂ (hn.cons (x := x) (e := .mono (.var _)) trivial trivial)
      ((hok.ext (Ext.fresh.trans (hd.to_ext.trans hc.to_ext))).cons (x := x) (e := .mono _)
        (hvs.scope_mono hc.to_ext.next))
      hf (rd.1.constrain hc fd.1.wf.scope hf₂.ext)
    exact ⟨r.1, .dflt rd.2 fd.2.1.pre.ne_abs (accepts hcl hf₂.ext hc.logged) r.2.1, r.2.2⟩
end

end

/-! ## From the initial state -/

theorem pbuiltins_ok {F s : State} : CtxOk F s pbuiltins := by
  intro p hp
  simp only [pbuiltins, builtins, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    exact fun w hw => by simp [SType.vars, SParams.vars, builtinSig] at hw

/-- **Adequacy**: an accepted run yields a valid certificate, with a
typing skeleton with let-polymorphism for the term at the inferred type. -/
theorem TypeTerm.certificate {K : Nat → List String} {L : Nat → Nat}
    (h : TypeTerm pbuiltins 0 (State.initKL K L) t st s') (hr : StructRanked s'.bounds r) :
    (s'.certificate r).Valid ∧ PTyp (s'.certificate r) pbuiltins t st := by
  have g₀ : Good L (State.initKL K L) := ⟨rfl, .init, .init, .init⟩
  have f := h.good g₀ pbuiltins_wf pbuiltins_NAC
  have hfin : Fin s' L 0 s' := by
    have := Fin.final f.1.wf 0
    rwa [f.1.level] at this
  have r := h.cert (c := s'.certificate r) (State.certificate_bounds f.1.inv₂) (fun _ hp => hp)
    g₀ pbuiltins_wf pbuiltins_NAC pbuiltins_ok hfin (fun _ h => nomatch h)
  exact ⟨State.certificate_valid ⟨fun p hp => .inr (r.1 p hp), f.1.wf.cons⟩ f.1.inv₂ f.1.nac
    (h.kinds pbuiltins_K .init .init).1 hr, r.2⟩

/-- **Theorem 1** (soundness of type inference, with let-polymorphism): if
the algorithm types `t` with `st` from the built-ins, for the kinds `K`
and the levels `L` of its run, then `t` has the type `st` in the
declarative system with constrained schemes, over the solution of the
run's certificate, which has no recursive types. -/
theorem theorem1 {K : Nat → List String} {L : Nat → Nat} (h : Infers K L t st s') :
    ∃ c : Certificate,
      Typ (defsOf c.state) (pbuiltins.toCtx c.bounds .gv) t st.toTy ∧
        ∃ r, Defs.Ranked (defsOf c.state) r := by
  obtain ⟨h, r, hr⟩ := h
  have hc := h.certificate hr
  exact ⟨_, PTyp.sound_top hc.1 hc.2, _, hc.1.nonrec⟩

end BoltCore.Alg
