import BoltCore.Soundness

/-!
# Typing with levels: what a run leaves alone

`let` generalizes the variables above its level that its right-hand side
allocated. This is sound because nothing else mentions them, and nothing
will: this file proves the facts behind that.

* **Locality** (`TypeTerm.local`): a set of variables that is closed under
  bounds, contains the variables of the context and every variable
  allocated from now on, stays closed across a run, and the bounds of the
  variables outside it are untouched.
* **Frames** (`Frame`, `TypeTerm.frame`): the instance for the variables
  of level at most `lvl` and those allocated from `n` on. A run at level
  `lvl` or above, in a context of level at most `lvl`, leaves the variables
  above `lvl` that were there before alone.
* **The allocation invariants** (`TypeTerm.wf`): every state a run reaches
  is in scope, its bounds have the levels of their variables and are
  consistent, and the inferred type is in scope, of level at most the
  current level.
-/

namespace BoltCore.Alg

open State

/-! ## Growth across a run -/

/-- The bounds and the log only grow, the kinds and levels stay, and no
variable is freed. (The cache is reset by each `constrain`.) -/
structure Ext (s s' : State) : Prop where
  lower : ∀ v x, x ∈ (s.bounds v).lower → x ∈ (s'.bounds v).lower
  upper : ∀ v x, x ∈ (s.bounds v).upper → x ∈ (s'.bounds v).upper
  log : ∀ p, p ∈ s.log → p ∈ s'.log
  kind : s'.kind = s.kind
  level : s'.level = s.level
  next : s.next ≤ s'.next

namespace Ext

theorem refl : Ext s s := ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, rfl, rfl, Nat.le_refl _⟩

theorem trans (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) : Ext s₁ s₃ :=
  ⟨fun v x h => h₂.lower v x (h₁.lower v x h), fun v x h => h₂.upper v x (h₁.upper v x h),
    fun p h => h₂.log p (h₁.log p h), h₂.kind.trans h₁.kind, h₂.level.trans h₁.level,
    Nat.le_trans h₁.next h₂.next⟩

theorem of_grows (g : Grows s s') (hn : s.next ≤ s'.next) : Ext s s' :=
  ⟨g.lower, g.upper, g.log, g.kind, g.level, hn⟩

theorem fresh : Ext s s.fresh :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, rfl, rfl, Nat.le_succ _⟩

end Ext

theorem ConstrainTop.to_ext {s s' : State} {a b : SType} (h : ConstrainTop s a b s') : Ext s s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  have g := hc.grows
  exact ⟨g.lower, g.upper, g.log, g.kind, g.level, hc.keeps.next⟩

mutual
theorem TypeTerm.to_ext : TypeTerm Γ lvl s t st s' → Ext s s'
  | .lit | .var _ => .refl
  | .inst _ _ => .of_grows .instantiate (Nat.le_add_right _ _)
  | .lam _ _ h => Ext.fresh.trans h.to_ext
  | .app _ _ h₁ h₂ hc => (Ext.fresh.trans h₁.to_ext).trans (h₂.to_ext.trans hc.to_ext)
  | .rcd h => h.to_ext
  | .sel _ _ h hc => (Ext.fresh.trans h.to_ext).trans hc.to_ext
  | .selOr _ _ h hc hd hc' =>
    (Ext.fresh.trans h.to_ext).trans (hc.to_ext.trans (hd.to_ext.trans hc'.to_ext))
  | .ext _ h₁ h₂ _ _ hc => (h₁.to_ext.trans h₂.to_ext).trans (Ext.fresh.trans hc.to_ext)
  | .extNil h => h.to_ext
  | .letIn h₁ h₂ => h₁.to_ext.trans h₂.to_ext
  | .letRec _ _ _ h₁ hc h₂ => (Ext.fresh.trans h₁.to_ext).trans (hc.to_ext.trans h₂.to_ext)
  | .ite _ _ hc h₁ ha h₂ hb h₃ =>
    (Ext.fresh.trans hc.to_ext).trans
      (h₁.to_ext.trans (ha.to_ext.trans (h₂.to_ext.trans (hb.to_ext.trans h₃.to_ext))))
  | .fn _ hp h => hp.to_ext.trans h.to_ext

theorem TypeFields.to_ext : TypeFields Γ lvl s fs F s' → Ext s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.to_ext.trans h₂.to_ext

theorem TypeParams.to_ext : TypeParams Γ lvl s ps P Γ' s' → Ext s s'
  | .nil => .refl
  | .req _ _ h => Ext.fresh.trans h.to_ext
  | .dflt _ _ hd hc h => (Ext.fresh.trans hd.to_ext).trans (hc.to_ext.trans h.to_ext)
end

theorem TypeTerm.log_grows (h : TypeTerm Γ lvl s t st s') : ∀ p, p ∈ s.log → p ∈ s'.log :=
  h.to_ext.log

/-! ## Contexts in a set of variables -/

/-- The entry only mentions variables of `X`, other than those it
generalizes. -/
def CEntry.In (X : Nat → Prop) (s : State) : CEntry → Prop
  | .mono st => st.In X
  | .poly gen st => SchemeIn X s gen st

def CtxIn (X : Nat → Prop) (s : State) (Γ : PCtx) : Prop :=
  ∀ x e, Γ.lookup x = some e → e.In X s

section
variable {X Y : Nat → Prop}

theorem PCtx.lookup_cons {Γ : PCtx} {x y : String} {e e' : CEntry}
    (h : PCtx.lookup ((x, e) :: Γ) y = some e') : (x = y ∧ e' = e) ∨ Γ.lookup y = some e' := by
  simp only [PCtx.lookup, List.find?_cons] at h
  by_cases hxy : x = y
  · simp [hxy] at h; exact .inl ⟨hxy, h.symm⟩
  · simp only [hxy, decide_false] at h; exact .inr h

theorem CtxIn.cons {s : State} {Γ : PCtx} {x : String} {e : CEntry} (h : CtxIn X s Γ)
    (he : e.In X s) : CtxIn X s ((x, e) :: Γ) := by
  intro y e' hy
  rcases PCtx.lookup_cons hy with ⟨_, rfl⟩ | hy
  · exact he
  · exact h y e' hy

theorem CEntry.In.mono {s : State} (hxy : ∀ w, X w → Y w) : ∀ {e : CEntry}, e.In X s → e.In Y s
  | .mono _, h => SType.In.mono hxy h
  | .poly _ _, h =>
    ⟨fun w hw hg => hxy w (h.ty w hw hg), fun α hα b hb w hw hg => hxy w (h.bounds α hα b hb w hw hg)⟩

theorem CtxIn.mono {s : State} {Γ : PCtx} (h : CtxIn X s Γ) (hxy : ∀ w, X w → Y w) : CtxIn Y s Γ :=
  fun x e hx => (h x e hx).mono hxy

/-- An entry stays in a closed set across a run that is local to it: a
generalized variable in the set has its bounds in the set, and one outside
it has the bounds it had. -/
theorem CEntry.In.local [DecidablePred X] {s s' : State} (l : Local X s s') :
    ∀ {e : CEntry}, e.In X s → e.In X s'
  | .mono _, h => h
  | .poly _ _, h =>
    ⟨h.ty, fun α hα b hb w hw hg => by
      by_cases hx : X α
      · exact l.closed α hx b hb w hw
      · rw [l.frame α hx] at hb; exact h.bounds α hα b hb w hw hg⟩

theorem CtxIn.local [DecidablePred X] {s s' : State} {Γ : PCtx} (l : Local X s s')
    (h : CtxIn X s Γ) : CtxIn X s' Γ := fun x e hx => (h x e hx).local l

/-! ## Locality of typing -/

theorem ConstrainTop.local {s s' : State} {a b : SType} (h : ConstrainTop s a b s')
    (hup : ∀ w, s.next ≤ w → X w) (ha : a.In X) (hb : b.In X) (hx : XClosed X s)
    (he : ExpsIn X s) : Local X s s' ∧ ExpsNew X s s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  have r := hc.local (X := X) (fun w hw _ => hup w hw) ha hb hx he
  exact ⟨⟨r.1.closed, r.1.frame⟩, r.2⟩

theorem Local.fresh {s : State} (hx : XClosed X s) : Local X s s.fresh := ⟨hx, fun _ _ => rfl⟩

mutual
/-- **Locality of typing.** -/
theorem TypeTerm.local [DecidablePred X] : TypeTerm Γ lvl s t st s' → (∀ w, s.next ≤ w → X w) →
    CtxIn X s Γ → XClosed X s → ExpsIn X s → Local X s s' ∧ ExpsNew X s s' ∧ st.In X
  | .lit, _, _, hx, _ => ⟨.refl hx, .refl, SType.in_prim⟩
  | .var hl, _, hΓ, hx, _ => ⟨.refl hx, .refl, hΓ _ _ hl⟩
  | .inst hl hi, hup, hΓ, hx, _ => by
    have hc : ∀ α ∈ _, X _ := fun α hα => hup _ (hi.fresh α hα).1
    have hsch : SchemeIn X _ _ _ := hΓ _ _ hl
    exact ⟨Local.instantiate hx hi hc hsch, .of_eq rfl, in_rename_of hi hc hsch.ty⟩
  | .lam (s := s₀) _ _ h, hup, hΓ, hx, he => by
    have hv : X s₀.next := hup _ (Nat.le_refl _)
    have l₀ := Local.fresh hx
    have r := h.local (fun w hw => hup w (Nat.le_of_succ_le hw))
      ((hΓ.local l₀).cons (SType.in_var.mpr hv)) hx he
    exact ⟨l₀.trans r.1, r.2.1, SType.in_arrow.mpr ⟨SType.in_var.mpr hv, r.2.2⟩⟩
  | .app (s := s₀) _ _ h₁ h₂ hc, hup, hΓ, hx, he => by
    have hv : X s₀.next := hup _ (Nat.le_refl _)
    have l₀ := Local.fresh hx
    have r₁ := h₁.local (fun w hw => hup w (Nat.le_of_succ_le hw)) (hΓ.local l₀) hx he
    have n₁ := Nat.le_trans (Nat.le_succ _) h₁.to_ext.next
    have r₂ := h₂.local (fun w hw => hup w (Nat.le_trans n₁ hw)) (hΓ.local (l₀.trans r₁.1))
      r₁.1.closed (he.of_new r₁.2.1)
    have r₃ := hc.local (fun w hw => hup w (Nat.le_trans (Nat.le_trans n₁ h₂.to_ext.next) hw))
      r₁.2.2 (SType.in_arrow.mpr ⟨r₂.2.2, SType.in_var.mpr hv⟩) r₂.1.closed
      (he.of_new (r₁.2.1.trans r₂.2.1))
    exact ⟨l₀.trans (r₁.1.trans (r₂.1.trans r₃.1)), r₁.2.1.trans (r₂.2.1.trans r₃.2),
      SType.in_var.mpr hv⟩
  | .rcd h, hup, hΓ, hx, he => by
    have r := h.local hup hΓ hx he
    exact ⟨r.1, r.2.1, SType.in_record.mpr ⟨r.2.2, SType.in_nil⟩⟩
  | .sel (s := s₀) _ _ h hc, hup, hΓ, hx, he => by
    have hv : X s₀.next := hup _ (Nat.le_refl _)
    have l₀ := Local.fresh hx
    have r₁ := h.local (fun w hw => hup w (Nat.le_of_succ_le hw)) (hΓ.local l₀) hx he
    have n₁ := Nat.le_trans (Nat.le_succ _) h.to_ext.next
    have r₂ := hc.local (fun w hw => hup w (Nat.le_trans n₁ hw)) r₁.2.2
      (SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨SType.in_var.mpr hv, SFields.in_nil⟩,
        SType.in_abs⟩) r₁.1.closed (he.of_new r₁.2.1)
    exact ⟨l₀.trans (r₁.1.trans r₂.1), r₁.2.1.trans r₂.2, SType.in_var.mpr hv⟩
  | .selOr (s := s₀) _ _ h hc hd hc', hup, hΓ, hx, he => by
    have hv : X s₀.next := hup _ (Nat.le_refl _)
    have l₀ := Local.fresh hx
    have r₁ := h.local (fun w hw => hup w (Nat.le_of_succ_le hw)) (hΓ.local l₀) hx he
    have n₁ := Nat.le_trans (Nat.le_succ _) h.to_ext.next
    have r₂ := hc.local (fun w hw => hup w (Nat.le_trans n₁ hw)) r₁.2.2
      (SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨SType.in_opt.mpr (SType.in_var.mpr hv),
        SFields.in_nil⟩, SType.in_abs⟩) r₁.1.closed (he.of_new r₁.2.1)
    have n₂ := Nat.le_trans n₁ hc.to_ext.next
    have l₂ := l₀.trans (r₁.1.trans r₂.1)
    have e₂ := r₁.2.1.trans r₂.2
    have r₃ := hd.local (fun w hw => hup w (Nat.le_trans n₂ hw)) (hΓ.local l₂) l₂.closed
      (he.of_new e₂)
    have r₄ := hc'.local (fun w hw => hup w (Nat.le_trans (Nat.le_trans n₂ hd.to_ext.next) hw))
      r₃.2.2 (SType.in_var.mpr hv) r₃.1.closed (he.of_new (e₂.trans r₃.2.1))
    exact ⟨l₂.trans (r₃.1.trans r₄.1), e₂.trans (r₃.2.1.trans r₄.2), SType.in_var.mpr hv⟩
  | .ext (s₂ := s₂) _ h₁ h₂ _ _ hc, hup, hΓ, hx, he => by
    have r₁ := h₁.local hup hΓ hx he
    have r₂ := h₂.local (fun w hw => hup w (Nat.le_trans h₁.to_ext.next hw)) (hΓ.local r₁.1)
      r₁.1.closed (he.of_new r₁.2.1)
    have n₂ := Nat.le_trans h₁.to_ext.next h₂.to_ext.next
    have hv : X s₂.next := hup _ n₂
    have l₂ := r₁.1.trans r₂.1
    have r₃ := hc.local (fun w hw => hup w (Nat.le_trans n₂ (Nat.le_of_succ_le hw))) r₁.2.2
      (SType.in_record.mpr ⟨SFields.In.absOf, SType.in_var.mpr hv⟩) l₂.closed
      (he.of_new (r₁.2.1.trans r₂.2.1))
    exact ⟨l₂.trans (Local.trans (Local.fresh l₂.closed) r₃.1),
      r₁.2.1.trans (r₂.2.1.trans r₃.2), SType.in_record.mpr ⟨r₂.2.2, SType.in_var.mpr hv⟩⟩
  | .extNil h, hup, hΓ, hx, he => h.local hup hΓ hx he
  | .letIn (s := s₀) (s₁ := s₁) h₁ h₂, hup, hΓ, hx, he => by
    have r₁ := h₁.local hup hΓ hx he
    -- the generalized variables were allocated by the right-hand side
    have hsch : SchemeIn X s₁ (genVars s₀.level s₀.next s₁.next lvl) _ :=
      ⟨fun w hw _ => r₁.2.2 w hw, fun α hα b hb w hw _ =>
        r₁.1.closed α (hup α (mem_genVars.mp hα).1) b hb w hw⟩
    have r₂ := h₂.local (fun w hw => hup w (Nat.le_trans h₁.to_ext.next hw))
      ((hΓ.local r₁.1).cons hsch) r₁.1.closed (he.of_new r₁.2.1)
    exact ⟨r₁.1.trans r₂.1, r₁.2.1.trans r₂.2.1, r₂.2.2⟩
  | .letRec (s := s₀) (s₂ := s₂) _ _ _ h₁ hc h₂, hup, hΓ, hx, he => by
    have hv : X s₀.next := hup _ (Nat.le_refl _)
    have l₀ := Local.fresh hx
    have r₁ := h₁.local (fun w hw => hup w (Nat.le_of_succ_le hw))
      ((hΓ.local l₀).cons (SType.in_var.mpr hv)) hx he
    have n₁ := Nat.le_trans (Nat.le_succ _) h₁.to_ext.next
    have r₂ := hc.local (fun w hw => hup w (Nat.le_trans n₁ hw)) r₁.2.2 (SType.in_var.mpr hv)
      r₁.1.closed (he.of_new r₁.2.1)
    have l₂ := l₀.trans (r₁.1.trans r₂.1)
    have e₂ := r₁.2.1.trans r₂.2
    have hsch : SchemeIn X s₂ (genVars s₀.level s₀.next s₂.next lvl) (.var s₀.next) :=
      ⟨fun w hw _ => SType.in_var.mpr hv w hw, fun α hα b hb w hw _ =>
        l₂.closed α (hup α (mem_genVars.mp hα).1) b hb w hw⟩
    have r₃ := h₂.local (fun w hw => hup w (Nat.le_trans (Nat.le_trans n₁ hc.to_ext.next) hw))
      ((hΓ.local l₂).cons hsch) l₂.closed (he.of_new e₂)
    exact ⟨l₂.trans r₃.1, e₂.trans r₃.2.1, r₃.2.2⟩
  | .ite (s := s₀) _ _ hc h₁ ha h₂ hb h₃, hup, hΓ, hx, he => by
    have hv : X s₀.next := hup _ (Nat.le_refl _)
    have l₀ := Local.fresh hx
    have r₁ := hc.local (fun w hw => hup w (Nat.le_of_succ_le hw)) (hΓ.local l₀) hx he
    have n₁ := Nat.le_trans (Nat.le_succ _) hc.to_ext.next
    have r₂ := h₁.local (fun w hw => hup w (Nat.le_trans n₁ hw)) r₁.2.2 SType.in_prim
      r₁.1.closed (he.of_new r₁.2.1)
    have n₂ := Nat.le_trans n₁ h₁.to_ext.next
    have l₂ := l₀.trans (r₁.1.trans r₂.1)
    have e₂ := r₁.2.1.trans r₂.2
    have r₃ := ha.local (fun w hw => hup w (Nat.le_trans n₂ hw)) (hΓ.local l₂) l₂.closed
      (he.of_new e₂)
    have n₃ := Nat.le_trans n₂ ha.to_ext.next
    have r₄ := h₂.local (fun w hw => hup w (Nat.le_trans n₃ hw)) r₃.2.2 (SType.in_var.mpr hv)
      r₃.1.closed (he.of_new (e₂.trans r₃.2.1))
    have n₄ := Nat.le_trans n₃ h₂.to_ext.next
    have l₄ := l₂.trans (r₃.1.trans r₄.1)
    have e₄ := e₂.trans (r₃.2.1.trans r₄.2)
    have r₅ := hb.local (fun w hw => hup w (Nat.le_trans n₄ hw)) (hΓ.local l₄) l₄.closed
      (he.of_new e₄)
    have r₆ := h₃.local (fun w hw => hup w (Nat.le_trans (Nat.le_trans n₄ hb.to_ext.next) hw))
      r₅.2.2 (SType.in_var.mpr hv) r₅.1.closed (he.of_new (e₄.trans r₅.2.1))
    exact ⟨l₄.trans (r₅.1.trans r₆.1), e₄.trans (r₅.2.1.trans r₆.2), SType.in_var.mpr hv⟩
  | .fn _ hp h, hup, hΓ, hx, he => by
    have rp := hp.local hup hΓ hx he
    have r := h.local (fun w hw => hup w (Nat.le_trans hp.to_ext.next hw)) rp.2.2.2 rp.1.closed
      (he.of_new rp.2.1)
    exact ⟨rp.1.trans r.1, rp.2.1.trans r.2.1,
      SType.in_arrow.mpr ⟨SType.in_sig.mpr rp.2.2.1, r.2.2⟩⟩

theorem TypeFields.local [DecidablePred X] : TypeFields Γ lvl s fs F s' →
    (∀ w, s.next ≤ w → X w) → CtxIn X s Γ → XClosed X s → ExpsIn X s →
    Local X s s' ∧ ExpsNew X s s' ∧ F.In X
  | .nil, _, _, hx, _ => ⟨.refl hx, .refl, SFields.in_nil⟩
  | .cons h₁ h₂, hup, hΓ, hx, he => by
    have r₁ := h₁.local hup hΓ hx he
    have r₂ := h₂.local (fun w hw => hup w (Nat.le_trans h₁.to_ext.next hw)) (hΓ.local r₁.1)
      r₁.1.closed (he.of_new r₁.2.1)
    exact ⟨r₁.1.trans r₂.1, r₁.2.1.trans r₂.2.1, SFields.in_cons.mpr ⟨r₁.2.2, r₂.2.2⟩⟩

theorem TypeParams.local [DecidablePred X] : TypeParams Γ lvl s ps P Γ' s' →
    (∀ w, s.next ≤ w → X w) → CtxIn X s Γ → XClosed X s → ExpsIn X s →
    Local X s s' ∧ ExpsNew X s s' ∧ P.In X ∧ CtxIn X s' Γ'
  | .nil, _, hΓ, hx, _ => ⟨.refl hx, .refl, SParams.in_nil, hΓ⟩
  | .req (s := s₀) _ _ h, hup, hΓ, hx, he => by
    have hv : X s₀.next := hup _ (Nat.le_refl _)
    have l₀ := Local.fresh hx
    have r := h.local (fun w hw => hup w (Nat.le_of_succ_le hw))
      ((hΓ.local l₀).cons (SType.in_var.mpr hv)) hx he
    exact ⟨l₀.trans r.1, r.2.1, SParams.in_cons.mpr ⟨SType.in_var.mpr hv, r.2.2.1⟩, r.2.2.2⟩
  | .dflt (s := s₀) _ _ hd hc h, hup, hΓ, hx, he => by
    have hv : X s₀.next := hup _ (Nat.le_refl _)
    have l₀ := Local.fresh hx
    have r₁ := hd.local (fun w hw => hup w (Nat.le_of_succ_le hw)) (hΓ.local l₀) hx he
    have n₁ := Nat.le_trans (Nat.le_succ _) hd.to_ext.next
    have r₂ := hc.local (fun w hw => hup w (Nat.le_trans n₁ hw)) r₁.2.2 (SType.in_var.mpr hv)
      r₁.1.closed (he.of_new r₁.2.1)
    have l₂ := l₀.trans (r₁.1.trans r₂.1)
    have e₂ := r₁.2.1.trans r₂.2
    have r₃ := h.local (fun w hw => hup w (Nat.le_trans (Nat.le_trans n₁ hc.to_ext.next) hw))
      ((hΓ.local l₂).cons (SType.in_var.mpr hv)) l₂.closed (he.of_new e₂)
    exact ⟨l₂.trans r₃.1, e₂.trans r₃.2.1,
      SParams.in_cons.mpr ⟨SType.in_var.mpr hv, r₃.2.2.1⟩, r₃.2.2.2⟩
end

end

/-! ## Frames -/

/-- The variables allocated from `n` on, and those of level at most
`lvl`. -/
def Frame (L : Nat → Nat) (n lvl : Nat) (w : Nat) : Prop := n ≤ w ∨ L w ≤ lvl

instance (L : Nat → Nat) (n lvl : Nat) : DecidablePred (Frame L n lvl) :=
  fun w => inferInstanceAs (Decidable (n ≤ w ∨ L w ≤ lvl))

/-- The allocation invariants of a state: it is in scope, its bounds have
at most the levels of their variables, and they are consistent. -/
structure WF (s : State) : Prop where
  scope : Scope s
  levels : LevelInv s
  cons : Consistent s

theorem WF.fresh {s : State} (h : WF s) : WF s.fresh := ⟨h.scope.fresh, h.levels, h.cons⟩

/-- The frame at the counter of a well-formed state is closed: a variable
that is not allocated has no bounds, and a bound has at most the level of
its variable. -/
theorem WF.closed {s : State} (h : WF s) (lvl : Nat) : XClosed (Frame s.level s.next lvl) s := by
  intro v hv b hb
  rcases hv with hv | hv
  · exact absurd (h.scope.bounds v b hb).1 (Nat.not_lt.mpr hv)
  · exact (SType.level_le.mp (Nat.le_trans (h.levels v b hb) hv)).mono fun _ hw => .inr hw

theorem WF.expsIn {s : State} (h : WF s) (lvl : Nat) : ExpsIn (Frame s.level s.next lvl) s := by
  intro v L r hm hv
  rcases hv with hv | hv
  · exact absurd (h.scope.exps _ hm).1 (Nat.not_lt.mpr hv)
  · exact .inr (by rw [h.scope.expLevel v L r hm]; exact hv)

/-- **A run leaves the variables above a level alone**, when its context
is of that level at most: the frame of the level stays closed, the bounds
of the variables outside it are untouched, and the inferred type is in
it. -/
theorem TypeTerm.frame {lvl : Nat} (h : TypeTerm Γ lvl' s t st s') (w : WF s)
    (hΓ : CtxIn (fun v => s.level v ≤ lvl) s Γ) :
    Local (Frame s.level s.next lvl) s s' ∧ st.In (Frame s.level s.next lvl) := by
  have r := h.local (X := Frame s.level s.next lvl) (fun _ hw => .inl hw)
    (hΓ.mono fun _ hw => .inr hw) (w.closed lvl) (w.expsIn lvl)
  exact ⟨r.1, r.2.2⟩

theorem TypeFields.frame {lvl : Nat} (h : TypeFields Γ lvl' s fs F s') (w : WF s)
    (hΓ : CtxIn (fun v => s.level v ≤ lvl) s Γ) : Local (Frame s.level s.next lvl) s s' :=
  (h.local (X := Frame s.level s.next lvl) (fun _ hw => .inl hw)
    (hΓ.mono fun _ hw => .inr hw) (w.closed lvl) (w.expsIn lvl)).1

theorem TypeParams.frame {lvl : Nat} (h : TypeParams Γ lvl' s ps P Γ' s') (w : WF s)
    (hΓ : CtxIn (fun v => s.level v ≤ lvl) s Γ) : Local (Frame s.level s.next lvl) s s' :=
  (h.local (X := Frame s.level s.next lvl) (fun _ hw => .inl hw)
    (hΓ.mono fun _ hw => .inr hw) (w.closed lvl) (w.expsIn lvl)).1

theorem ConstrainTop.frame {s s' : State} {a b : SType} {lvl : Nat} (h : ConstrainTop s a b s')
    (w : WF s) (ha : a.In (fun v => s.level v ≤ lvl)) (hb : b.In (fun v => s.level v ≤ lvl)) :
    Local (Frame s.level s.next lvl) s s' :=
  (h.local (X := Frame s.level s.next lvl) (fun _ hw => .inl hw) (ha.mono fun _ hw => .inr hw)
    (hb.mono fun _ hw => .inr hw) (w.closed lvl) (w.expsIn lvl)).1

theorem ConstrainTop.wf {s s' : State} {a b : SType} (h : ConstrainTop s a b s') (w : WF s)
    (ha : a.In (· < s.next)) (hb : b.In (· < s.next)) : WF s' :=
  ⟨h.scope w.scope ha hb, h.levels w.levels, h.consistent w.scope ha hb w.cons⟩

/-! ## Well-formed contexts -/

/-- An entry at level `lvl`: it is in scope, and outside what it
generalizes it only mentions variables of level at most `lvl`. -/
def CEntry.WF (L : Nat → Nat) (lvl : Nat) (s : State) : CEntry → Prop
  | .mono st => st.In (· < s.next) ∧ st.In (fun w => L w ≤ lvl)
  | .poly gen st =>
    st.In (· < s.next) ∧ (∀ α ∈ gen, α < s.next) ∧ SchemeIn (fun w => L w ≤ lvl) s gen st

def CtxWF (L : Nat → Nat) (lvl : Nat) (s : State) (Γ : PCtx) : Prop :=
  ∀ x e, Γ.lookup x = some e → e.WF L lvl s

section
variable {L : Nat → Nat} {lvl : Nat}

theorem CtxWF.cons {s : State} {Γ : PCtx} {x : String} {e : CEntry} (h : CtxWF L lvl s Γ)
    (he : e.WF L lvl s) : CtxWF L lvl s ((x, e) :: Γ) := by
  intro y e' hy
  rcases PCtx.lookup_cons hy with ⟨_, rfl⟩ | hy
  · exact he
  · exact h y e' hy

theorem CtxWF.ctxIn {s : State} {Γ : PCtx} (h : CtxWF L lvl s Γ) :
    CtxIn (fun w => L w ≤ lvl) s Γ := fun x e hx => by
  have := h x e hx
  cases e with
  | mono st => exact this.2
  | poly gen st => exact this.2.2

theorem CtxWF.mono_lvl {s : State} {Γ : PCtx} {lvl' : Nat} (h : CtxWF L lvl s Γ)
    (hl : lvl ≤ lvl') : CtxWF L lvl' s Γ := fun x e hx => by
  have := h x e hx
  cases e with
  | mono st => exact ⟨this.1, this.2.mono fun _ hw => Nat.le_trans hw hl⟩
  | poly gen st =>
    exact ⟨this.1, this.2.1,
      (CEntry.In.mono (e := .poly gen st) (fun _ hw => Nat.le_trans hw hl) this.2.2)⟩

theorem CtxWF.fresh {s : State} {Γ : PCtx} (h : CtxWF L lvl s Γ) : CtxWF L lvl s.fresh Γ :=
  fun x e hx => by
    have := h x e hx
    cases e with
    | mono st => exact ⟨this.1.scope_mono (Nat.le_succ _), this.2⟩
    | poly gen st =>
      exact ⟨this.1.scope_mono (Nat.le_succ _), fun α hα => Nat.lt_succ_of_lt (this.2.1 α hα),
        this.2.2.ty, this.2.2.bounds⟩

/-- A well-formed context stays well-formed across a run that leaves its
frame alone: a generalized variable of low level has bounds of low level,
and one above has the bounds it had. -/
theorem CtxWF.step {s s' : State} {Γ : PCtx} (h : CtxWF L lvl s Γ) (hL' : s'.level = L)
    (hn : s.next ≤ s'.next) (hl : LevelInv s') (l : Local (Frame L s.next lvl) s s') :
    CtxWF L lvl s' Γ := fun x e hx => by
  have := h x e hx
  cases e with
  | mono st => exact ⟨this.1.scope_mono hn, this.2⟩
  | poly gen st =>
    refine ⟨this.1.scope_mono hn, fun α hα => Nat.lt_of_lt_of_le (this.2.1 α hα) hn, this.2.2.ty,
      fun α hα b hb w hw hg => ?_⟩
    by_cases hα' : L α ≤ lvl
    · have hbl := hl α b hb
      rw [hL'] at hbl
      exact SType.level_le.mp (Nat.le_trans hbl hα') w hw
    · have hf : ¬ Frame L s.next lvl α := fun hf =>
        hf.elim (fun hf => absurd (this.2.1 α hα) (Nat.not_lt.mpr hf)) hα'
      rw [l.frame α hf] at hb
      exact this.2.2.bounds α hα b hb w hw hg

/-- Across a run in the same context. -/
theorem CtxWF.run {s s' : State} {Γ : PCtx} (hΓ : CtxWF L lvl s Γ) (hL : s.level = L) (w : WF s)
    (h : TypeTerm Γ lvl' s t st s') (w' : WF s') : CtxWF L lvl s' Γ := by
  subst hL
  exact hΓ.step h.to_ext.level h.to_ext.next w'.levels (h.frame w hΓ.ctxIn).1

theorem CtxWF.runFields {s s' : State} {Γ : PCtx} (hΓ : CtxWF L lvl s Γ) (hL : s.level = L)
    (w : WF s) (h : TypeFields Γ lvl' s fs F s') (w' : WF s') : CtxWF L lvl s' Γ := by
  subst hL
  exact hΓ.step h.to_ext.level h.to_ext.next w'.levels (h.frame w hΓ.ctxIn)

/-- Across a top-level `constrain` on types of level at most `lvl`. -/
theorem CtxWF.constrain {s s' : State} {Γ : PCtx} {a b : SType} (hΓ : CtxWF L lvl s Γ)
    (hL : s.level = L) (w : WF s) (h : ConstrainTop s a b s') (w' : WF s')
    (ha : a.In (fun v => L v ≤ lvl)) (hb : b.In (fun v => L v ≤ lvl)) : CtxWF L lvl s' Γ := by
  subst hL
  exact hΓ.step h.to_ext.level h.to_ext.next w'.levels (h.frame w ha hb)

/-- The variables of a frame that are allocated and not generalized have a
low level. -/
theorem frame_low {n m w : Nat} (hw : Frame L n lvl w) (hlt : w < m)
    (hg : w ∉ genVars L n m lvl) : L w ≤ lvl := by
  rcases hw with hw | hw
  · exact Nat.le_of_not_lt fun h => hg (mem_genVars.mpr ⟨hw, hlt, h⟩)
  · exact hw

/-- The scheme of a `let` is a well-formed entry: its type and the bounds
of its generalized variables are in the frame of the right-hand side. -/
theorem let_entry {s₁ : State} {n : Nat} {st : SType} (w₁ : WF s₁) (hst : st.In (· < s₁.next))
    (hf : st.In (Frame L n lvl)) (hx : XClosed (Frame L n lvl) s₁) :
    (CEntry.poly (genVars L n s₁.next lvl) st).WF L lvl s₁ :=
  ⟨hst, fun _ hα => (mem_genVars.mp hα).2.1,
    fun w hw hg => frame_low (hf w hw) (hst w hw) hg,
    fun α hα b hb w hw hg =>
      frame_low (hx α (.inl (mem_genVars.mp hα).1) b hb w hw) ((w₁.scope.bounds α b hb).2 w hw) hg⟩

end

/-- The window of a `let rec`: across its right-hand side and the
constraint on its own name, the frame of the `let` stays closed, and the
scheme is a well-formed entry. -/
theorem letRec_window {s₀ s₁ s₂ : State} {Γ : PCtx} {x : String} {r : Term} {inf : SType}
    {lvl : Nat} (h₁ : TypeTerm ((x, .mono (.var s₀.next)) :: Γ) (lvl + 1) s₀.fresh r inf s₁)
    (hc : ConstrainTop s₁ inf (.var s₀.next) s₂) (w : WF s₀) (hΓ : CtxWF s₀.level lvl s₀ Γ)
    (w₁ : WF s₁) (hinf : inf.In (· < s₁.next)) :
    WF s₂ ∧ Local (Frame s₀.level s₀.next lvl) s₀ s₂ ∧
      CtxWF s₀.level lvl s₂
        ((x, .poly (genVars s₀.level s₀.next s₂.next lvl) (.var s₀.next)) :: Γ) := by
  have hvs := (in_fresh s₀).scope_mono h₁.to_ext.next
  have c := hc.wf w₁ hinf hvs
  have hnX : Frame s₀.level s₀.next lvl s₀.next := .inl (Nat.le_refl _)
  have l₀ := Local.fresh (w.closed lvl)
  have f₁ := h₁.local (X := Frame s₀.level s₀.next lvl) (fun _ hw => .inl (Nat.le_of_succ_le hw))
    (((hΓ.ctxIn.mono fun _ hw => .inr hw).local l₀).cons (x := x) (e := .mono _)
      (SType.in_var.mpr hnX))
    (w.closed lvl) (w.expsIn lvl)
  have n₁ := Nat.le_trans (Nat.le_succ _) h₁.to_ext.next
  have f₂ := hc.local (X := Frame s₀.level s₀.next lvl) (fun _ hw => .inl (Nat.le_trans n₁ hw))
    f₁.2.2 (SType.in_var.mpr hnX) f₁.1.closed ((w.expsIn lvl).of_new f₁.2.1)
  have lw := l₀.trans (f₁.1.trans f₂.1)
  have hL₂ : s₂.level = s₀.level := hc.to_ext.level.trans h₁.to_ext.level
  exact ⟨c, lw, (hΓ.step hL₂ (Nat.le_trans n₁ hc.to_ext.next) c.levels lw).cons
    (let_entry c (hvs.scope_mono hc.to_ext.next) (SType.in_var.mpr hnX) lw.closed)⟩

/-! ## The allocation invariants of typing -/

mutual
/-- **Typing keeps the allocation invariants**, and the inferred type is
in scope, of level at most the current level. -/
theorem TypeTerm.wf : TypeTerm Γ lvl s t st s' → s.level = L → WF s → CtxWF L lvl s Γ →
    WF s' ∧ st.In (· < s'.next) ∧ st.In (fun w => L w ≤ lvl)
  | .lit, _, w, _ => ⟨w, SType.in_prim, SType.in_prim⟩
  | .var hl, _, w, hΓ => ⟨w, (hΓ _ _ hl).1, (hΓ _ _ hl).2⟩
  | .inst hl hi, hL, w, hΓ => by
    subst hL
    obtain ⟨hst, _, hsch⟩ := hΓ _ _ hl
    exact ⟨⟨w.scope.instantiate hi, w.levels.instantiate hi hsch, w.cons.instantiate w.scope hi⟩,
      in_scope_rename hi hst,
      in_rename_of (X := fun w => _ ≤ lvl) hi (fun α hα => Nat.le_of_eq (hi.level α hα)) hsch.ty⟩
  | .lam (s := s₀) (x := x) _ hlv h, hL, w, hΓ => by
    have hv := in_fresh s₀
    have hvl : (SType.var s₀.next).In (fun w => L w ≤ lvl) :=
      SType.in_var.mpr (by rw [← hL]; exact Nat.le_of_eq hlv)
    have r := h.wf hL w.fresh (hΓ.fresh.cons (x := x) (e := .mono _) ⟨hv, hvl⟩)
    exact ⟨r.1, SType.in_arrow.mpr ⟨hv.scope_mono h.to_ext.next, r.2.1⟩,
      SType.in_arrow.mpr ⟨hvl, r.2.2⟩⟩
  | .app (s := s₀) _ hlv h₁ h₂ hc, hL, w, hΓ => by
    have hv := in_fresh s₀
    have hvl : (SType.var s₀.next).In (fun w => L w ≤ lvl) :=
      SType.in_var.mpr (by rw [← hL]; exact Nat.le_of_eq hlv)
    have r₁ := h₁.wf hL w.fresh hΓ.fresh
    have r₂ := h₂.wf (h₁.to_ext.level.trans hL) r₁.1 (hΓ.fresh.run hL w.fresh h₁ r₁.1)
    have hres := hv.scope_mono (Nat.le_trans h₁.to_ext.next h₂.to_ext.next)
    have c := hc.wf r₂.1 (r₁.2.1.scope_mono h₂.to_ext.next) (SType.in_arrow.mpr ⟨r₂.2.1, hres⟩)
    exact ⟨c, hres.scope_mono hc.to_ext.next, hvl⟩
  | .rcd h, hL, w, hΓ => by
    have r := h.wf hL w hΓ
    exact ⟨r.1, SType.in_record.mpr ⟨r.2.1, SType.in_nil⟩,
      SType.in_record.mpr ⟨r.2.2, SType.in_nil⟩⟩
  | .sel (s := s₀) _ hlv h hc, hL, w, hΓ => by
    have hv := in_fresh s₀
    have hvl : (SType.var s₀.next).In (fun w => L w ≤ lvl) :=
      SType.in_var.mpr (by rw [← hL]; exact Nat.le_of_eq hlv)
    have r := h.wf hL w.fresh hΓ.fresh
    have hres := hv.scope_mono h.to_ext.next
    have c := hc.wf r.1 r.2.1
      (SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨hres, SFields.in_nil⟩, SType.in_abs⟩)
    exact ⟨c, hres.scope_mono hc.to_ext.next, hvl⟩
  | .selOr (s := s₀) _ hlv h hc hd hc', hL, w, hΓ => by
    have hv := in_fresh s₀
    have hvl : (SType.var s₀.next).In (fun w => L w ≤ lvl) :=
      SType.in_var.mpr (by rw [← hL]; exact Nat.le_of_eq hlv)
    have r := h.wf hL w.fresh hΓ.fresh
    have hres := hv.scope_mono h.to_ext.next
    have c := hc.wf r.1 r.2.1
      (SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨SType.in_opt.mpr hres, SFields.in_nil⟩,
        SType.in_abs⟩)
    have hL₁ := h.to_ext.level.trans hL
    have hΓ₂ := (hΓ.fresh.run hL w.fresh h r.1).constrain hL₁ r.1 hc c r.2.2
      (SType.in_record.mpr ⟨SFields.in_cons.mpr ⟨SType.in_opt.mpr hvl, SFields.in_nil⟩,
        SType.in_abs⟩)
    have rd := hd.wf (hc.to_ext.level.trans hL₁) c hΓ₂
    have hres' := hres.scope_mono (Nat.le_trans hc.to_ext.next hd.to_ext.next)
    have c' := hc'.wf rd.1 rd.2.1 hres'
    exact ⟨c', hres'.scope_mono hc'.to_ext.next, hvl⟩
  | .ext (s₂ := s₂) _ h₁ h₂ _ hlv hc, hL, w, hΓ => by
    have r₁ := h₁.wf hL w hΓ
    have hL₁ := h₁.to_ext.level.trans hL
    have r₂ := h₂.wf hL₁ r₁.1 (hΓ.run hL w h₁ r₁.1)
    have hρ := in_fresh s₂
    have hρl : (SType.var s₂.next).In (fun w => L w ≤ lvl) :=
      SType.in_var.mpr (by rw [← h₂.to_ext.level.trans hL₁]; exact Nat.le_of_eq hlv)
    have c := hc.wf r₂.1.fresh
      (r₁.2.1.scope_mono (Nat.le_trans h₂.to_ext.next (Nat.le_succ _)))
      (SType.in_record.mpr ⟨SFields.In.absOf, hρ⟩)
    exact ⟨c, SType.in_record.mpr
        ⟨r₂.2.1.scope_mono (Nat.le_trans (Nat.le_succ _) hc.to_ext.next),
          hρ.scope_mono hc.to_ext.next⟩,
      SType.in_record.mpr ⟨r₂.2.2, hρl⟩⟩
  | .extNil h, hL, w, hΓ => h.wf hL w hΓ
  | .letIn (s := s₀) (s₁ := s₁) h₁ h₂, hL, w, hΓ => by
    subst hL
    have r₁ := h₁.wf rfl w (hΓ.mono_lvl (Nat.le_succ lvl))
    have fr := h₁.frame (lvl := lvl) w hΓ.ctxIn
    exact h₂.wf h₁.to_ext.level r₁.1
      ((hΓ.run rfl w h₁ r₁.1).cons (let_entry r₁.1 r₁.2.1 fr.2 fr.1.closed))
  | .letRec (s := s₀) (s₁ := s₁) (s₂ := s₂) (x := x) _ _ hlv h₁ hc h₂, hL, w, hΓ => by
    subst hL
    have hv := in_fresh s₀
    have hvl : (SType.var s₀.next).In (fun w => s₀.level w ≤ lvl + 1) :=
      SType.in_var.mpr (Nat.le_of_eq hlv)
    have r₁ := h₁.wf rfl w.fresh
      (((hΓ.mono_lvl (Nat.le_succ lvl)).fresh).cons (x := x) (e := .mono _) ⟨hv, hvl⟩)
    have win := letRec_window h₁ hc w hΓ r₁.1 r₁.2.1
    exact h₂.wf (hc.to_ext.level.trans h₁.to_ext.level) win.1 win.2.2
  | .ite (s := s₀) _ hlv hc h₁ ha h₂ hb h₃, hL, w, hΓ => by
    have hv := in_fresh s₀
    have hvl : (SType.var s₀.next).In (fun w => L w ≤ lvl) :=
      SType.in_var.mpr (by rw [← hL]; exact Nat.le_of_eq hlv)
    have rc := hc.wf hL w.fresh hΓ.fresh
    have c₁ := h₁.wf rc.1 rc.2.1 SType.in_prim
    have hL₁ := hc.to_ext.level.trans hL
    have hL₂ := h₁.to_ext.level.trans hL₁
    have hΓ₂ := (hΓ.fresh.run hL w.fresh hc rc.1).constrain hL₁ rc.1 h₁ c₁ rc.2.2 SType.in_prim
    have ra := ha.wf hL₂ c₁ hΓ₂
    have k₃ := Nat.le_trans hc.to_ext.next (Nat.le_trans h₁.to_ext.next ha.to_ext.next)
    have c₂ := h₂.wf ra.1 ra.2.1 (hv.scope_mono k₃)
    have hL₃ := ha.to_ext.level.trans hL₂
    have hL₄ := h₂.to_ext.level.trans hL₃
    have hΓ₄ := (hΓ₂.run hL₂ c₁ ha ra.1).constrain hL₃ ra.1 h₂ c₂ ra.2.2 hvl
    have rb := hb.wf hL₄ c₂ hΓ₄
    have k₅ := Nat.le_trans k₃ (Nat.le_trans h₂.to_ext.next hb.to_ext.next)
    have c₃ := h₃.wf rb.1 rb.2.1 (hv.scope_mono k₅)
    exact ⟨c₃, hv.scope_mono (Nat.le_trans k₅ h₃.to_ext.next), hvl⟩
  | .fn _ hp h, hL, w, hΓ => by
    have rp := hp.wf hL w hΓ
    have r := h.wf (hp.to_ext.level.trans hL) rp.1 rp.2.2.2
    exact ⟨r.1, SType.in_arrow.mpr ⟨SType.in_sig.mpr (rp.2.1.scope_mono h.to_ext.next), r.2.1⟩,
      SType.in_arrow.mpr ⟨SType.in_sig.mpr rp.2.2.1, r.2.2⟩⟩

theorem TypeFields.wf : TypeFields Γ lvl s fs F s' → s.level = L → WF s → CtxWF L lvl s Γ →
    WF s' ∧ F.In (· < s'.next) ∧ F.In (fun w => L w ≤ lvl)
  | .nil, _, w, _ => ⟨w, SFields.in_nil, SFields.in_nil⟩
  | .cons h₁ h₂, hL, w, hΓ => by
    have r₁ := h₁.wf hL w hΓ
    have r₂ := h₂.wf (h₁.to_ext.level.trans hL) r₁.1 (hΓ.run hL w h₁ r₁.1)
    exact ⟨r₂.1, SFields.in_cons.mpr ⟨r₁.2.1.scope_mono h₂.to_ext.next, r₂.2.1⟩,
      SFields.in_cons.mpr ⟨r₁.2.2, r₂.2.2⟩⟩

theorem TypeParams.wf : TypeParams Γ lvl s ps P Γ' s' → s.level = L → WF s → CtxWF L lvl s Γ →
    WF s' ∧ P.In (· < s'.next) ∧ P.In (fun w => L w ≤ lvl) ∧ CtxWF L lvl s' Γ'
  | .nil, _, w, hΓ => ⟨w, SParams.in_nil, SParams.in_nil, hΓ⟩
  | .req (s := s₀) (x := x) _ hlv h, hL, w, hΓ => by
    have hv := in_fresh s₀
    have hvl : (SType.var s₀.next).In (fun w => L w ≤ lvl) :=
      SType.in_var.mpr (by rw [← hL]; exact Nat.le_of_eq hlv)
    have r := h.wf hL w.fresh (hΓ.fresh.cons (x := x) (e := .mono _) ⟨hv, hvl⟩)
    exact ⟨r.1, SParams.in_cons.mpr ⟨hv.scope_mono h.to_ext.next, r.2.1⟩,
      SParams.in_cons.mpr ⟨hvl, r.2.2.1⟩, r.2.2.2⟩
  | .dflt (s := s₀) (x := x) _ hlv hd hc h, hL, w, hΓ => by
    have hv := in_fresh s₀
    have hvl : (SType.var s₀.next).In (fun w => L w ≤ lvl) :=
      SType.in_var.mpr (by rw [← hL]; exact Nat.le_of_eq hlv)
    have rd := hd.wf hL w.fresh hΓ.fresh
    have hvs := hv.scope_mono hd.to_ext.next
    have c := hc.wf rd.1 rd.2.1 hvs
    have hL₁ := hd.to_ext.level.trans hL
    have hΓ₂ := (hΓ.fresh.run hL w.fresh hd rd.1).constrain hL₁ rd.1 hc c rd.2.2 hvl
    have r := h.wf (hc.to_ext.level.trans hL₁) c
      (hΓ₂.cons (x := x) (e := .mono _) ⟨hvs.scope_mono hc.to_ext.next, hvl⟩)
    exact ⟨r.1,
      SParams.in_cons.mpr
        ⟨hvs.scope_mono (Nat.le_trans hc.to_ext.next h.to_ext.next), r.2.1⟩,
      SParams.in_cons.mpr ⟨hvl, r.2.2.1⟩, r.2.2.2⟩
end

/-! ## From the initial state -/

theorem WF.init {K : Nat → List String} {L : Nat → Nat} : WF (State.initKL K L) :=
  ⟨.init, fun _ _ h => h.elim (fun h => nomatch h) (fun h => nomatch h), fun _ _ _ h _ => nomatch h⟩

theorem PCtx.lookup_mem {Γ : PCtx} {x : String} {e : CEntry} (h : Γ.lookup x = some e) :
    (x, e) ∈ Γ := by
  simp only [PCtx.lookup, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hx := List.find?_some hp
  simp at hx
  have := List.mem_of_find?_eq_some hp
  subst hx
  exact this

/-- The built-ins mention no variable. -/
theorem pbuiltins_closed {x : String} {e : CEntry} (h : pbuiltins.lookup x = some e) :
    ∃ st, e = .mono st ∧ st.vars = [] := by
  have hm := PCtx.lookup_mem h
  simp only [pbuiltins, builtins, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    exact ⟨_, rfl, by simp [SType.vars, SParams.vars, builtinSig]⟩

theorem pbuiltins_wf {L : Nat → Nat} {lvl : Nat} {s : State} : CtxWF L lvl s pbuiltins := by
  intro x e h
  obtain ⟨st, rfl, hv⟩ := pbuiltins_closed h
  exact ⟨(fun w hw => by rw [hv] at hw; exact nomatch hw),
    (fun w hw => by rw [hv] at hw; exact nomatch hw)⟩

/-- A run from the initial state. -/
theorem TypeTerm.wf_init {K : Nat → List String} {L : Nat → Nat}
    (h : TypeTerm pbuiltins 0 (State.initKL K L) t st s') : WF s' :=
  (h.wf (L := L) rfl .init pbuiltins_wf).1

end BoltCore.Alg
