import SimpleSub.Soundness
import SimpleSub.Sub

/-!
# A solution of the inferred constraints

Soundness of constraining (`Soundness.lean`) says that the algorithm's log
of accepted constraints is self-justifying and its bounds consistent. Here
we turn that into actual subtyping facts: we interpret every type variable
`v` of the state as the graph variable `gvar v`, defined (`Defs`, see
`Sub.lean`) as the intersection of its upper bounds, and prove that every
accepted constraint `a ≤ b` gives `θ(a) ≤ θ(b)` in the declarative relation
`Sub`. This is the paper's *unifying coalescing* (Fig. 12): each variable is
instantiated to the greatest type consistent with its bounds.

The upper bounds of `v` that define it are the *non-variable* upper bounds
reachable from `v` through variable-to-variable upper bounds (`Clo`), since
the algorithm does not close such chains itself, and they may be cyclic.
Being an inductive predicate, `Clo` needs no visited set and no fuel.

This file covers the **record-free fragment** (variables, primitives,
arrows). Rows add field projections and row expansion to the argument and
come next.
-/

namespace SimpleSub.Alg

open State

/-! ## From simple types to types -/

mutual
/-- A simple type as a type: variables become graph variables. -/
def SType.toTy : SType → Ty
  | .var v => .gvar v
  | .prim n => .prim n
  | .arrow a b => .arrow a.toTy b.toTy
  | .record fs t => .record fs.toFields t.toTy
  | .abs => .abs

def SFields.toFields : SFields → Fields
  | .nil => .nil
  | .cons n f fs => .cons n f.toTy fs.toFields
end

/-- Record-free simple types. -/
def SType.RF : SType → Prop
  | .var _ => True
  | .prim _ => True
  | .arrow a b => a.RF ∧ b.RF
  | _ => False

/-- `u` is a non-variable upper bound of `n`, possibly through a chain of
variable upper bounds. -/
inductive Clo (σ : Nat → Bounds) : Nat → SType → Prop where
  | here : u ∈ (σ n).upper → (∀ w, u ≠ .var w) → Clo σ n u
  | step : .var m ∈ (σ n).upper → Clo σ m u → Clo σ n u

/-- The definitions of the solution: `gvar n` is the intersection of the
(translated) non-variable upper bounds reachable from `n`. -/
def defsOf (s : State) : Defs := fun n τ => ∃ u, Clo s.bounds n u ∧ τ = u.toTy

theorem Clo.nonvar : Clo σ n u → ∀ w, u ≠ .var w
  | .here _ h => h
  | .step _ h => h.nonvar

/-! ## Two more invariants -/

/-- Every bound was installed by a logged constraint. -/
def BoundsInLog (s : State) : Prop :=
  (∀ v x, x ∈ (s.bounds v).upper → (.var v, x) ∈ s.log) ∧
  (∀ v x, x ∈ (s.bounds v).lower → (x, .var v) ∈ s.log)

/-- Lower bounds are never variables (a variable-to-variable constraint
always installs an upper bound). -/
def LbNonVar (s : State) : Prop := ∀ v x, x ∈ (s.bounds v).lower → ∀ w, x ≠ .var w

structure Inv₂ (s : State) : Prop where
  inLog : BoundsInLog s
  lbNonVar : LbNonVar s

theorem Inv₂.of_bounds {s s' : State} (h : Inv₂ s) (hb : s'.bounds = s.bounds)
    (hlog : ∀ p, p ∈ s.log → p ∈ s'.log) : Inv₂ s' := by
  refine ⟨⟨fun v x hx => ?_, fun v x hx => ?_⟩, fun v x hx => ?_⟩
  · rw [hb] at hx; exact hlog _ (h.inLog.1 v x hx)
  · rw [hb] at hx; exact hlog _ (h.inLog.2 v x hx)
  · rw [hb] at hx; exact h.lbNonVar v x hx

theorem Inv₂.addUpper {s : State} {v : Nat} {b : SType} (h : Inv₂ (s.remember (.var v) b)) :
    Inv₂ ((s.remember (.var v) b).addUpper v b) := by
  refine ⟨⟨fun w x hx => ?_, fun w x hx => ?_⟩, fun w x hx => ?_⟩
  · rcases mem_upper_addUpper_inv hx with ⟨rfl, rfl⟩ | hx
    · exact List.mem_cons_self ..
    · exact h.inLog.1 w x hx
  · rw [lower_addUpper] at hx; exact h.inLog.2 w x hx
  · rw [lower_addUpper] at hx; exact h.lbNonVar w x hx

theorem Inv₂.addLower {s : State} {v : Nat} {a : SType} (hnv : ∀ w, a ≠ .var w)
    (h : Inv₂ (s.remember a (.var v))) : Inv₂ ((s.remember a (.var v)).addLower v a) := by
  refine ⟨⟨fun w x hx => ?_, fun w x hx => ?_⟩, fun w x hx => ?_⟩
  · rw [upper_addLower] at hx; exact h.inLog.1 w x hx
  · rcases mem_lower_addLower_inv hx with ⟨rfl, rfl⟩ | hx
    · exact List.mem_cons_self ..
    · exact h.inLog.2 w x hx
  · rcases mem_lower_addLower_inv hx with ⟨rfl, rfl⟩ | hx
    · exact hnv
    · exact h.lbNonVar w x hx

theorem Inv₂.remember {s : State} (h : Inv₂ s) : Inv₂ (s.remember a b) :=
  h.of_bounds rfl fun _ hp => List.mem_cons_of_mem _ hp

mutual
theorem Constrain.inv₂ : Constrain s a b s' → Inv₂ s → Inv₂ s'
  | .cached _, h => h
  | .refl, h => h
  | .arrow _ h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h.remember)
  | .absR _, h => h.remember
  | .absRecord _ h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h.remember)
  | .record _ _ _ h₁ h₂ h₃, h => h₃.inv₂ (h₂.inv₂ (h₁.inv₂ h.remember))
  | .varL _ _ h', h => h'.inv₂ h.remember.addUpper
  | .varR _ hnv h', h => h'.inv₂ (h.remember.addLower hnv)

theorem ConstrainEach.inv₂ : ConstrainEach s ps s' → Inv₂ s → Inv₂ s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)

theorem ConstrainField.inv₂ : ConstrainField s a b s' → Inv₂ s → Inv₂ s'
  | .toAbs, h => h
  | .pre _ _ h', h => h'.inv₂ h

theorem FieldsEach.inv₂ : FieldsEach s ps s' → Inv₂ s → Inv₂ s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)

theorem Expand.inv₂ : Expand s t ms t' s' → Inv₂ s → Inv₂ s'
  | .none, h => h
  | .abs _ h', h => h'.inv₂ h
  | .memo _ _ h', h => h'.inv₂ h
  | .fresh _ _ h', h => h'.inv₂ (h.of_bounds rfl fun _ hp => hp)
end

theorem Inv₂.fresh {s : State} (h : Inv₂ s) : Inv₂ s.fresh := h.of_bounds rfl fun _ hp => hp

theorem ConstrainTop.inv₂ {s s' : State} (h : ConstrainTop s a b s') (hi : Inv₂ s) : Inv₂ s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact (hc.inv₂ (hi.of_bounds rfl fun _ hp => hp)).of_bounds rfl fun _ hp => hp

mutual
theorem TypeTerm.inv₂ : TypeTerm Γ s t st s' → Inv₂ s → Inv₂ s'
  | .lit, h => h
  | .var _, h => h
  | .lam h', h => h'.inv₂ h.fresh
  | .app h₁ h₂ hc, h => hc.inv₂ (h₂.inv₂ (h₁.inv₂ h.fresh))
  | .rcd h', h => h'.inv₂ h
  | .sel h' hc, h => hc.inv₂ (h'.inv₂ h.fresh)
  | .ext h₁ h₂ hc, h => hc.inv₂ (h₂.inv₂ (h₁.inv₂ h)).fresh
  | .letIn h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)
  | .letRec h₁ hc h₂, h => h₂.inv₂ (hc.inv₂ (h₁.inv₂ h.fresh))

theorem TypeFields.inv₂ : TypeFields Γ s fs F s' → Inv₂ s → Inv₂ s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)
end

theorem Inv₂.init : Inv₂ State.init :=
  ⟨⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩, (fun _ _ h => nomatch h)⟩

/-! ## Closing chains of variable bounds -/

theorem Justified.step {s : State} (h : Justified s) (hp : (a, b) ∈ s.log) :
    GStep s.bounds (Logged s) a b := by
  rcases h _ hp with h | h
  · exact nomatch h
  · exact h

/-- A logged constraint from a non-variable into a variable installed a
lower bound. -/
theorem GStep.lower_of_var (h : GStep σ R a (.var m)) (hnv : ∀ w, a ≠ .var w) :
    a ∈ (σ m).lower := by
  cases h with
  | varR h => exact h
  | varL => exact absurd rfl (hnv _)

/-- **Chains of variable bounds are closed**: a lower bound of `v` is
logged below every upper bound reachable from `v`. -/
theorem clo_logged {s : State} (hi : Inv s) (h₂ : Inv₂ s) (hc : Clo s.bounds v u) :
    ∀ a, a ∈ (s.bounds v).lower → Logged s a u := by
  induction hc with
  | here hu _ =>
    intro a ha
    rcases hi.cons _ a _ ha hu with h | h
    · exact h
    · exact nomatch h
  | step hm _ ih =>
    intro a ha
    have hnv := h₂.lbNonVar _ a ha
    rcases hi.cons _ a _ ha hm with h | h
    · rcases h with h | h
      · exact absurd h (hnv _)
      · exact ih a ((hi.just.step h).lower_of_var hnv)
    · exact nomatch h

/-! ## The solution, for the record-free fragment -/

/-- Every accepted constraint is record-free. -/
def RecordFree (s : State) : Prop := ∀ p, p ∈ s.log → p.1.RF ∧ p.2.RF

theorem Clo.rf {s : State} (h₂ : Inv₂ s) (hrf : RecordFree s) : Clo s.bounds n u → u.RF
  | .here hu _ => (hrf _ (h₂.inLog.1 _ _ hu)).2
  | .step _ h => h.rf h₂ hrf

/-- The relation used for the coinduction. -/
def SolRel (s : State) (x y : Ty) : Prop :=
  ∃ a b, Logged s a b ∧ a.RF ∧ b.RF ∧ x = a.toTy ∧ y = b.toTy

/-- One layer of reflexivity for a record-free type. -/
theorem step_refl_rf {s : State} (ha : SType.RF a) : Step (defsOf s) (SolRel s) a.toTy a.toTy := by
  match a, ha with
  | .var _, _ => exact .gvar
  | .prim _, _ => exact .prim
  | .arrow a b, ⟨ha, hb⟩ =>
    exact .arrow ⟨a, a, .inl rfl, ha, ha, rfl, rfl⟩ ⟨b, b, .inl rfl, hb, hb, rfl, rfl⟩

/-- One layer for a logged constraint between two non-variable record-free
types: it is reflexive, or an arrow constraint. -/
theorem step_nonvar {s : State} (hi : Inv s) (hl : Logged s a b) (ha : a.RF) (hb : b.RF)
    (hav : ∀ w, a ≠ .var w) (hbv : ∀ w, b ≠ .var w) :
    Step (defsOf s) (SolRel s) a.toTy b.toTy := by
  rcases hl with rfl | hl
  · exact step_refl_rf ha
  · cases hi.just.step hl with
    | absR => exact nomatch hb
    | absRecord => exact nomatch ha
    | record => exact nomatch ha
    | varL => exact absurd rfl (hav _)
    | varR => exact absurd rfl (hbv _)
    | arrow h₁ h₂ =>
      exact .arrow ⟨_, _, h₁, hb.1, ha.1, rfl, rfl⟩ ⟨_, _, h₂, ha.2, hb.2, rfl, rfl⟩

/-- **Solution theorem** (record-free fragment): in a state reached by the
algorithm whose accepted constraints are record-free, every accepted
constraint `a ≤ b` holds of the solution: `θ(a) ≤ θ(b)`, where each type
variable is the intersection of its reachable upper bounds. -/
theorem solution {s : State} (hi : Inv s) (h₂ : Inv₂ s) (hrf : RecordFree s)
    (hl : Logged s a b) (ha : a.RF) (hb : b.RF) : Sub (defsOf s) a.toTy b.toTy := by
  refine Sub.coind (SolRel s) ?_ ⟨a, b, hl, ha, hb, rfl, rfl⟩
  rintro _ _ ⟨a, b, hl, ha, hb, rfl, rfl⟩
  rcases hl with rfl | hl
  · exact step_refl_rf ha
  · cases hi.just.step hl with
    | absR => exact nomatch hb
    | absRecord => exact nomatch ha
    | record => exact nomatch ha
    | arrow h₁ h₂ =>
      exact .arrow ⟨_, _, h₁, hb.1, ha.1, rfl, rfl⟩ ⟨_, _, h₂, ha.2, hb.2, rfl, rfl⟩
    | varL hub =>
      -- `gvar v ≤ θ(b)`, with `b` an upper bound of `v`
      match b, hb with
      | .var w, _ =>
        -- below every upper bound of `w`: each is also reachable from `v`
        exact .defR fun τ ⟨u, hc, hτ⟩ => by
          subst hτ
          exact .defL ⟨u, .step hub hc, rfl⟩ (step_refl_rf (hc.rf h₂ hrf))
      | .prim _, _ => exact .defL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ .prim
      | .arrow _ _, hb =>
        exact .defL ⟨_, .here hub (fun _ h => nomatch h), rfl⟩ (step_refl_rf hb)
    | varR hlb =>
      -- `θ(a) ≤ gvar v`, with `a` a lower bound of `v`: below every
      -- reachable upper bound of `v`, by consistency along the chain
      exact .defR fun τ ⟨u, hc, hτ⟩ => by
        subst hτ
        exact step_nonvar hi (clo_logged hi h₂ hc a hlb) ha (hc.rf h₂ hrf)
          (h₂.lbNonVar _ a hlb) hc.nonvar

end SimpleSub.Alg
