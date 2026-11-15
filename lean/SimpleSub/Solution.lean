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

This file sets up the solution and the invariants it needs; the solution
theorem itself, for all simple types, is in `SolutionRows.lean`.
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
  | .allAbsent _ _ h', h => h'.inv₂ h
  | .memo _ _ h₁ _ h₂, h => h₂.inv₂ (h₁.inv₂ h)
  | .fresh _ _ h₁ _ _ h₂, h => h₂.inv₂ ((h₁.inv₂ h).of_bounds rfl fun _ hp => hp)
end

theorem Inv₂.fresh {s : State} (h : Inv₂ s) : Inv₂ s.fresh := h.of_bounds rfl fun _ hp => hp

theorem ConstrainTop.inv₂ {s s' : State} (h : ConstrainTop s a b s') (hi : Inv₂ s) : Inv₂ s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact (hc.inv₂ (hi.of_bounds rfl fun _ hp => hp)).of_bounds rfl fun _ hp => hp

mutual
theorem TypeTerm.inv₂ : TypeTerm Γ s t st s' → Inv₂ s → Inv₂ s'
  | .lit, h => h
  | .var _, h => h
  | .lam _ h', h => h'.inv₂ h.fresh
  | .app _ h₁ h₂ hc, h => hc.inv₂ (h₂.inv₂ (h₁.inv₂ h.fresh))
  | .rcd h', h => h'.inv₂ h
  | .sel _ h' hc, h => hc.inv₂ (h'.inv₂ h.fresh)
  | .ext _ h₁ h₂ _ hc, h => hc.inv₂ (h₂.inv₂ (h₁.inv₂ h)).fresh
  | .extNil h', h => h'.inv₂ h
  | .letIn h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)
  | .letRec _ h₁ hc h₂, h => h₂.inv₂ (hc.inv₂ (h₁.inv₂ h.fresh))

theorem TypeFields.inv₂ : TypeFields Γ s fs F s' → Inv₂ s → Inv₂ s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)
end

theorem Inv₂.init {K : Nat → List String} : Inv₂ (State.initK K) :=
  ⟨⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩, (fun _ _ h => nomatch h)⟩

/-! ## Closing chains of variable bounds -/

theorem Justified.step {s : State} (h : Justified s) (hp : (a, b) ∈ s.log) :
    GStep s.bounds (Logged s) a b := by
  rcases h _ hp with h | h
  · exact nomatch h
  · exact h

end SimpleSub.Alg
