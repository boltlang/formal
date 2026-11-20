import BoltCore.Soundness
import BoltCore.Sub

/-!
# A solution of the inferred constraints

Soundness of constraining (`Soundness.lean`) says that the algorithm's log
of accepted constraints is self-justifying and its bounds consistent. The
solution turns that into subtyping facts: every type variable `v` becomes
the graph variable `gvar v`, defined (`Defs`, see `Sub.lean`) as the
intersection of its upper bounds, and every accepted constraint holds of
it (`SolutionRows.lean`). This is the paper's *unifying coalescing*
(Fig. 12): each variable is instantiated to the greatest type consistent
with its bounds.

The upper bounds that define `v` are its *non-variable* upper bounds
reachable through variable-to-variable upper bounds (`Clo`), since the
algorithm does not close such chains itself, and they may be cyclic. Being
an inductive predicate, `Clo` needs no visited set and no fuel.

The algorithm's simple types are unsorted; a simple type is translated by
the position it is used in (`docs/design/sorts.md`):

* `toTy` as a type: a record is `rcd` of its row;
* `toRow` as a row: a record's fields go in front of its tail's row, the
  top row `Abs` is `⊤`, and the empty row is `nil`;
* `toField` as a field: `Abs` is `⊤`, `Missing` is `missing`, `Opt τ` is
  `opt τ = pre τ ∪ missing`, and any other type `τ` is `pre τ`.

A signature is the union of its argument records, `Ty.sig` of its
translated parameters: as a type the union of the records, and as a row
the union of their rows.

A variable becomes the graph variable of the same number at the sort of its
position, and every graph variable is defined at every sort, by its
reachable upper bounds translated at that sort (`defsOf`).
-/

namespace BoltCore.Alg

open State

/-- `u` is a non-variable upper bound of `n`, possibly through a chain of
variable upper bounds. -/
inductive Clo (σ : Nat → Bounds) : Nat → SType → Prop where
  | here : u ∈ (σ n).upper → (∀ w, u ≠ .var w) → Clo σ n u
  | step : .var m ∈ (σ n).upper → Clo σ m u → Clo σ n u

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
  | .absRecord _ h₁ h₂, h | .nilRecord _ h₁ h₂, h | .recordNil _ _ h₁ h₂, h =>
    h₂.inv₂ (h₁.inv₂ h.remember)
  | .record _ _ _ h₁ h₂ h₃, h => h₃.inv₂ (h₂.inv₂ (h₁.inv₂ h.remember))
  | .varL _ _ h', h => h'.inv₂ h.remember.addUpper
  | .varR _ hnv h', h => h'.inv₂ (h.remember.addLower hnv)
  | .recordSig _ _ _ _ _ h', h | .sigL _ _ h', h => h'.inv₂ h.remember

theorem ConstrainEach.inv₂ : ConstrainEach s ps s' → Inv₂ s → Inv₂ s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)

theorem ConstrainField.inv₂ : ConstrainField s a b s' → Inv₂ s → Inv₂ s'
  | .toAbs, h | .misMis, h | .misOpt, h => h
  | .optOpt _ h', h | .preOpt _ h', h | .pre _ _ h', h => h'.inv₂ h

theorem FieldsEach.inv₂ : FieldsEach s ps s' → Inv₂ s → Inv₂ s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)

theorem Expand.inv₂ : Expand s t ms t' s' → Inv₂ s → Inv₂ s'
  | .none, h => h
  | .abs _ h', h | .nil _ h', h => h'.inv₂ h
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
  | .ite _ hc h₁ ha h₂ hb h₃, h =>
    h₃.inv₂ (hb.inv₂ (h₂.inv₂ (ha.inv₂ (h₁.inv₂ (hc.inv₂ h.fresh)))))
  | .selOr _ h' hc hd hc', h => hc'.inv₂ (hd.inv₂ (hc.inv₂ (h'.inv₂ h.fresh)))
  | .ext _ h₁ h₂ _ hc, h => hc.inv₂ (h₂.inv₂ (h₁.inv₂ h)).fresh
  | .extNil h', h => h'.inv₂ h
  | .letIn h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)
  | .letRec _ _ h₁ hc h₂, h => h₂.inv₂ (hc.inv₂ (h₁.inv₂ h.fresh))
  | .fn _ hp h', h => h'.inv₂ (hp.inv₂ h)

theorem TypeFields.inv₂ : TypeFields Γ s fs F s' → Inv₂ s → Inv₂ s'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.inv₂ (h₁.inv₂ h)

theorem TypeParams.inv₂ : TypeParams Γ s ps P Γ' s' → Inv₂ s → Inv₂ s'
  | .nil, h => h
  | .req _ h', h => h'.inv₂ h.fresh
  | .dflt _ hd hc h', h => h'.inv₂ (hc.inv₂ (hd.inv₂ h.fresh))
end

theorem Inv₂.init {K : Nat → List String} : Inv₂ (State.initK K) :=
  ⟨⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩, (fun _ _ h => nomatch h)⟩

/-! ## Closing chains of variable bounds -/

theorem Justified.step {s : State} (h : Justified s) (hp : (a, b) ∈ s.log) :
    GStep s.bounds (Logged s) a b := by
  rcases h _ hp with h | h
  · exact nomatch h
  · exact h

/-! ## Translations

The translations are given under an *interpretation* of the variables, a
type and a row for each (`SInterp`), as generalizing a `let` needs
(`SolutionRows.lean`); the solution's translations are those under the
interpretation of each variable as its graph variable (`SInterp.gv`). -/

/-- An interpretation of the variables, at the type and row sorts. -/
abbrev SInterp := (srt : Srt) → Nat → Ty srt

/-- The solution's interpretation: every variable is its graph variable. -/
def SInterp.gv : SInterp := fun _ v => .gvar v

mutual
/-- A simple type as a type. (`Abs`, `Missing` and `Opt τ` are not types:
`Abs` and `Missing` are sent to `⊤` and `Opt τ` to `τ`, which only matters
for ill-sorted input. The empty row is read as the empty closed record, so
that a constraint between rows also holds between the records of those
rows.) -/
def SType.toTyI (I : SInterp) : SType → Ty .ty
  | .var v => I .ty v
  | .prim n => .prim n
  | .arrow a b => .arrow (a.toTyI I) (b.toTyI I)
  | .record fs t => .rcd (fs.toRowOnI I (t.toRowI I))
  | .nil => .rcd .nil
  | .opt t => t.toTyI I
  | .abs | .missing => .top
  | .sig P => Ty.sig (P.toParamsI I)

/-- A simple type as a row. Primitive and function types have no fields. -/
def SType.toRowI (I : SInterp) : SType → Ty .row
  | .var v => I .row v
  | .record fs t => fs.toRowOnI I (t.toRowI I)
  | .nil => .nil
  | .prim _ | .arrow _ _ | .abs | .missing | .opt _ => .top
  | .sig P => Ty.unions (Ty.sigRows (P.toParamsI I))

/-- Fields in front of a row. -/
def SFields.toRowOnI (I : SInterp) : SFields → Ty .row → Ty .row
  | .nil, ρ => ρ
  | .cons n f fs, ρ =>
    .cons n (match f with
      | .abs => .top
      | .missing => .missing
      | .opt τ => Ty.opt (τ.toTyI I)
      | f => .pre (f.toTyI I)) (fs.toRowOnI I ρ)

/-- The parameters of a signature, with their types translated. -/
def SParams.toParamsI (I : SInterp) : SParams → List (Param (Ty .ty))
  | .nil => []
  | .cons n k o τ P => ⟨n, k, o, τ.toTyI I⟩ :: P.toParamsI I
end

theorem SParams.toParamsI_eq (I : SInterp) : ∀ P : SParams,
    P.toParamsI I = P.toList.map (Param.map (·.toTyI I))
  | .nil => rfl
  | .cons _ _ _ _ P => by
    simp only [SParams.toParamsI, SParams.toList, List.map_cons, SParams.toParamsI_eq I P]; rfl

/-- A simple type as a field. -/
def SType.toFieldI (I : SInterp) : SType → Ty .field
  | .abs => .top
  | .missing => .missing
  | .opt τ => Ty.opt (τ.toTyI I)
  | f => .pre (f.toTyI I)

theorem SFields.toRowOnI_cons (I : SInterp) (n : String) (f : SType) (fs : SFields)
    (ρ : Ty .row) : (SFields.cons n f fs).toRowOnI I ρ = .cons n (f.toFieldI I) (fs.toRowOnI I ρ) := by
  cases f <;> rfl

theorem SType.toFieldI_of_pre {I : SInterp} {f : SType} (h : f.IsPre) : f.toFieldI I = .pre (f.toTyI I) := by
  cases f <;> first | rfl | exact absurd h id

/-- The solution's translations: every variable is its graph variable. -/
abbrev SType.toTy (t : SType) : Ty .ty := t.toTyI .gv
abbrev SType.toRow (t : SType) : Ty .row := t.toRowI .gv
abbrev SFields.toRowOn (fs : SFields) (ρ : Ty .row) : Ty .row := fs.toRowOnI .gv ρ
abbrev SType.toField (t : SType) : Ty .field := t.toFieldI .gv

/-- A simple type at a sort. -/
def SType.toAt (t : SType) : (srt : Srt) → Ty srt
  | .ty => t.toTy
  | .row => t.toRow
  | .field => t.toField

theorem SFields.toRowOn_cons (n : String) (f : SType) (fs : SFields) (ρ : Ty .row) :
    (SFields.cons n f fs).toRowOn ρ = .cons n f.toField (fs.toRowOn ρ) :=
  SFields.toRowOnI_cons .gv n f fs ρ

theorem SType.toField_of_pre {f : SType} (h : f.IsPre) : f.toField = .pre f.toTy :=
  SType.toFieldI_of_pre h

theorem SType.toTyI_gv (t : SType) : t.toTyI .gv = t.toTy := rfl
theorem SType.toRowI_gv (t : SType) : t.toRowI .gv = t.toRow := rfl

/-! ## The definitions of the solution -/

/-- `gvar n`, at each sort, is the intersection of the reachable
non-variable upper bounds of `n`, translated at that sort. -/
def defsOf (s : State) : Defs := fun srt n τ => ∃ u, Clo s.bounds n u ∧ τ = u.toAt srt

theorem defsOf.clo {s : State} (srt : Srt) (h : Clo s.bounds n u) : defsOf s srt n (u.toAt srt) :=
  ⟨u, h, rfl⟩

end BoltCore.Alg
