import BoltCore.SolutionRows
import BoltCore.Typing

/-!
# The final state

What the solution theorem needs of the state a run ends in (`Final`), and
the fields of inferred records (`SFields.Pres`: present, not `Abs`).

Theorem 1, soundness of inference, used to be proved here directly on a
run of the algorithm. A run with let-polymorphism is checked through its
certificate instead (`theorem1`, `Adequacy.lean`).
-/

namespace BoltCore.Alg

open State

/-- A top-level `constrain` call accepts its constraint (no invariant needed). -/
theorem ConstrainTop.logged {s s' : State} (h : ConstrainTop s a b s') : Logged s' a b := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact hc.accepts fun _ h => nomatch h

theorem ConstrainTop.log_grows {s s' : State} (h : ConstrainTop s a b s') :
    ∀ p, p ∈ s.log → p ∈ s'.log := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact hc.grows.log

theorem TypeFields.log_grows (h : TypeFields Γ lvl s fs F s') : ∀ p, p ∈ s.log → p ∈ s'.log :=
  h.to_ext.log

theorem TypeParams.log_grows (h : TypeParams Γ lvl s ps P Γ' s') :
    ∀ p, p ∈ s.log → p ∈ s'.log := h.to_ext.log

theorem TypeTerm.kind_eq (h : TypeTerm Γ lvl s t st s') : s'.kind = s.kind := h.to_ext.kind

/-! ## What the final state provides -/

/-- What the final state provides: the invariants the solution theorem
needs. -/
structure Final (sf : State) (rank : Nat → Nat) : Prop where
  inv : Inv sf
  inLog : BoundsInLog sf
  nac : LogNAC sf
  ranked : TailRanked sf rank

theorem Logged.of_log {s s' : State} (hlog : ∀ p, p ∈ s.log → p ∈ s'.log) :
    Logged s a b → Logged s' a b
  | .inl h => .inl h
  | .inr h => .inr (hlog _ h)

/-! ## Fields of inferred records -/

/-- The fields as a list of label and type, under an interpretation. -/
def SFields.toListI (I : SInterp) : SFields → List (String × Ty .ty)
  | .nil => []
  | .cons n f fs => (n, f.toTyI I) :: fs.toListI I

/-- Every field is present: none is `Abs`, `Missing` or optional. -/
def SFields.Pres : SFields → Prop
  | .nil => True
  | .cons _ f fs => f.IsPre ∧ fs.Pres

theorem SFields.toRowOnI_pres {I : SInterp} {ρ : Ty .row} :
    ∀ {F : SFields}, F.Pres → F.toRowOnI I ρ = Ty.ofFields (F.toListI I) ρ
  | .nil, _ => rfl
  | .cons n f F, ⟨hf, hF⟩ => by
    rw [SFields.toRowOnI_cons, SType.toFieldI_of_pre hf, SFields.toRowOnI_pres hF]; rfl

theorem SFields.toRowOnI_absOf {I : SInterp} {ρ : Ty .row} :
    ∀ F : SFields, F.absOf.toRowOnI I ρ = Ty.absFields (F.toListI I) ρ
  | .nil => rfl
  | .cons n f F => by
    simp only [SFields.absOf, SFields.toRowOnI_cons, SFields.toRowOnI_absOf F]; rfl

/-- The fields as a list, in the solution. -/
abbrev SFields.toList (F : SFields) : List (String × Ty .ty) := F.toListI .gv

theorem SFields.Pres.rename {f : Nat → Nat} : ∀ {F : SFields}, F.Pres → (F.rename f).Pres
  | .nil, _ => trivial
  | .cons _ _ _, ⟨hg, hF⟩ => ⟨hg.rename, hF.rename⟩

end BoltCore.Alg
