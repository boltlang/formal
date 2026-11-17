import BoltCore.Sorted.Solution
import BoltCore.Sorted.Typing
import BoltCore.Kinds

/-!
# Theorem 1, sorted

If the algorithm types a term, the term has the inferred type, translated
at the type sort through the sorted solution, in the sorted declarative
system. The proof is the unsorted one (`Theorem1.lean`) with two
simplifications: a selection needs no `⊤` premise (the typing rule asks for
`pre τ` by its shape), so the solution needs no `⊤` definition for type
variables; and constraints hold at the type sort directly. Record literals
and extensions need their field types to be present (not `Abs`), which
inferred types are (`TypeTerm.nac`).

With kinds discharging acyclicity of row tails (`kinds_tailRanked`), there
is no assumption left (`stheorem1`).
-/

namespace BoltCore.Alg

open State
open BoltCore.Sorted (Srt)

/-! ## Fields of inferred records -/

/-- The fields as a list of label and type. -/
def SFields.sList : SFields → List (String × Sorted.Ty .ty)
  | .nil => []
  | .cons n f fs => (n, f.sTy) :: fs.sList

/-- Every field is present: none is `Abs`. -/
def SFields.Pres : SFields → Prop
  | .nil => True
  | .cons _ f fs => f ≠ .abs ∧ fs.Pres

theorem SFields.sRowOn_pres {ρ : Sorted.Ty .row} :
    ∀ {F : SFields}, F.Pres → F.sRowOn ρ = Sorted.Ty.ofFields F.sList ρ
  | .nil, _ => rfl
  | .cons n f F, ⟨hf, hF⟩ => by
    rw [SFields.sRowOn_cons, SType.sField_of_ne hf, SFields.sRowOn_pres hF]; rfl

theorem SFields.sRowOn_absOf {ρ : Sorted.Ty .row} :
    ∀ F : SFields, F.absOf.sRowOn ρ = Sorted.Ty.absFields F.sList ρ
  | .nil => rfl
  | .cons n f F => by
    simp only [SFields.absOf, SFields.sRowOn_cons, SFields.sRowOn_absOf F]; rfl

theorem SFields.Pres.rename {f : Nat → Nat} : ∀ {F : SFields}, F.Pres → (F.rename f).Pres
  | .nil, _ => trivial
  | .cons _ _ _, ⟨hg, hF⟩ => ⟨SType.rename_ne_abs hg, hF.rename⟩

/-! ## Contexts -/

def SCtx.sCtxR (f : Nat → Nat) (Γ : SCtx) : Sorted.Ctx :=
  Γ.map fun p => (p.1, Sorted.Scheme.mono (p.2.rename f).sTy)

def SCtx.sCtx (Γ : SCtx) : Sorted.Ctx := Γ.map fun p => (p.1, Sorted.Scheme.mono p.2.sTy)

theorem SCtx.sCtxR_id (Γ : SCtx) : Γ.sCtxR id = Γ.sCtx := by
  simp only [SCtx.sCtxR, SCtx.sCtx, SType.rename_id]

theorem SCtx.lookup_sCtxR {f : Nat → Nat} : ∀ {Γ : SCtx} {x : String} {st : SType},
    Γ.lookup x = some st → (Γ.sCtxR f).lookup x = some (.mono (st.rename f).sTy)
  | [], _, _, h => by simp [SCtx.lookup] at h
  | (y, t) :: Γ, x, st, h => by
    simp only [SCtx.lookup, List.find?_cons] at h
    simp only [SCtx.sCtxR, List.map_cons, Sorted.Ctx.lookup, List.find?_cons]
    by_cases hy : y = x
    · simp only [hy, decide_true] at h ⊢
      simp at h
      subst h
      rfl
    · simp only [hy, decide_false] at h ⊢
      have := SCtx.lookup_sCtxR (f := f) (Γ := Γ) h
      simpa [SCtx.sCtxR, Sorted.Ctx.lookup] using this

/-! ## The theorem -/

/-- What the renamed proof needs: accepted constraints whose left side is
not `Abs` hold, renamed, at the type sort. -/
structure SRenSound (E : Sorted.Defs) (f : Nat → Nat) (sf : State) : Prop where
  sub : ∀ {s : State} {a b : SType}, Logged s a b → (∀ p, p ∈ s.log → p ∈ sf.log) → a ≠ .abs →
    Sorted.Sub E (a.rename f).sTy (b.rename f).sTy

theorem Final.srenSound {sf : State} {rank : Nat → Nat} (hf : Final sf rank) :
    SRenSound (sdefsOf sf) id sf where
  sub := fun hl hlog ha => by
    simp only [SType.rename_id]
    exact ssolution_ty hf.inv hf.nac hf.ranked (hl.of_log hlog) (.inl ha)

mutual
/-- **Theorem 1, renamed and sorted.** -/
theorem TypeTerm.ssoundR {E : Sorted.Defs} {f : Nat → Nat} {sf : State} (H : SRenSound E f sf) :
    TypeTerm Γ s t st s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ sf.log) →
    Sorted.Typ E (Γ.sCtxR f) t (st.rename f).sTy
  | .lit, _, _, _, _ => .lit
  | .var hx, _, _, _, _ => Sorted.Typ.var_mono (SCtx.lookup_sCtxR hx)
  | .lam _ h, hΓ, i, n, hlog =>
    .lam (h.ssoundR H (hΓ.cons trivial (fun h => nomatch h)) i.fresh n hlog)
  | .app _ h₁ h₂ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i.fresh
    have r₁ := h₁.nac hΓ i.fresh n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .app (.sub (h₁.ssoundR H hΓ i.fresh n hlog₁) (H.sub hc.logged hlog r₁.2.2))
      (h₂.ssoundR H hΓ i₁ r₁.1 hlog₂)
  | .rcd (F := F) h, hΓ, i, n, hlog => by
    obtain ⟨hF, hp⟩ := h.ssoundR H hΓ i n hlog
    have e : ((SType.record F .abs).rename f).sTy = Sorted.Ty.record (F.rename f).sList := by
      simp only [SType.rename, SType.sTy, Sorted.Ty.record]
      exact congrArg Sorted.Ty.rcd (SFields.sRowOn_pres hp.rename)
    rw [e]
    exact .rcd hF
  | .sel _ h hc, hΓ, i, n, hlog => by
    have r := h.nac hΓ i.fresh n
    exact .sel (.sub (h.ssoundR H hΓ i.fresh n (fun p hp => hlog p (hc.log_grows p hp)))
      (H.sub hc.logged hlog r.2.2))
  | .extNil h, hΓ, i, n, hlog => .extNil (h.ssoundR H hΓ i n hlog)
  | .ext (F := F) (s₂ := s₂) _ h₁ h₂ _ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i
    have r₁ := h₁.nac hΓ i n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    have hs := H.sub hc.logged hlog r₁.2.2
    simp only [SType.rename, SFields.rename_absOf, SType.sTy, SFields.sRowOn_absOf] at hs
    obtain ⟨hF, hp⟩ := h₂.ssoundR H hΓ i₁ r₁.1 hlog₂
    have e : ((SType.record F (.var s₂.next)).rename f).sTy =
        .rcd (Sorted.Ty.ofFields (F.rename f).sList (.gvar (f s₂.next))) := by
      simp only [SType.rename, SType.sTy, SType.sRow]
      exact congrArg Sorted.Ty.rcd (SFields.sRowOn_pres hp.rename)
    rw [e]
    exact .ext (.sub (h₁.ssoundR H hΓ i n hlog₁) hs) hF
  | .letIn h₁ h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac hΓ i n
    exact Sorted.Typ.letIn_mono (h₁.ssoundR H hΓ i n (fun p hp => hlog p (h₂.log_grows p hp)))
      (h₂.ssoundR H (hΓ.cons r₁.2.1 r₁.2.2) (h₁.inv₂ i) r₁.1 hlog)
  | .letRec hf _ h₁ hc h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac (hΓ.cons trivial (fun h => nomatch h)) i.fresh n
    have i₁ := h₁.inv₂ i.fresh
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (h₂.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact Sorted.Typ.letRec_mono hf
      (.sub (h₁.ssoundR H (hΓ.cons trivial (fun h => nomatch h)) i.fresh n hlog₁)
        (H.sub hc.logged hlog₂ r₁.2.2))
      (h₂.ssoundR H (hΓ.cons trivial (fun h => nomatch h)) (hc.inv₂ i₁)
        (hc.nac i₁ r₁.2.1 trivial r₁.1) hlog)

/-- Fields: their typing, and that every field is present. -/
theorem TypeFields.ssoundR {E : Sorted.Defs} {f : Nat → Nat} {sf : State} (H : SRenSound E f sf) :
    TypeFields Γ s fs F s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ sf.log) →
    Sorted.TypFields E (Γ.sCtxR f) fs (F.rename f).sList ∧ F.Pres
  | .nil, _, _, _, _ => ⟨.nil, trivial⟩
  | .cons h₁ h₂, hΓ, i, n, hlog =>
    have r₁ := h₁.nac hΓ i n
    have ih := h₂.ssoundR H hΓ (h₁.inv₂ i) r₁.1 hlog
    ⟨.cons (h₁.ssoundR H hΓ i n (fun p hp => hlog p (h₂.log_grows p hp))) ih.1, r₁.2.2, ih.2⟩
end

/-- **Theorem 1, sorted**, for the solution of any later state with the
invariants. -/
theorem TypeTerm.ssound {rank : Nat → Nat} {sf : State} (hf : Final sf rank)
    (h : TypeTerm Γ s t st s') (hΓ : CtxNAC Γ) (i : Inv₂ s) (n : LogNAC s)
    (hlog : ∀ p, p ∈ s'.log → p ∈ sf.log) :
    Sorted.Typ (sdefsOf sf) Γ.sCtx t st.sTy := by
  have := h.ssoundR hf.srenSound hΓ i n hlog
  rwa [SCtx.sCtxR_id, SType.rename_id] at this

/-- **Theorem 1, sorted, with no assumption left**: if the algorithm types
`t` with `st` in the built-in context, for the kinds `K` of its run, ending
in state `s'`, then `t : θ(st)` in the sorted declarative system, where `θ`
is the sorted solution of `s'`. -/
theorem stheorem1 {K : Nat → List String} (h : TypeTerm builtins (State.initK K) t st s') :
    Sorted.Typ (sdefsOf s') builtins.sCtx t st.sTy := by
  have hn := h.nac builtins_NAC Inv₂.init LogNAC.init
  have hr := kinds_tailRanked (h.kinds builtins_K Inv₂.init KInv.init).1 (h.inv₂ Inv₂.init).inLog
  exact TypeTerm.ssound ⟨h.inv_init, (h.inv₂ Inv₂.init).inLog, hn.1, hr⟩ h builtins_NAC Inv₂.init
    LogNAC.init (fun _ hp => hp)

end BoltCore.Alg
