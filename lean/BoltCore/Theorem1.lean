import BoltCore.SolutionRows
import BoltCore.Typing

/-!
# Theorem 1: soundness of type inference

If the algorithm types a term, the term has the inferred type, translated
through the solution, in the declarative system (`Typ`, over `Sub`). This
is the paper's Theorem 1 for our model (monomorphic `let`, rows, no
structural recursive types).

The solution is the one for the *final* state: every constraint accepted
along the way is still logged there (the log only grows), so the solution
theorem relates all of them at once. Each `constrain` the algorithm
performed becomes a subsumption step, at the type sort since its left side
is an inferred type, never `Abs` (`TypeTerm.nac`). A selection needs no
side condition: the typing rule asks for a present field (`pre τ`) by its
shape. Record literals and extensions need their field types to be present
(not `Abs`), which inferred types are.
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

mutual
theorem TypeTerm.log_grows : TypeTerm Γ s t st s' → ∀ p, p ∈ s.log → p ∈ s'.log
  | .lit => fun _ h => h
  | .var _ => fun _ h => h
  | .lam _ h => h.log_grows
  | .app _ h₁ h₂ hc => fun p hp => hc.log_grows p (h₂.log_grows p (h₁.log_grows p hp))
  | .rcd h => h.log_grows
  | .sel _ h hc => fun p hp => hc.log_grows p (h.log_grows p hp)
  | .ite _ hc h₁ ha h₂ hb h₃ => fun p hp =>
    h₃.log_grows p (hb.log_grows p (h₂.log_grows p (ha.log_grows p (h₁.log_grows p
      (hc.log_grows p hp)))))
  | .selOr _ h hc hd hc' => fun p hp =>
    hc'.log_grows p (hd.log_grows p (hc.log_grows p (h.log_grows p hp)))
  | .ext _ h₁ h₂ _ hc => fun p hp => hc.log_grows p (h₂.log_grows p (h₁.log_grows p hp))
  | .extNil h => h.log_grows
  | .letIn h₁ h₂ => fun p hp => h₂.log_grows p (h₁.log_grows p hp)
  | .letRec _ _ h₁ hc h₂ => fun p hp => h₂.log_grows p (hc.log_grows p (h₁.log_grows p hp))
  | .fn _ hp h => fun p hp' => h.log_grows p (hp.log_grows p hp')

theorem TypeFields.log_grows : TypeFields Γ s fs F s' → ∀ p, p ∈ s.log → p ∈ s'.log
  | .nil => fun _ h => h
  | .cons h₁ h₂ => fun p hp => h₂.log_grows p (h₁.log_grows p hp)

theorem TypeParams.log_grows : TypeParams Γ s ps P Γ' s' → ∀ p, p ∈ s.log → p ∈ s'.log
  | .nil => fun _ h => h
  | .req _ h => h.log_grows
  | .dflt _ hd hc h => fun p hp => h.log_grows p (hc.log_grows p (hd.log_grows p hp))
end

theorem ConstrainTop.kind_eq {s s' : State} (h : ConstrainTop s a b s') : s'.kind = s.kind := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact hc.grows.kind

mutual
/-- Typing never changes the kinds. -/
theorem TypeTerm.kind_eq : TypeTerm Γ s t st s' → s'.kind = s.kind
  | .lit => rfl
  | .var _ => rfl
  | .lam _ h => h.kind_eq
  | .app _ h₁ h₂ hc => (hc.kind_eq.trans h₂.kind_eq).trans h₁.kind_eq
  | .rcd h => h.kind_eq
  | .sel _ h hc => hc.kind_eq.trans h.kind_eq
  | .ite _ hc h₁ ha h₂ hb h₃ =>
    ((((h₃.kind_eq.trans hb.kind_eq).trans h₂.kind_eq).trans ha.kind_eq).trans h₁.kind_eq).trans
      hc.kind_eq
  | .selOr _ h hc hd hc' => ((hc'.kind_eq.trans hd.kind_eq).trans hc.kind_eq).trans h.kind_eq
  | .ext _ h₁ h₂ _ hc => (hc.kind_eq.trans h₂.kind_eq).trans h₁.kind_eq
  | .extNil h => h.kind_eq
  | .letIn h₁ h₂ => h₂.kind_eq.trans h₁.kind_eq
  | .letRec _ _ h₁ hc h₂ => (h₂.kind_eq.trans hc.kind_eq).trans h₁.kind_eq
  | .fn _ hp h => h.kind_eq.trans hp.kind_eq

theorem TypeFields.kind_eq : TypeFields Γ s fs F s' → s'.kind = s.kind
  | .nil => rfl
  | .cons h₁ h₂ => h₂.kind_eq.trans h₁.kind_eq

theorem TypeParams.kind_eq : TypeParams Γ s ps P Γ' s' → s'.kind = s.kind
  | .nil => rfl
  | .req _ h => h.kind_eq
  | .dflt _ hd hc h => (h.kind_eq.trans hc.kind_eq).trans hd.kind_eq
end

/-! ## The theorem -/

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

/-! ## Renaming type variables

Let-polymorphism instantiates a type scheme by copying its generalized
variables: a *renaming*. The soundness proof below is stated for any
renaming `f` of the type variables, given that the renamed accepted
constraints hold; the plain theorem is the case `f = id`. -/

mutual
def SType.rename (f : Nat → Nat) : SType → SType
  | .var v => .var (f v)
  | .prim n => .prim n
  | .arrow a b => .arrow (a.rename f) (b.rename f)
  | .record fs t => .record (fs.rename f) (t.rename f)
  | .abs => .abs
  | .missing => .missing
  | .opt t => .opt (t.rename f)
  | .nil => .nil
  | .sig P => .sig (P.rename f)

def SFields.rename (f : Nat → Nat) : SFields → SFields
  | .nil => .nil
  | .cons n g fs => .cons n (g.rename f) (fs.rename f)

def SParams.rename (f : Nat → Nat) : SParams → SParams
  | .nil => .nil
  | .cons n k o τ P => .cons n k o (τ.rename f) (P.rename f)
end

mutual
theorem SType.rename_id : ∀ a : SType, a.rename id = a
  | .var _ | .prim _ | .abs | .missing | .nil => rfl
  | .opt t => by simp only [SType.rename, SType.rename_id t]
  | .arrow a b => by simp only [SType.rename, SType.rename_id a, SType.rename_id b]
  | .record fs t => by simp only [SType.rename, SFields.rename_id fs, SType.rename_id t]
  | .sig P => by simp only [SType.rename, SParams.rename_id P]

theorem SFields.rename_id : ∀ fs : SFields, fs.rename id = fs
  | .nil => rfl
  | .cons _ g fs => by simp only [SFields.rename, SType.rename_id g, SFields.rename_id fs]

theorem SParams.rename_id : ∀ P : SParams, P.rename id = P
  | .nil => rfl
  | .cons _ _ _ τ P => by simp only [SParams.rename, SType.rename_id τ, SParams.rename_id P]
end

theorem SFields.rename_absOf (f : Nat → Nat) : ∀ F : SFields, F.absOf.rename f = (F.rename f).absOf
  | .nil => rfl
  | .cons _ _ F => by simp only [SFields.absOf, SFields.rename, SType.rename, SFields.rename_absOf f F]

theorem SType.rename_ne_abs {f : Nat → Nat} : ∀ {a : SType}, a ≠ .abs → a.rename f ≠ .abs
  | .var _, _ | .prim _, _ | .arrow _ _, _ | .record _ _, _
  | .missing, _ | .opt _, _ | .nil, _ | .sig _, _ => fun h => nomatch h
  | .abs, h => absurd rfl h

theorem SType.IsPre.rename {f : Nat → Nat} : ∀ {a : SType}, a.IsPre → (a.rename f).IsPre
  | .var _, _ | .prim _, _ | .arrow _ _, _ | .record _ _, _ | .nil, _ | .sig _, _ => trivial
  | .abs, h | .missing, h | .opt _, h => absurd h id

theorem SParams.toList_rename (f : Nat → Nat) : ∀ P : SParams,
    (P.rename f).toList = P.toList.map (Param.map (·.rename f))
  | .nil => rfl
  | .cons _ _ _ _ P => by
    simp only [SParams.rename, SParams.toList, List.map_cons, SParams.toList_rename f P]; rfl

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

/-! ## Contexts -/

def SCtx.toCtxR (f : Nat → Nat) (Γ : SCtx) : Ctx :=
  Γ.map fun p => (p.1, Scheme.mono (p.2.rename f).toTy)

def SCtx.toCtx (Γ : SCtx) : Ctx := Γ.map fun p => (p.1, Scheme.mono p.2.toTy)

theorem SCtx.toCtxR_id (Γ : SCtx) : Γ.toCtxR id = Γ.toCtx := by
  simp only [SCtx.toCtxR, SCtx.toCtx, SType.rename_id]

theorem SCtx.lookup_toCtxR {f : Nat → Nat} {Γ : SCtx} {x : String} {st : SType}
    (h : Γ.lookup x = some st) : (Γ.toCtxR f).lookup x = some (.mono (st.rename f).toTy) := by
  simp only [SCtx.lookup] at h
  simp only [Ctx.lookup, SCtx.toCtxR]
  rw [lookup_map (fun t : SType => Scheme.mono (t.rename f).toTy), h]; rfl

/-! ## The theorem -/

/-- What the renamed proof needs: accepted constraints whose left side is
not `Abs` hold, renamed, at the type sort. -/
structure RenSound (E : Defs) (f : Nat → Nat) (sf : State) : Prop where
  sub : ∀ {s : State} {a b : SType}, Logged s a b → (∀ p, p ∈ s.log → p ∈ sf.log) → a ≠ .abs →
    Sub E (a.rename f).toTy (b.rename f).toTy

theorem Final.renSound {sf : State} {rank : Nat → Nat} (hf : Final sf rank) :
    RenSound (defsOf sf) id sf where
  sub := fun hl hlog ha => by
    simp only [SType.rename_id]
    exact solution_ty hf.inv hf.nac hf.ranked (hl.of_log hlog) (.inl ha)

mutual
/-- **Theorem 1, renamed**: if the algorithm types `t` with `st`, and the
accepted constraints hold (renamed by `f`) in `E`, then `t` has the renamed
type `f(st)` in the renamed context. -/
theorem TypeTerm.soundR {E : Defs} {f : Nat → Nat} {sf : State} (H : RenSound E f sf) :
    TypeTerm Γ s t st s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ sf.log) →
    Typ E (Γ.toCtxR f) t (st.rename f).toTy
  | .lit, _, _, _, _ => .lit
  | .var hx, _, _, _, _ => Typ.var_mono (SCtx.lookup_toCtxR hx)
  | .lam _ h, hΓ, i, n, hlog =>
    .lam (h.soundR H (hΓ.cons trivial trivial) i.fresh n hlog)
  | .app _ h₁ h₂ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i.fresh
    have r₁ := h₁.nac hΓ i.fresh n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    exact .app (.sub (h₁.soundR H hΓ i.fresh n hlog₁) (H.sub hc.logged hlog r₁.2.2.ne_abs))
      (h₂.soundR H hΓ i₁ r₁.1 hlog₂)
  | .rcd (F := F) h, hΓ, i, n, hlog => by
    obtain ⟨hF, hp⟩ := h.soundR H hΓ i n hlog
    have e : ((SType.record F .nil).rename f).toTy = Ty.record (F.rename f).toList := by
      simp only [SType.rename, SType.toTy, Ty.record]
      exact congrArg Ty.rcd (SFields.toRowOnI_pres hp.rename)
    rw [e]
    exact .rcd hF
  | .sel _ h hc, hΓ, i, n, hlog => by
    have r := h.nac hΓ i.fresh n
    exact .sel (.sub (h.soundR H hΓ i.fresh n (fun p hp => hlog p (hc.log_grows p hp)))
      (H.sub hc.logged hlog r.2.2.ne_abs))
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
    have hlog₅ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (h₃.log_grows p hp)
    have hlog₄ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₅ p (hb.log_grows p hp)
    have hlog₃ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₄ p (h₂.log_grows p hp)
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₃ p (ha.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (h₁.log_grows p hp)
    exact .ite (.sub (hc.soundR H hΓ i.fresh n hlog₁) (H.sub h₁.logged hlog₂ rc.2.2.ne_abs))
      (.sub (ha.soundR H hΓ i₂ n₁ hlog₃) (H.sub h₂.logged hlog₄ ra.2.2.ne_abs))
      (.sub (hb.soundR H hΓ i₄ n₂ hlog₅) (H.sub h₃.logged hlog rb.2.2.ne_abs))
  | .selOr _ h hc hd hc', hΓ, i, n, hlog => by
    have r := h.nac hΓ i.fresh n
    have i₁ := h.inv₂ i.fresh
    have n₂ := hc.nac i₁ r.2.1 ⟨⟨trivial, trivial⟩, trivial⟩ r.1
    have i₂ := hc.inv₂ i₁
    have rd := hd.nac hΓ i₂ n₂
    have hlog₃ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (hc'.log_grows p hp)
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₃ p (hd.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact .selOr (.sub (h.soundR H hΓ i.fresh n hlog₁) (H.sub hc.logged hlog₂ r.2.2.ne_abs))
      (.sub (hd.soundR H hΓ i₂ n₂ hlog₃) (H.sub hc'.logged hlog rd.2.2.ne_abs))
  | .extNil h, hΓ, i, n, hlog => .extNil (h.soundR H hΓ i n hlog)
  | .ext (F := F) (s₂ := s₂) _ h₁ h₂ _ hc, hΓ, i, n, hlog => by
    have i₁ := h₁.inv₂ i
    have r₁ := h₁.nac hΓ i n
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (hc.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (h₂.log_grows p hp)
    have hs := H.sub hc.logged hlog r₁.2.2.ne_abs
    have e' : ((SType.record F.absOf (.var s₂.next)).rename f).toTy =
        .rcd (Ty.absFields (F.rename f).toList (.gvar (f s₂.next))) := by
      simp only [SType.rename, SFields.rename_absOf]
      exact congrArg Ty.rcd (SFields.toRowOnI_absOf _)
    rw [e'] at hs
    obtain ⟨hF, hp⟩ := h₂.soundR H hΓ i₁ r₁.1 hlog₂
    have e : ((SType.record F (.var s₂.next)).rename f).toTy =
        .rcd (Ty.ofFields (F.rename f).toList (.gvar (f s₂.next))) := by
      simp only [SType.rename]
      exact congrArg Ty.rcd (SFields.toRowOnI_pres hp.rename)
    rw [e]
    exact .ext (.sub (h₁.soundR H hΓ i n hlog₁) hs) hF
  | .letIn h₁ h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac hΓ i n
    exact Typ.letIn_mono (h₁.soundR H hΓ i n (fun p hp => hlog p (h₂.log_grows p hp)))
      (h₂.soundR H (hΓ.cons r₁.2.1 r₁.2.2) (h₁.inv₂ i) r₁.1 hlog)
  | .letRec hf _ h₁ hc h₂, hΓ, i, n, hlog => by
    have r₁ := h₁.nac (hΓ.cons trivial trivial) i.fresh n
    have i₁ := h₁.inv₂ i.fresh
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (h₂.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact Typ.letRec_mono hf
      (.sub (h₁.soundR H (hΓ.cons trivial trivial) i.fresh n hlog₁)
        (H.sub hc.logged hlog₂ r₁.2.2.ne_abs))
      (h₂.soundR H (hΓ.cons trivial trivial) (hc.inv₂ i₁)
        (hc.nac i₁ r₁.2.1 trivial r₁.1) hlog)
  | .fn (P := P) hw hp h, hΓ, i, n, hlog => by
    have rp := hp.nac hΓ i n
    have hw' : Param.WF ((P.rename f).toParamsI .gv) := by
      rw [SParams.toParamsI_eq, SParams.toList_rename]
      exact (hw.map _).map _
    exact .fn hw' (hp.soundR H hΓ i n (fun p hp' => hlog p (h.log_grows p hp')))
      (h.soundR H rp.2.2 (hp.inv₂ i) rp.1 hlog)

/-- Fields: their typing, and that every field is present. -/
theorem TypeFields.soundR {E : Defs} {f : Nat → Nat} {sf : State} (H : RenSound E f sf) :
    TypeFields Γ s fs F s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ sf.log) →
    TypFields E (Γ.toCtxR f) fs (F.rename f).toList ∧ F.Pres
  | .nil, _, _, _, _ => ⟨.nil, trivial⟩
  | .cons h₁ h₂, hΓ, i, n, hlog =>
    have r₁ := h₁.nac hΓ i n
    have ih := h₂.soundR H hΓ (h₁.inv₂ i) r₁.1 hlog
    ⟨.cons (h₁.soundR H hΓ i n (fun p hp => hlog p (h₂.log_grows p hp))) ih.1, r₁.2.2, ih.2⟩

/-- Parameters: each default has its parameter's type, and the body's
context is the translated one. -/
theorem TypeParams.soundR {E : Defs} {f : Nat → Nat} {sf : State} (H : RenSound E f sf) :
    TypeParams Γ s ps P Γ' s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    (∀ p, p ∈ s'.log → p ∈ sf.log) →
    TypParams E (Γ.toCtxR f) ps ((P.rename f).toParamsI .gv) (Γ'.toCtxR f)
  | .nil, _, _, _, _ => .nil
  | .req _ h, hΓ, i, n, hlog => .req (h.soundR H (hΓ.cons trivial trivial) i.fresh n hlog)
  | .dflt _ hd hc h, hΓ, i, n, hlog => by
    have rd := hd.nac hΓ i.fresh n
    have i₁ := hd.inv₂ i.fresh
    have hlog₂ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog p (h.log_grows p hp)
    have hlog₁ : ∀ p, p ∈ _ → p ∈ sf.log := fun p hp => hlog₂ p (hc.log_grows p hp)
    exact .dflt (.sub (hd.soundR H hΓ i.fresh n hlog₁) (H.sub hc.logged hlog₂ rd.2.2.ne_abs))
      (h.soundR H (hΓ.cons trivial trivial) (hc.inv₂ i₁) (hc.nac i₁ rd.2.1 trivial rd.1) hlog)
end

/-- **Theorem 1** (soundness of inference): if the algorithm types `t` with
`st`, starting from a state and context satisfying the invariants, then `t`
has type `θ(st)` in the declarative system, for the solution `θ` of any
later state with the invariants (in particular the final one). -/
theorem TypeTerm.sound {rank : Nat → Nat} {sf : State} (hf : Final sf rank)
    (h : TypeTerm Γ s t st s') (hΓ : CtxNAC Γ) (i : Inv₂ s) (n : LogNAC s)
    (hlog : ∀ p, p ∈ s'.log → p ∈ sf.log) :
    Typ (defsOf sf) Γ.toCtx t st.toTy := by
  have := h.soundR hf.renSound hΓ i n hlog
  rwa [SCtx.toCtxR_id, SType.rename_id] at this


/-- **Theorem 1, from scratch**: if the algorithm types `t` with `st` in the
built-in context, ending in state `s'`, and the row-variable tails of `s'`
are acyclic, then `t : θ(st)` in the declarative system, where `θ` is the
solution of `s'`. Kinds discharge the acyclicity assumption (`theorem1` in
`Kinds.lean`). -/
theorem soundness {K : Nat → List String} {rank : Nat → Nat}
    (h : TypeTerm builtins (State.initK K) t st s') (hr : TailRanked s' rank) :
    Typ (defsOf s') builtins.toCtx t st.toTy := by
  have hn := h.nac builtins_NAC Inv₂.init LogNAC.init
  exact TypeTerm.sound ⟨h.inv_init, (h.inv₂ Inv₂.init).inLog, hn.1, hr⟩ h builtins_NAC Inv₂.init
    LogNAC.init (fun _ hp => hp)

end BoltCore.Alg
