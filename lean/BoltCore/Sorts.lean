import BoltCore.Solution

/-!
# `Abs` never occurs as a component of a function type

`Abs` (the top field, and the top row) only ever occurs in field and row
tail positions: never as a parameter or result type. This matters for the
solution (`SolutionRows.lean`): `Abs` is the top of `Sub` (`x ≤ Abs` for
every `x`), so `Abs ≤ {…}` must stay false at the level of types, and the
type-level part of the solution proof must never meet `Abs` on the left.

`NAC` ("no `Abs` component") says that every function type inside a simple
type has non-`Abs` parameter and result, and that the parameters of a
signature are types (`IsPre`), so that an argument record of the signature
translates to the argument record of the translated parameters. We prove that every constraint the
algorithm accepts is `NAC`, and that the types it infers for terms are
`NAC` and are types (`IsPre`: not `Abs`, `Missing` or `Opt τ`).
-/

namespace BoltCore.Alg

open State

mutual
def SType.NAC : SType → Prop
  | .arrow a b => a ≠ .abs ∧ b ≠ .abs ∧ a.NAC ∧ b.NAC
  | .record fs t => fs.NAC ∧ t.NAC
  | .opt t => t.NAC
  | .sig P => P.NAC
  | _ => True

def SFields.NAC : SFields → Prop
  | .nil => True
  | .cons _ f fs => f.NAC ∧ fs.NAC

def SParams.NAC : SParams → Prop
  | .nil => True
  | .cons _ _ _ τ P => τ.IsPre ∧ τ.NAC ∧ P.NAC
end

/-- Every accepted constraint is `NAC`. -/
def LogNAC (s : State) : Prop := ∀ p, p ∈ s.log → p.1.NAC ∧ p.2.NAC

theorem SFields.NAC.append : ∀ {fs gs : SFields}, fs.NAC → gs.NAC → (fs.append gs).NAC
  | .nil, _, _, h₂ => h₂
  | .cons _ _ _, _, h₁, h₂ => ⟨h₁.1, SFields.NAC.append h₁.2 h₂⟩

theorem rowView_NAC : ∀ x : SType, x.NAC → (rowView x).1.NAC ∧ (rowView x).2.NAC
  | .record fs t, ⟨hfs, ht⟩ => by
    have := rowView_NAC t ht
    simp only [rowView]
    exact ⟨hfs.append this.1, this.2⟩
  | .var _, _ | .prim _, _ | .abs, _ | .missing, _ | .nil, _ => ⟨trivial, trivial⟩
  | .arrow _ _, h | .opt _, h | .sig _, h => ⟨trivial, h⟩

/-! ## Argument records -/

theorem SParams.NAC.mem : ∀ {P : SParams}, P.NAC → ∀ p ∈ P.toList, p.ty.IsPre ∧ p.ty.NAC
  | .nil, _, _, h => nomatch h
  | .cons _ _ _ _ _, ⟨h₁, h₂, h₃⟩, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨h₁, h₂⟩
    · exact h₃.mem p hp

theorem SType.list_NAC : ∀ {τs : List SType}, (∀ τ ∈ τs, τ.NAC) → (SType.list τs).NAC
  | [], _ => ⟨trivial, trivial⟩
  | τ :: _, h =>
    ⟨⟨h τ (List.mem_cons_self ..),
      SType.list_NAC fun σ hσ => h σ (List.mem_cons_of_mem _ hσ), trivial⟩, trivial⟩

theorem SFields.ofParams_NAC : ∀ {ps : List (Param SType)}, (∀ p ∈ ps, p.ty.NAC) →
    (SFields.ofParams ps).NAC
  | [], _ => trivial
  | p :: _, h => by
    refine ⟨?_, SFields.ofParams_NAC fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
    have := h p (List.mem_cons_self ..)
    cases ho : p.opt <;> simpa [SType.NAC] using this

/-- The argument records of a `NAC` signature are `NAC`. -/
theorem SParams.NAC.domain {P : SParams} (h : P.NAC) (k : Nat) : (P.domain k).NAC :=
  ⟨⟨SType.list_NAC fun _ hτ => by
      obtain ⟨p, hp, rfl⟩ := Param.mem_pos hτ
      exact (h.mem p hp).2,
    SFields.ofParams_NAC fun p hp => (h.mem p (Param.mem_named hp)).2⟩, trivial⟩

theorem SParams.NAC.domains {P : SParams} (h : P.NAC) : ∀ d ∈ P.domains, d.NAC := fun d hd => by
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
  exact h.domain k

theorem SFields.NAC.lookup : ∀ {fs : SFields}, fs.NAC → fs.lookup l = some f → f.NAC
  | .nil, _, h => by simp [SFields.lookup] at h
  | .cons n g rest, ⟨hg, hr⟩, h => by
    simp only [SFields.lookup] at h
    split at h
    · cases h; exact hg
    · exact hr.lookup h

theorem SFields.NAC.common {fs₀ : SFields} (h₀ : fs₀.NAC) : ∀ {fs₁ : SFields}, fs₁.NAC →
    ∀ p, p ∈ fs₀.common fs₁ → p.1.NAC ∧ p.2.NAC
  | .nil, _, _, h => nomatch h
  | .cons n g rest, ⟨hg, hr⟩, p, hp => by
    simp only [SFields.common] at hp
    split at hp
    · next f hf =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨h₀.lookup hf, hg⟩
      · exact h₀.common hr p hp
    · exact h₀.common hr p hp

theorem SFields.NAC.missing {fs₀ : SFields} : ∀ {fs₁ : SFields}, fs₁.NAC → (fs₀.missing fs₁).NAC
  | .nil, _ => trivial
  | .cons n g rest, ⟨hg, hr⟩ => by
    simp only [SFields.missing]
    split
    · exact hr.missing
    · exact ⟨hg, hr.missing⟩

theorem SFields.NAC.absPairs : ∀ {fs : SFields}, fs.NAC →
    ∀ p, p ∈ fs.absPairs → p.1.NAC ∧ p.2.NAC
  | .nil, _, _, h => nomatch h
  | .cons _ f rest, ⟨hf, hr⟩, p, hp => by
    simp only [SFields.absPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨trivial, hf⟩
    · exact hr.absPairs p hp

theorem SFields.NAC.misPairs : ∀ {fs : SFields}, fs.NAC →
    ∀ p, p ∈ fs.misPairs → p.1.NAC ∧ p.2.NAC
  | .nil, _, _, h => nomatch h
  | .cons _ f rest, ⟨hf, hr⟩, p, hp => by
    simp only [SFields.misPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨trivial, hf⟩
    · exact hr.misPairs p hp

theorem SFields.NAC.toMisPairs : ∀ {fs : SFields}, fs.NAC →
    ∀ p, p ∈ fs.toMisPairs → p.1.NAC ∧ p.2.NAC
  | .nil, _, _, h => nomatch h
  | .cons _ f rest, ⟨hf, hr⟩, p, hp => by
    simp only [SFields.toMisPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨hf, trivial⟩
    · exact hr.toMisPairs p hp

theorem SFields.NAC.absOf : ∀ {fs : SFields}, (fs.absOf).NAC
  | .nil => trivial
  | .cons _ _ _ => ⟨trivial, SFields.NAC.absOf⟩

theorem SFields.NAC.absentIn {K : List String} : ∀ {fs : SFields}, fs.NAC → (fs.absentIn K).NAC
  | .nil, _ => trivial
  | .cons n _ _, ⟨hf, hr⟩ => by
    simp only [SFields.absentIn]; split
    · exact ⟨hf, hr.absentIn⟩
    · exact hr.absentIn

theorem SFields.NAC.presentIn {K : List String} : ∀ {fs : SFields}, fs.NAC → (fs.presentIn K).NAC
  | .nil, _ => trivial
  | .cons n _ _, ⟨hf, hr⟩ => by
    simp only [SFields.presentIn]; split
    · exact hr.presentIn
    · exact ⟨hf, hr.presentIn⟩

theorem restRow_NAC {ex : SFields} {t : SType} (he : ex.NAC) (ht : t.NAC) : (restRow ex t).NAC := by
  cases ex with
  | nil => exact ht
  | cons => exact ⟨he, ht⟩

theorem LogNAC.remember {s : State} (h : LogNAC s) (ha : a.NAC) (hb : b.NAC) :
    LogNAC (s.remember a b) := by
  intro p hp
  simp only [State.remember, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ⟨ha, hb⟩
  · exact h p hp

/-- The bounds are `NAC`, since they are in the log. -/
theorem LogNAC.upper {s : State} (h : LogNAC s) (h₂ : Inv₂ s) (hx : x ∈ (s.bounds v).upper) :
    x.NAC := (h _ (h₂.inLog.1 v x hx)).2

theorem LogNAC.lower {s : State} (h : LogNAC s) (h₂ : Inv₂ s) (hx : x ∈ (s.bounds v).lower) :
    x.NAC := (h _ (h₂.inLog.2 v x hx)).1

/-! ## Extrusion -/

theorem LogNAC.logAll {s : State} {ps : List (SType × SType)} (h : LogNAC s)
    (hps : ∀ p ∈ ps, p.1.NAC ∧ p.2.NAC) : LogNAC (s.logAll ps) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hps p hp
  · exact h p hp

theorem polPair_NAC {t t' : SType} (ht : t.NAC) (ht' : t'.NAC) :
    ∀ {pol : Bool}, (polPair pol t t').1.NAC ∧ (polPair pol t t').2.NAC
  | true => ⟨ht, ht'⟩
  | false => ⟨ht', ht⟩

theorem listPairs_NAC : ∀ {as bs : List SType}, (∀ a ∈ as, a.NAC) → (∀ b ∈ bs, b.NAC) →
    ∀ p ∈ listPairs as bs, p.1.NAC ∧ p.2.NAC
  | [], _, _, _, _, hp => nomatch hp
  | _ :: _, [], _, _, _, hp => nomatch hp
  | _ :: _, _ :: _, ha, hb, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨SType.list_NAC ha, SType.list_NAC hb⟩
    · exact listPairs_NAC (fun a h => ha a (List.mem_cons_of_mem _ h))
        (fun b h => hb b (List.mem_cons_of_mem _ h)) p hp

theorem sigPairs_NAC {lo hi : SParams} (hlo : lo.NAC) (hhi : hi.NAC) :
    ∀ p ∈ sigPairs lo hi, p.1.NAC ∧ p.2.NAC := by
  intro p hp
  obtain ⟨k, _, hp⟩ := List.mem_flatMap.mp hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hlo.domain k, hhi⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hlo.domain k, hhi.domain k⟩
  · exact listPairs_NAC
      (fun _ hτ => by obtain ⟨q, hq, rfl⟩ := Param.mem_pos hτ; exact (hlo.mem q hq).2)
      (fun _ hτ => by obtain ⟨q, hq, rfl⟩ := Param.mem_pos hτ; exact (hhi.mem q hq).2) p hp

theorem sigPairsPol_NAC {P P' : SParams} (h : P.NAC) (h' : P'.NAC) :
    ∀ {pol : Bool}, ∀ p ∈ sigPairsPol pol P P', p.1.NAC ∧ p.2.NAC
  | true => sigPairs_NAC h h'
  | false => sigPairs_NAC h' h

mutual
/-- Extrusion keeps the log and its result free of `Abs` components. -/
theorem Extrude.nac : Extrude s c pol lvl t t' s' c' → BoundsInLog s → t.NAC → LogNAC s →
    LogNAC s' ∧ t'.NAC
  | .low _, _, ht, h => ⟨h, ht⟩
  | .arrow _ h₁ h₂, hb, ht, h => by
    have r₁ := h₁.nac hb ht.2.2.1 h
    have r₂ := h₂.nac (h₁.inLog hb) ht.2.2.2 r₁.1
    have ht' : (SType.arrow _ _).NAC := ⟨h₁.ne_abs ht.1, h₂.ne_abs ht.2.1, r₁.2, r₂.2⟩
    exact ⟨r₂.1.logAll fun p hp => by
      have e := List.mem_singleton.mp hp; subst e; exact polPair_NAC ht ht', ht'⟩
  | .record _ h₁ h₂, hb, ht, h => by
    have r₁ := h₁.nac hb ht.1 h
    have r₂ := h₂.nac (h₁.inLog hb) ht.2 r₁.1
    have ht' : (SType.record _ _).NAC := ⟨r₁.2, r₂.2⟩
    exact ⟨r₂.1.logAll fun p hp => by
      have e := List.mem_singleton.mp hp; subst e; exact polPair_NAC ht ht', ht'⟩
  | .sig _ h', hb, ht, h => by
    have r := h'.nac hb ht h
    refine ⟨r.1.logAll fun p hp => ?_, r.2⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact polPair_NAC (t := .sig _) (t' := .sig _) ht r.2
    · exact sigPairsPol_NAC ht r.2 p hp
  | .varCopied _ _, _, _, h =>
    ⟨h.logAll fun p hp => by
      have e := List.mem_singleton.mp hp; subst e
      exact polPair_NAC (t := .var _) (t' := .var _) trivial trivial, trivial⟩
  | .varPos (s := s) (v := v) _ _ _ _ h', hb, _, h => by
    have r := h'.nac (BoundsInLog.addUpperLog (s := s.fresh) hb.fresh)
      (fun t ht => (h _ (hb.2 v t ht)).1)
      (LogNAC.logAll (s := s.fresh.addUpper v (.var s.next)) h fun p hp => by
        have e := List.mem_singleton.mp hp; subst e; exact ⟨trivial, trivial⟩)
    refine ⟨r.1.logAll fun p hp => ?_, trivial⟩
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      exact ⟨r.2 t ht, trivial⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      exact ⟨(h _ (hb.2 v t ht)).1, trivial⟩
  | .varNeg (s := s) (v := v) _ _ _ _ h', hb, _, h => by
    have r := h'.nac (BoundsInLog.addLowerLog (s := s.fresh) hb.fresh)
      (fun t ht => (h _ (hb.1 v t ht)).2)
      (LogNAC.logAll (s := s.fresh.addLower v (.var s.next)) h fun p hp => by
        have e := List.mem_singleton.mp hp; subst e; exact ⟨trivial, trivial⟩)
    refine ⟨r.1.logAll fun p hp => ?_, trivial⟩
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      exact ⟨trivial, r.2 t ht⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      exact ⟨trivial, (h _ (hb.1 v t ht)).2⟩

theorem ExtrudeFields.nac : ExtrudeFields s c pol lvl fs fs' s' c' → BoundsInLog s → fs.NAC →
    LogNAC s → LogNAC s' ∧ fs'.NAC
  | .nil, _, ht, h => ⟨h, ht⟩
  | .opt h₁ h₂, hb, ht, h => by
    have r₁ := h₁.nac hb ht.1 h
    have r₂ := h₂.nac (h₁.inLog hb) ht.2 r₁.1
    exact ⟨r₂.1, r₁.2, r₂.2⟩
  | .cons _ h₁ h₂, hb, ht, h => by
    have r₁ := h₁.nac hb ht.1 h
    have r₂ := h₂.nac (h₁.inLog hb) ht.2 r₁.1
    exact ⟨r₂.1, r₁.2, r₂.2⟩

theorem ExtrudeParams.nac : ExtrudeParams s c pol lvl P P' s' c' → BoundsInLog s → P.NAC →
    LogNAC s → LogNAC s' ∧ P'.NAC
  | .nil, _, ht, h => ⟨h, ht⟩
  | .cons h₁ h₂, hb, ht, h => by
    have r₁ := h₁.nac hb ht.2.1 h
    have r₂ := h₂.nac (h₁.inLog hb) ht.2.2 r₁.1
    exact ⟨r₂.1, h₁.isPre ht.1, r₁.2, r₂.2⟩

theorem ExtrudeEach.nac : ExtrudeEach s c pol lvl ts ts' s' c' → BoundsInLog s →
    (∀ t ∈ ts, t.NAC) → LogNAC s → LogNAC s' ∧ ∀ t' ∈ ts', t'.NAC
  | .nil, _, _, h => ⟨h, fun _ h => nomatch h⟩
  | .cons h₁ h₂, hb, ht, h => by
    have r₁ := h₁.nac hb (ht _ (List.mem_cons_self ..)) h
    have r₂ := h₂.nac (h₁.inLog hb) (fun t h => ht t (List.mem_cons_of_mem _ h)) r₁.1
    refine ⟨r₂.1, fun t' h => ?_⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact r₁.2
    · exact r₂.2 t' h
end

mutual
theorem Constrain.nac : Constrain s a b s' → Inv₂ s → a.NAC → b.NAC → LogNAC s → LogNAC s'
  | .cached _, _, _, _, h => h
  | .refl, _, _, _, h => h
  | .arrow _ h₁ h₂, i, ⟨_, _, ha₁, ha₂⟩, ⟨_, _, hb₁, hb₂⟩, h =>
    have i₁ := h₁.inv₂ i.remember
    h₂.nac i₁ ha₂ hb₂ (h₁.nac i.remember hb₁ ha₁ (h.remember ⟨‹_›, ‹_›, ha₁, ha₂⟩ ⟨‹_›, ‹_›, hb₁, hb₂⟩))
  | .absR _, _, ha, _, h => h.remember ha trivial
  | .absRecord _ h₁ h₂, i, _, ⟨hfs, ht⟩, h =>
    have i₁ := h₁.inv₂ i.remember
    h₂.nac i₁ trivial ht (h₁.nac i.remember (hfs.absPairs) (h.remember trivial ⟨hfs, ht⟩))
  | .nilRecord _ h₁ h₂, i, _, ⟨hfs, ht⟩, h =>
    have i₁ := h₁.inv₂ i.remember
    h₂.nac i₁ trivial ht (h₁.nac i.remember (hfs.misPairs) (h.remember trivial ⟨hfs, ht⟩))
  | .recordNil _ e₀ h₁ h₂, i, ha, _, h => by
    have v₀ := rowView_NAC _ ha
    rw [e₀] at v₀
    have i₁ := h₁.inv₂ i.remember
    exact h₂.nac i₁ v₀.2 trivial (h₁.nac i.remember v₀.1.toMisPairs (h.remember ha trivial))
  | .record _ e₀ e₁ h₁ h₂ h₃, i, ha, hb, h => by
    have v₀ := rowView_NAC _ ha
    have v₁ := rowView_NAC _ hb
    rw [e₀] at v₀
    rw [e₁] at v₁
    have i₁ := h₁.inv₂ i.remember
    have i₂ := h₂.inv₂ i₁
    have n₁ := h₁.nac i.remember (v₀.1.common v₁.1) (h.remember ha hb)
    have n₂ := h₂.nac i₁ v₀.2 v₁.1.missing n₁
    exact h₃.nac i₂ (restRow_NAC v₀.1.missing n₂.2) v₁.2 n₂.1
  | .varL _ _ _ h', i, _, hb, h =>
    h'.nac i.remember.addUpper
      (fun p hp => by
        simp only [List.mem_map] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        exact ⟨h.lower i hx, hb⟩)
      (h.remember trivial hb)
  | .varR _ _ _ h', i, ha, _, h =>
    h'.nac i.remember.addLower
      (fun p hp => by
        simp only [List.mem_map] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        exact ⟨ha, h.upper i hx⟩)
      (h.remember ha trivial)
  | .extLHit _ _ _ hx _, i, ha, hb, h => (hx.nac i.remember.inLog hb (h.remember ha hb)).1
  | .extLNew _ _ _ hx _ h', i, ha, hb, h => by
    have r := hx.nac i.remember.inLog hb (h.remember ha hb)
    have i₁ : Inv₂ _ := ⟨hx.inLog i.remember.inLog⟩
    exact h'.nac i₁.remember.addUpper
      (fun p hp => by
        simp only [List.mem_map] at hp
        obtain ⟨x, hx', rfl⟩ := hp
        exact ⟨r.1.lower i₁ hx', r.2⟩)
      (r.1.remember trivial r.2)
  | .extRHit _ _ _ hx _, i, ha, hb, h => (hx.nac i.remember.inLog ha (h.remember ha hb)).1
  | .extRNew _ _ _ hx _ h', i, ha, hb, h => by
    have r := hx.nac i.remember.inLog ha (h.remember ha hb)
    have i₁ : Inv₂ _ := ⟨hx.inLog i.remember.inLog⟩
    exact h'.nac i₁.remember.addLower
      (fun p hp => by
        simp only [List.mem_map] at hp
        obtain ⟨x, hx', rfl⟩ := hp
        exact ⟨r.2, r.1.upper i₁ hx'⟩)
      (r.1.remember r.2 trivial)
  | .recordSig (k := k) _ _ _ _ _ h', i, ha, hb, h =>
    h'.nac i.remember ha (SParams.NAC.domain hb k) (h.remember ha hb)
  | .sigL _ _ h', i, ha, hb, h =>
    h'.nac i.remember
      (fun p hp => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
        exact ⟨SParams.NAC.domains ha d hd, hb⟩)
      (h.remember ha hb)

theorem ConstrainEach.nac : ConstrainEach s ps s' → Inv₂ s →
    (∀ p, p ∈ ps → p.1.NAC ∧ p.2.NAC) → LogNAC s → LogNAC s'
  | .nil, _, _, h => h
  | .cons h₁ h₂, i, hps, h =>
    have hh := hps _ (List.mem_cons_self ..)
    h₂.nac (h₁.inv₂ i) (fun p hp => hps p (List.mem_cons_of_mem _ hp)) (h₁.nac i hh.1 hh.2 h)

theorem ConstrainField.nac : ConstrainField s a b s' → Inv₂ s → a.NAC → b.NAC → LogNAC s → LogNAC s'
  | .toAbs, _, _, _, h | .misMis, _, _, _, h | .misOpt, _, _, _, h => h
  | .optOpt _ h', i, ha, hb, h | .preOpt _ h', i, ha, hb, h | .pre _ _ h', i, ha, hb, h =>
    h'.nac i ha hb h

theorem FieldsEach.nac : FieldsEach s ps s' → Inv₂ s →
    (∀ p, p ∈ ps → p.1.NAC ∧ p.2.NAC) → LogNAC s → LogNAC s'
  | .nil, _, _, h => h
  | .cons h₁ h₂, i, hps, h =>
    have hh := hps _ (List.mem_cons_self ..)
    h₂.nac (h₁.inv₂ i) (fun p hp => hps p (List.mem_cons_of_mem _ hp)) (h₁.nac i hh.1 hh.2 h)

/-- Expansion also returns a `NAC` tail. -/
theorem Expand.nac : Expand s t ms t' s' → Inv₂ s → t.NAC → ms.NAC → LogNAC s →
    LogNAC s' ∧ t'.NAC
  | .none, _, ht, _, h => ⟨h, ht⟩
  | .abs _ h', i, _, hms, h => ⟨h'.nac i hms.absPairs h, trivial⟩
  | .nil _ h', i, _, hms, h => ⟨h'.nac i hms.misPairs h, trivial⟩
  | .allAbsent _ _ h', i, ht, hms, h => ⟨h'.nac i hms.absentIn.absPairs h, ht⟩
  | .memo _ _ h₁ _ h₂, i, _, hms, h =>
    ⟨h₂.nac (h₁.inv₂ i) trivial ⟨hms.presentIn, trivial⟩ (h₁.nac i hms.absentIn.absPairs h), trivial⟩
  | .fresh _ _ h₁ _ _ _ h₂, i, _, hms, h =>
    ⟨h₂.nac ((h₁.inv₂ i).of_bounds rfl fun _ hp => hp) trivial ⟨hms.presentIn, trivial⟩
      (h₁.nac i hms.absentIn.absPairs h), trivial⟩
end

theorem ConstrainTop.nac {s s' : State} (h : ConstrainTop s a b s') (i : Inv₂ s)
    (ha : a.NAC) (hb : b.NAC) (hl : LogNAC s) : LogNAC s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  exact hc.nac (i.of_bounds rfl fun _ hp => hp) ha hb hl

/-- The context's types are `NAC` and are types. -/
def CtxNAC (Γ : SCtx) : Prop := ∀ x st, Γ.lookup x = some st → st.NAC ∧ st.IsPre

theorem CtxNAC.cons (h : CtxNAC Γ) (hs : st.NAC) (hn : st.IsPre) : CtxNAC ((x, st) :: Γ) := by
  intro y t hy
  simp only [SCtx.lookup, List.find?_cons] at hy
  split at hy
  · simp at hy; subst hy; exact ⟨hs, hn⟩
  · exact h y t hy

mutual
/-- Inferred types are `NAC` and are types, and accepted constraints stay `NAC`. -/
theorem TypeTerm.nac : TypeTerm Γ s t st s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    LogNAC s' ∧ st.NAC ∧ st.IsPre
  | .lit, _, _, h => ⟨h, trivial, trivial⟩
  | .var hx, hΓ, _, h => ⟨h, (hΓ _ _ hx).1, (hΓ _ _ hx).2⟩
  | .lam _ h', hΓ, i, h =>
    have r := h'.nac (hΓ.cons trivial trivial) i.fresh h
    ⟨r.1, ⟨(fun h => nomatch h), r.2.2.ne_abs, trivial, r.2.1⟩, trivial⟩
  | .app _ h₁ h₂ hc, hΓ, i, h =>
    have r₁ := h₁.nac hΓ i.fresh h
    have i₁ := h₁.inv₂ i.fresh
    have r₂ := h₂.nac hΓ i₁ r₁.1
    ⟨hc.nac (h₂.inv₂ i₁) r₁.2.1 ⟨r₂.2.2.ne_abs, (fun h => nomatch h), r₂.2.1, trivial⟩ r₂.1,
      trivial, trivial⟩
  | .rcd h', hΓ, i, h =>
    have r := h'.nac hΓ i h
    ⟨r.1, ⟨r.2, trivial⟩, trivial⟩
  | .sel _ h' hc, hΓ, i, h =>
    have r := h'.nac hΓ i.fresh h
    ⟨hc.nac (h'.inv₂ i.fresh) r.2.1 ⟨⟨trivial, trivial⟩, trivial⟩ r.1, trivial, trivial⟩
  | .ite _ hc h₁ ha h₂ hb h₃, hΓ, i, h =>
    have rc := hc.nac hΓ i.fresh h
    have i₁ := hc.inv₂ i.fresh
    have n₁ := h₁.nac i₁ rc.2.1 trivial rc.1
    have i₂ := h₁.inv₂ i₁
    have ra := ha.nac hΓ i₂ n₁
    have i₃ := ha.inv₂ i₂
    have n₂ := h₂.nac i₃ ra.2.1 trivial ra.1
    have i₄ := h₂.inv₂ i₃
    have rb := hb.nac hΓ i₄ n₂
    ⟨h₃.nac (hb.inv₂ i₄) rb.2.1 trivial rb.1, trivial, trivial⟩
  | .selOr _ h' hc hd hc', hΓ, i, h =>
    have r := h'.nac hΓ i.fresh h
    have i₁ := h'.inv₂ i.fresh
    have n₂ := hc.nac i₁ r.2.1 ⟨⟨trivial, trivial⟩, trivial⟩ r.1
    have i₂ := hc.inv₂ i₁
    have rd := hd.nac hΓ i₂ n₂
    ⟨hc'.nac (hd.inv₂ i₂) rd.2.1 trivial rd.1, trivial, trivial⟩
  | .extNil h', hΓ, i, h => h'.nac hΓ i h
  | .ext _ h₁ h₂ _ hc, hΓ, i, h =>
    have r₁ := h₁.nac hΓ i h
    have i₁ := h₁.inv₂ i
    have r₂ := h₂.nac hΓ i₁ r₁.1
    ⟨hc.nac (h₂.inv₂ i₁).fresh r₁.2.1 ⟨SFields.NAC.absOf, trivial⟩ r₂.1, ⟨r₂.2, trivial⟩,
      trivial⟩
  | .letIn h₁ h₂, hΓ, i, h =>
    have r₁ := h₁.nac hΓ i h
    h₂.nac (hΓ.cons r₁.2.1 r₁.2.2) (h₁.inv₂ i) r₁.1
  | .letRec _ _ h₁ hc h₂, hΓ, i, h =>
    have hΓ' := hΓ.cons (st := .var _) trivial trivial
    have r₁ := h₁.nac hΓ' i.fresh h
    have i₁ := h₁.inv₂ i.fresh
    h₂.nac hΓ' (hc.inv₂ i₁) (hc.nac i₁ r₁.2.1 trivial r₁.1)
  | .fn _ hp h', hΓ, i, h =>
    have rp := hp.nac hΓ i h
    have r := h'.nac rp.2.2 (hp.inv₂ i) rp.1
    ⟨r.1, ⟨(fun h => nomatch h), r.2.2.ne_abs, rp.2.1, r.2.1⟩, trivial⟩

theorem TypeFields.nac : TypeFields Γ s fs F s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    LogNAC s' ∧ F.NAC
  | .nil, _, _, h => ⟨h, trivial⟩
  | .cons h₁ h₂, hΓ, i, h =>
    have r₁ := h₁.nac hΓ i h
    have r₂ := h₂.nac hΓ (h₁.inv₂ i) r₁.1
    ⟨r₂.1, r₁.2.1, r₂.2⟩

/-- Parameters: the signature is `NAC`, and so is the context of the body. -/
theorem TypeParams.nac : TypeParams Γ s ps P Γ' s' → CtxNAC Γ → Inv₂ s → LogNAC s →
    LogNAC s' ∧ P.NAC ∧ CtxNAC Γ'
  | .nil, hΓ, _, h => ⟨h, trivial, hΓ⟩
  | .req _ h', hΓ, i, h =>
    have r := h'.nac (hΓ.cons trivial trivial) i.fresh h
    ⟨r.1, ⟨trivial, trivial, r.2.1⟩, r.2.2⟩
  | .dflt _ hd hc h', hΓ, i, h =>
    have rd := hd.nac hΓ i.fresh h
    have i₁ := hd.inv₂ i.fresh
    have r := h'.nac (hΓ.cons trivial trivial) (hc.inv₂ i₁) (hc.nac i₁ rd.2.1 trivial rd.1)
    ⟨r.1, ⟨trivial, trivial, r.2.1⟩, r.2.2⟩
end

theorem LogNAC.init {K : Nat → List String} : LogNAC (State.initK K) := fun _ h => nomatch h

theorem builtins_NAC : CtxNAC builtins := by
  intro x st h
  have hm := SCtx.lookup_mem h
  simp only [builtins, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    exact ⟨by simp [SType.NAC, SParams.NAC, builtinSig, SType.IsPre], trivial⟩

end BoltCore.Alg
