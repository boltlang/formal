import BoltCore.Justify

/-!
# Extrusion: every pair it logs is justified

An extrusion logs the pair of each copied type and its original, the bounds
it installs, and what consistency asks for at a copied variable
(`Algorithm.lean`). This file shows each of them justified by one step
(`Extrude.just`), from what the extrusion of the components logged:

* a copy and its original are logged in the order of the polarity
  (`Extrude.logged`), with the same constructor, so fields and rows are
  related label by label (`ExtrudeFields.rel`, `Extrude.rows`) and a record
  is below its copy by `GStep.sameLabels`;
* a copied variable has its copy as a bound (`CopiesOK`), so a bound of
  the original is related to the copy through the copy of the bound
  (`ElemOK`): by `viaL`/`viaR` if it is not a variable, by `viaVar` if it
  is;
* a signature is related to its copy through their argument records
  (`sigPairs_just`).
-/

namespace BoltCore.Alg

open State

/-! ## Growth -/

mutual
theorem Extrude.grows : Extrude s c pol lvl t t' s' c' → Grows s s'
  | .low _ => .refl
  | .arrow _ h₁ h₂ => (h₁.grows.trans h₂.grows).trans .logAll
  | .record _ h₁ h₂ => (h₁.grows.trans h₂.grows).trans .logAll
  | .sig _ h => h.grows.trans .logAll
  | .varCopied _ _ => .logAll
  | .varPos _ _ _ _ h =>
    ((Grows.fresh.trans .addUpper).trans h.grows).trans (Grows.addLowers.trans .logAll)
  | .varNeg _ _ _ _ h =>
    ((Grows.fresh.trans .addLower).trans h.grows).trans (Grows.addUppers.trans .logAll)

theorem ExtrudeFields.grows : ExtrudeFields s c pol lvl fs fs' s' c' → Grows s s'
  | .nil => .refl
  | .opt h₁ h₂ => h₁.grows.trans h₂.grows
  | .cons _ h₁ h₂ => h₁.grows.trans h₂.grows

theorem ExtrudeParams.grows : ExtrudeParams s c pol lvl P P' s' c' → Grows s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.grows.trans h₂.grows

theorem ExtrudeEach.grows : ExtrudeEach s c pol lvl ts ts' s' c' → Grows s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.grows.trans h₂.grows
end

/-! ## Polarity -/

/-- A relation in the order of a polarity: the copy is on the right if
positive, on the left if negative. -/
def PolR {α : Type} (R : α → α → Prop) (pol : Bool) (x y : α) : Prop :=
  match pol with
  | true => R x y
  | false => R y x

theorem PolR.mono {α : Type} {R R' : α → α → Prop} {x y : α} (h : ∀ x y, R x y → R' x y) :
    ∀ {pol : Bool}, PolR R pol x y → PolR R' pol x y
  | true, hr => h _ _ hr
  | false, hr => h _ _ hr

theorem PolR.logged_refl {s : State} {t : SType} : ∀ {pol : Bool}, PolR (Logged s) pol t t
  | true => .inl rfl
  | false => .inl rfl

theorem PolR.logged_mono {t t' : SType} (g : Grows s s') {pol : Bool}
    (h : PolR (Logged s) pol t t') : PolR (Logged s') pol t t' :=
  h.mono fun _ _ => Logged.mono g

/-- A pair in the list just logged is accepted. -/
theorem logged_polPair {s : State} {ps : List (SType × SType)} {t t' : SType} :
    ∀ {pol : Bool}, polPair pol t t' ∈ ps → PolR (Logged (s.logAll ps)) pol t t'
  | true, h => .inr (List.mem_append_left _ h)
  | false, h => .inr (List.mem_append_left _ h)

/-- A copy and its original are accepted, in the order of the polarity. -/
theorem Extrude.logged : Extrude s c pol lvl t t' s' c' → PolR (Logged s') pol t t'
  | .low _ => .logged_refl
  | .arrow .. | .record .. | .sig .. | .varCopied .. => logged_polPair (List.mem_cons_self ..)
  | .varPos .. => .inr (List.mem_append_left _ (List.mem_cons_self ..))
  | .varNeg .. => .inr (List.mem_append_left _ (List.mem_cons_self ..))

/-! ## Copies are bounds -/

/-- `w` is a bound of `v`: an upper bound if positive, a lower bound if
negative. -/
def BoundPol (s : State) (pol : Bool) (v w : Nat) : Prop :=
  match pol with
  | true => SType.var w ∈ (s.bounds v).upper
  | false => SType.var w ∈ (s.bounds v).lower

theorem BoundPol.mono (g : Grows s s') : ∀ {pol : Bool}, BoundPol s pol v w → BoundPol s' pol v w
  | true, h => g.upper _ _ h
  | false, h => g.lower _ _ h

/-- Each copy is a bound of its original. -/
def CopiesOK (s : State) (c : Copies) : Prop := ∀ v pol w, ((v, pol), w) ∈ c → BoundPol s pol v w

theorem CopiesOK.nil : CopiesOK s [] := fun _ _ _ h => nomatch h

theorem CopiesOK.mono (g : Grows s s') (h : CopiesOK s c) : CopiesOK s' c :=
  fun v pol w hm => (h v pol w hm).mono g

theorem CopiesOK.cons (h : CopiesOK s c) (hb : BoundPol s pol v w) :
    CopiesOK s (((v, pol), w) :: c) := by
  intro v' pol' w' hm
  rcases List.mem_cons.mp hm with e | hm
  · cases e; exact hb
  · exact h v' pol' w' hm

mutual
theorem Extrude.copiesOK : Extrude s c pol lvl t t' s' c' → CopiesOK s c → CopiesOK s' c'
  | .low _, h => h
  | .arrow _ h₁ h₂, h => (h₂.copiesOK (h₁.copiesOK h)).mono .logAll
  | .record _ h₁ h₂, h => (h₂.copiesOK (h₁.copiesOK h)).mono .logAll
  | .sig _ h', h => (h'.copiesOK h).mono .logAll
  | .varCopied _ _, h => h.mono .logAll
  | .varPos _ _ _ _ h', h =>
    (h'.copiesOK ((h.mono (Grows.fresh.trans .addUpper)).cons
      (pol := true) mem_upper_addUpper)).mono (Grows.addLowers.trans .logAll)
  | .varNeg _ _ _ _ h', h =>
    (h'.copiesOK ((h.mono (Grows.fresh.trans .addLower)).cons
      (pol := false) mem_lower_addLower)).mono (Grows.addUppers.trans .logAll)

theorem ExtrudeFields.copiesOK : ExtrudeFields s c pol lvl fs fs' s' c' → CopiesOK s c →
    CopiesOK s' c'
  | .nil, h => h
  | .opt h₁ h₂, h => h₂.copiesOK (h₁.copiesOK h)
  | .cons _ h₁ h₂, h => h₂.copiesOK (h₁.copiesOK h)

theorem ExtrudeParams.copiesOK : ExtrudeParams s c pol lvl P P' s' c' → CopiesOK s c →
    CopiesOK s' c'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.copiesOK (h₁.copiesOK h)

theorem ExtrudeEach.copiesOK : ExtrudeEach s c pol lvl ts ts' s' c' → CopiesOK s c →
    CopiesOK s' c'
  | .nil, h => h
  | .cons h₁ h₂, h => h₂.copiesOK (h₁.copiesOK h)
end

/-- The copy of a variable is one of its bounds. -/
theorem Extrude.varBound (h : Extrude s c pol lvl (.var u) (.var u') s' c') (hc : CopiesOK s c) :
    u' = u ∨ BoundPol s' pol u u' := by
  cases h with
  | low _ => exact .inl rfl
  | varCopied _ hw => exact .inr ((hc _ _ _ (lookup_mem hw)).mono .logAll)
  | varPos _ _ _ _ h' =>
    exact .inr (BoundPol.mono (h'.grows.trans (Grows.addLowers.trans .logAll)) (pol := true)
      mem_upper_addUpper)
  | varNeg _ _ _ _ h' =>
    exact .inr (BoundPol.mono (h'.grows.trans (Grows.addUppers.trans .logAll)) (pol := false)
      mem_lower_addLower)

/-! ## A bound and its copy -/

/-- How an extruded type relates to its original, as a bound: it is the
original; or neither is a variable nor `Abs`, and they are accepted in the
order of the polarity; or both are variables, and the copy is a bound of
the original. -/
def ElemOK (s : State) (pol : Bool) (t t' : SType) : Prop :=
  t' = t ∨
  ((∀ w, t ≠ .var w) ∧ (∀ w, t' ≠ .var w) ∧ t ≠ .abs ∧ t' ≠ .abs ∧ PolR (Logged s) pol t t') ∨
  ∃ u u', t = .var u ∧ t' = .var u' ∧ BoundPol s pol u u'

theorem ElemOK.mono (g : Grows s s') : ElemOK s pol t t' → ElemOK s' pol t t'
  | .inl e => .inl e
  | .inr (.inl ⟨h₁, h₂, h₃, h₄, h₅⟩) => .inr (.inl ⟨h₁, h₂, h₃, h₄, h₅.logged_mono g⟩)
  | .inr (.inr ⟨u, u', e, e', hb⟩) => .inr (.inr ⟨u, u', e, e', hb.mono g⟩)

theorem Extrude.elemOK (h : Extrude s c pol lvl t t' s' c') (hc : CopiesOK s c) :
    ElemOK s' pol t t' := by
  rcases h.con with e | hcon
  · exact .inl e
  · match t, t', hcon, h with
    | .var u, .var u', _, h =>
      rcases h.varBound hc with e | hb
      · exact .inl (by rw [e])
      · exact .inr (.inr ⟨u, u', rfl, rfl, hb⟩)
    | .arrow _ _, .arrow _ _, _, h =>
      exact .inr (.inl ⟨(fun _ e => nomatch e), (fun _ e => nomatch e), (fun e => nomatch e),
        (fun e => nomatch e), h.logged⟩)
    | .record _ _, .record _ _, _, h =>
      exact .inr (.inl ⟨(fun _ e => nomatch e), (fun _ e => nomatch e), (fun e => nomatch e),
        (fun e => nomatch e), h.logged⟩)
    | .sig _, .sig _, _, h =>
      exact .inr (.inl ⟨(fun _ e => nomatch e), (fun _ e => nomatch e), (fun e => nomatch e),
        (fun e => nomatch e), h.logged⟩)

/-- Each bound has its copy in the result. -/
theorem ExtrudeEach.elems : ExtrudeEach s c pol lvl ts ts' s' c' → CopiesOK s c →
    ∀ t ∈ ts, ∃ t' ∈ ts', ElemOK s' pol t t'
  | .nil, _, _, h => nomatch h
  | .cons h₁ h₂, hc, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨_, List.mem_cons_self .., (h₁.elemOK hc).mono h₂.grows⟩
    · obtain ⟨t', ht', hok⟩ := h₂.elems (h₁.copiesOK hc) t ht
      exact ⟨t', List.mem_cons_of_mem _ ht', hok⟩

/-! ## Fields and rows -/

theorem PolR.rel_nil {Q : SType → SType → Prop} :
    ∀ {pol : Bool}, PolR (SFields.Rel Q) pol .nil .nil
  | true => .nil
  | false => .nil

theorem PolR.rel_cons {Q : SType → SType → Prop} {n : String} {f f' : SType} {fs fs' : SFields} :
    ∀ {pol : Bool}, PolR Q pol f f' → PolR (SFields.Rel Q) pol fs fs' →
      PolR (SFields.Rel Q) pol (.cons n f fs) (.cons n f' fs')
  | true, h₁, h₂ => .cons h₁ h₂
  | false, h₁, h₂ => .cons h₁ h₂

theorem SFields.Rel.append {Q : SType → SType → Prop} :
    ∀ {fs fs' gs gs' : SFields}, SFields.Rel Q fs fs' → SFields.Rel Q gs gs' →
      SFields.Rel Q (fs.append gs) (fs'.append gs')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hq r, h => .cons hq (r.append h)

theorem PolR.rel_append {Q : SType → SType → Prop} {fs fs' gs gs' : SFields} :
    ∀ {pol : Bool}, PolR (SFields.Rel Q) pol fs fs' → PolR (SFields.Rel Q) pol gs gs' →
      PolR (SFields.Rel Q) pol (fs.append gs) (fs'.append gs')
  | true, h₁, h₂ => SFields.Rel.append h₁ h₂
  | false, h₁, h₂ => SFields.Rel.append h₁ h₂

theorem PolR.rel_refl {s : State} {fs : SFields} :
    ∀ {pol : Bool}, PolR (SFields.Rel (FieldR (Logged s))) pol fs fs
  | true => SFields.Rel.refl_logged fs
  | false => SFields.Rel.refl_logged fs

theorem PolR.rel_mono {fs fs' : SFields} (g : Grows s s') {pol : Bool}
    (h : PolR (SFields.Rel (FieldR (Logged s))) pol fs fs') :
    PolR (SFields.Rel (FieldR (Logged s'))) pol fs fs' :=
  h.mono fun _ _ r => r.mono fun _ _ f => f.mono fun _ _ => Logged.mono g

/-- A field that is a type and its copy, as fields. -/
theorem Extrude.fieldR (h : Extrude s c pol lvl f f' s₁ c₁) (g : Grows s₁ s') :
    PolR (FieldR (Logged s')) pol f f' := by
  have hl := h.logged.logged_mono g
  rcases h.con with rfl | hc
  · cases pol <;> exact .refl
  · have hp := hc.isPre
    cases pol
    · exact .pre hp.2 hp.1 hl
    · exact .pre hp.1 hp.2 hl

/-- An optional field and its copy. -/
theorem Extrude.fieldROpt (h : Extrude s c pol lvl t t' s₁ c₁) (g : Grows s₁ s') :
    PolR (FieldR (Logged s')) pol (.opt t) (.opt t') := by
  have hl := h.logged.logged_mono g
  rcases h.con with rfl | hc
  · cases pol <;> exact .refl
  · have hp := hc.isPre
    cases pol
    · exact .optOpt hp.2.ne_abs hl
    · exact .optOpt hp.1.ne_abs hl

/-- The fields of a record and their copies, label by label. -/
theorem ExtrudeFields.rel : ExtrudeFields s c pol lvl fs fs' s' c' →
    PolR (SFields.Rel (FieldR (Logged s'))) pol fs fs'
  | .nil => .rel_nil
  | .opt h₁ h₂ => .rel_cons (h₁.fieldROpt h₂.grows) h₂.rel
  | .cons _ h₁ h₂ => .rel_cons (h₁.fieldR h₂.grows) h₂.rel

/-- A row and its copy, flattened: the fields label by label, and the
tails. -/
theorem Extrude.rows : Extrude s c pol lvl t t' s' c' →
    PolR (SFields.Rel (FieldR (Logged s'))) pol (rowView t).1 (rowView t').1 ∧
      PolR (Logged s') pol (rowView t).2 (rowView t').2
  | .low _ => ⟨.rel_refl, .logged_refl⟩
  | h@(.arrow ..) => ⟨.rel_nil, h.logged⟩
  | h@(.sig ..) => ⟨.rel_nil, h.logged⟩
  | h@(.varCopied ..) => ⟨.rel_nil, h.logged⟩
  | h@(.varPos ..) => ⟨.rel_nil, h.logged⟩
  | h@(.varNeg ..) => ⟨.rel_nil, h.logged⟩
  | .record _ hf ht =>
    have r := ht.rows
    ⟨.rel_append (hf.rel.rel_mono (ht.grows.trans .logAll)) (r.1.rel_mono .logAll),
      r.2.logged_mono .logAll⟩

/-! ## Records with the same labels -/

theorem SFields.Rel.labels {Q : SType → SType → Prop} :
    ∀ {fs gs : SFields}, SFields.Rel Q fs gs → fs.labels = gs.labels
  | _, _, .nil => rfl
  | _, _, .cons _ r => by simp [SFields.labels, r.labels]

theorem SFields.lookup_of_mem_labels {l : String} :
    ∀ {fs : SFields}, l ∈ fs.labels → ∃ f, fs.lookup l = some f
  | .nil, h => nomatch h
  | .cons n f fs, h => by
    simp only [SFields.lookup]
    by_cases hn : n = l
    · exact ⟨f, by simp [hn]⟩
    · simp only [hn, ite_false]
      rcases List.mem_cons.mp h with e | h
      · exact absurd e.symm hn
      · exact SFields.lookup_of_mem_labels h

/-- No field is missing from a list that has every label. -/
theorem SFields.missing_eq_nil {fs₀ : SFields} :
    ∀ {fs₁ : SFields}, (∀ l ∈ fs₁.labels, ∃ f, fs₀.lookup l = some f) → fs₀.missing fs₁ = .nil
  | .nil, _ => rfl
  | .cons n f fs, h => by
    obtain ⟨g, hg⟩ := h n (List.mem_cons_self ..)
    simp only [SFields.missing, hg]
    exact SFields.missing_eq_nil fun l hl => h l (List.mem_cons_of_mem _ hl)

/-- A record is below a record with the same labels whose fields are
above its own, label by label, and whose tail is above its tail. -/
theorem GStep.sameLabels {σ : Nat → Bounds} {R : SType → SType → Prop} {fa fb F₀ F₁ : SFields}
    {ta tb U₀ U₁ : SType}
    (e₀ : rowView (.record fa ta) = (F₀, U₀)) (e₁ : rowView (.record fb tb) = (F₁, U₁))
    (hrel : SFields.Rel (FieldR R) F₀ F₁) (ht : R U₀ U₁) :
    GStep σ R (.record fa ta) (.record fb tb) := by
  have hl := hrel.labels
  have m₀ : F₀.missing F₁ = .nil :=
    SFields.missing_eq_nil fun l h => SFields.lookup_of_mem_labels (hl ▸ h)
  have m₁ : F₁.missing F₀ = .nil :=
    SFields.missing_eq_nil fun l h => SFields.lookup_of_mem_labels (hl ▸ h)
  refine .record (t₀' := U₀) e₀ e₁ (fun l f₀ f₁ h₀ h₁ => ?_) ?_ ?_
  · obtain ⟨f, hf, hq⟩ := hrel.lookup h₁
    rw [h₀] at hf; cases hf; exact hq
  · rw [m₀]; exact .none
  · rw [m₁]; exact ht

theorem rowView_record_nil (fs : SFields) : rowView (.record fs .nil) = (fs, .nil) := by
  simp [rowView, SFields.append_nil]

/-- The same for closed records. -/
theorem GStep.closed {σ : Nat → Bounds} {R : SType → SType → Prop} {fa fb : SFields}
    (hrel : SFields.Rel (FieldR R) fa fb) (hnil : R .nil .nil) :
    GStep σ R (.record fa .nil) (.record fb .nil) :=
  .sameLabels (rowView_record_nil fa) (rowView_record_nil fb) hrel hnil

/-! ## Signatures -/

/-- A type and its copy, as types: the same, or two types (not `Abs`,
`Missing` or an optional field) that are accepted. -/
def TyR (R : SType → SType → Prop) (τ τ' : SType) : Prop := τ' = τ ∨ (τ.IsPre ∧ τ'.IsPre ∧ R τ τ')

theorem TyR.mono {R R' : SType → SType → Prop} (h : ∀ x y, R x y → R' x y) {τ τ' : SType} :
    TyR R τ τ' → TyR R' τ τ'
  | .inl e => .inl e
  | .inr ⟨h₁, h₂, hr⟩ => .inr ⟨h₁, h₂, h _ _ hr⟩

theorem TyR.fieldR {R : SType → SType → Prop} {τ τ' : SType} : TyR R τ τ' → FieldR R τ τ'
  | .inl e => e ▸ .refl
  | .inr ⟨h₁, h₂, hr⟩ => .pre h₁ h₂ hr

theorem Extrude.tyR (h : Extrude s c pol lvl τ τ' s₁ c₁) (g : Grows s₁ s') :
    PolR (TyR (Logged s')) pol τ τ' := by
  have hl := h.logged.logged_mono g
  rcases h.con with rfl | hc
  · cases pol <;> exact .inl rfl
  · have hp := hc.isPre
    cases pol
    · exact .inr ⟨hp.2, hp.1, hl⟩
    · exact .inr ⟨hp.1, hp.2, hl⟩

/-- Two parameter lists with the same names, kinds and defaults, and
related types. -/
inductive ParamsR (Q : SType → SType → Prop) : List (Param SType) → List (Param SType) → Prop where
  | nil : ParamsR Q [] []
  | cons : Q τ τ' → ParamsR Q ps qs → ParamsR Q (⟨n, k, o, τ⟩ :: ps) (⟨n, k, o, τ'⟩ :: qs)

/-- Two lists of the same length, related element by element. -/
inductive ListR (Q : SType → SType → Prop) : List SType → List SType → Prop where
  | nil : ListR Q [] []
  | cons : Q a b → ListR Q as bs → ListR Q (a :: as) (b :: bs)

theorem ParamsR.mono {Q Q' : SType → SType → Prop} (h : ∀ x y, Q x y → Q' x y) :
    ParamsR Q ps qs → ParamsR Q' ps qs
  | .nil => .nil
  | .cons hq r => .cons (h _ _ hq) (r.mono h)

theorem ExtrudeParams.rel : ExtrudeParams s c pol lvl P P' s' c' →
    PolR (ParamsR (TyR (Logged s'))) pol P.toList P'.toList
  | .nil => by cases pol <;> exact .nil
  | .cons h₁ h₂ => by
    have t := h₁.tyR h₂.grows
    have r := h₂.rel
    cases pol
    · exact .cons t r
    · exact .cons t r

theorem ParamsR.erase {Q : SType → SType → Prop} : ParamsR Q ps qs →
    ps.map (Param.map fun _ => ()) = qs.map (Param.map fun _ => ())
  | .nil => rfl
  | .cons _ r => by simp [Param.map, r.erase]

/-- The same numbers of positional arguments. -/
theorem ParamsR.counts {Q : SType → SType → Prop} (h : ParamsR Q ps qs) :
    Param.counts ps = Param.counts qs := by
  rw [← Param.counts_map (fun _ => ()) ps, ← Param.counts_map (fun _ => ()) qs, h.erase]

theorem ParamsR.pos {Q : SType → SType → Prop} : ParamsR Q ps qs →
    ∀ k, ListR Q (Param.pos k ps) (Param.pos k qs)
  | .nil, 0 | .nil, _ + 1 => .nil
  | .cons _ _, 0 => .nil
  | .cons (k := kd) hq r, k + 1 => by
    by_cases hk : kd = PKind.kwOnly
    · simp only [Param.pos, hk, ite_true]; exact .nil
    · simp only [Param.pos, hk, ite_false]; exact .cons hq (r.pos k)

theorem ParamsR.named {Q : SType → SType → Prop} : ParamsR Q ps qs →
    ∀ k, ParamsR Q (Param.named k ps) (Param.named k qs)
  | .nil, _ => by simp only [Param.named]; exact .nil
  | .cons (k := kd) hq r, k => by
    by_cases hk : kd = PKind.kwOnly
    · simp only [Param.named, hk, ite_true]; exact .cons hq r
    · cases k with
      | succ k => simp only [Param.named, hk, ite_false]; exact r.named k
      | zero =>
        by_cases he : kd = PKind.either
        · subst he
          simp only [Param.named, ite_true, reduceCtorEq, ite_false]; exact .cons hq (r.named 0)
        · simp only [Param.named, hk, he, ite_false]; exact r.named 0

/-- The fields of the parameters passed by name. -/
theorem ParamsR.ofParams {R : SType → SType → Prop} : ParamsR (TyR R) ps qs →
    SFields.Rel (FieldR R) (SFields.ofParams ps) (SFields.ofParams qs)
  | .nil => .nil
  | .cons (o := o) hq r => by
    refine .cons ?_ r.ofParams
    cases o with
    | false => exact hq.fieldR
    | true =>
      rcases hq with e | ⟨h₁, _, hr⟩
      · rw [e]; exact .refl
      · exact .optOpt h₁.ne_abs hr

/-- The list of positional arguments, as a field. -/
theorem ListR.fieldR {R : SType → SType → Prop} {as bs : List SType} (h : ListR (TyR R) as bs)
    (hR : ∀ p ∈ listPairs as bs, R p.1 p.2) : FieldR R (SType.list as) (SType.list bs) := by
  cases h with
  | nil => exact .refl
  | cons _ _ =>
    exact .pre (SType.list_isPre _) (SType.list_isPre _) (hR _ (List.mem_cons_self ..))

/-- The lists of two argument lists are justified, suffix by suffix. -/
theorem listPairs_just {σ : Nat → Bounds} {R : SType → SType → Prop} (hnil : R .nil .nil) :
    ∀ {as bs : List SType}, ListR (TyR R) as bs → (∀ p ∈ listPairs as bs, R p.1 p.2) →
      ∀ p ∈ listPairs as bs, GStep σ R p.1 p.2
  | _, _, .nil, _, _, hp => nomatch hp
  | _, _, .cons hq r, hR, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact GStep.closed
        (.cons hq.fieldR (.cons (r.fieldR fun q hq' => hR q (List.mem_cons_of_mem _ hq')) .nil))
        hnil
    · exact listPairs_just hnil r (fun q hq' => hR q (List.mem_cons_of_mem _ hq')) p hp

/-- What relates a signature to a signature above it is justified. -/
theorem sigPairs_just {σ : Nat → Bounds} {R : SType → SType → Prop} {lo hi : SParams}
    (hrel : ParamsR (TyR R) lo.toList hi.toList) (hnil : R .nil .nil)
    (hR : ∀ p ∈ sigPairs lo hi, R p.1 p.2) : ∀ p ∈ sigPairs lo hi, GStep σ R p.1 p.2 := by
  intro p hp
  obtain ⟨k, hk, hp'⟩ := List.mem_flatMap.mp hp
  have hin : ∀ q, q ∈ ((lo.domain k, SType.sig hi) :: (lo.domain k, hi.domain k) ::
      listPairs (Param.pos k lo.toList) (Param.pos k hi.toList)) → R q.1 q.2 :=
    fun q hq => hR q (List.mem_flatMap.mpr ⟨k, hk, hq⟩)
  have hl : ∀ q ∈ listPairs (Param.pos k lo.toList) (Param.pos k hi.toList), R q.1 q.2 :=
    fun q hq => hin q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  rcases List.mem_cons.mp hp' with rfl | hp'
  · exact .recordSig (d := hi.domain k) (List.mem_map.mpr ⟨k, hrel.counts ▸ hk, rfl⟩)
      (hin _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rcases List.mem_cons.mp hp' with rfl | hp'
  · exact GStep.closed (.cons ((hrel.pos k).fieldR hl) (hrel.named k).ofParams) hnil
  · exact listPairs_just hnil (hrel.pos k) hl p hp'

/-- A signature is below a signature above it. -/
theorem sig_just {σ : Nat → Bounds} {R : SType → SType → Prop} {lo hi : SParams}
    (hR : ∀ p ∈ sigPairs lo hi, R p.1 p.2) : GStep σ R (.sig lo) (.sig hi) :=
  .sigL trivial fun d hd => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
    exact hR _ (List.mem_flatMap.mpr ⟨k, hk, List.mem_cons_self ..⟩)

/-- The same, when the pairs are among those just logged. -/
theorem sig_just_logAll {σ : Nat → Bounds} {s₁ : State} {lo hi : SParams}
    {ps : List (SType × SType)} (hps : ∀ q ∈ sigPairs lo hi, q ∈ ps) :
    GStep σ (Logged (s₁.logAll ps)) (.sig lo) (.sig hi) :=
  sig_just fun q hq => .inr (List.mem_append_left _ (hps q hq))

theorem sigPairs_just_logAll {σ : Nat → Bounds} {s₁ : State} {lo hi : SParams}
    {ps : List (SType × SType)} (hrel : ParamsR (TyR (Logged s₁)) lo.toList hi.toList)
    (hps : ∀ q ∈ sigPairs lo hi, q ∈ ps) :
    ∀ p ∈ sigPairs lo hi, GStep σ (Logged (s₁.logAll ps)) p.1 p.2 :=
  sigPairs_just (hrel.mono fun _ _ => TyR.mono fun _ _ => Logged.mono .logAll) (.inl rfl)
    fun q hq => .inr (List.mem_append_left _ (hps q hq))

/-! ## Justification -/

/-- Logging justified constraints keeps the log justified. -/
theorem JustExcept.logAll {ps : List (SType × SType)} (h : JustExcept s P)
    (hps : ∀ p ∈ ps, GStep s.bounds (Logged (s.logAll ps)) p.1 p.2) :
    JustExcept (s.logAll ps) P := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact .inr (hps p hp)
  · exact (h p hp).imp id (GStep.mono .logAll)

theorem mem_lower_addLowers {s : State} {v : Nat} {ts : List SType} {t : SType} (h : t ∈ ts) :
    t ∈ ((s.addLowers v ts).bounds v).lower := by simp [State.addLowers, h]

theorem mem_upper_addUppers {s : State} {v : Nat} {ts : List SType} {t : SType} (h : t ∈ ts) :
    t ∈ ((s.addUppers v ts).bounds v).upper := by simp [State.addUppers, h]

mutual
/-- Every pair an extrusion logs is justified. -/
theorem Extrude.just : Extrude s c pol lvl t t' s' c' → CopiesOK s c → JustExcept s P →
    JustExcept s' P
  | .low _, _, hj => hj
  | .arrow _ h₁ h₂, hc, hj => by
    refine (h₂.just (h₁.copiesOK hc) (h₁.just hc hj)).logAll fun p hp => ?_
    have e := List.mem_singleton.mp hp
    subst e
    cases pol
    · exact .arrow (h₁.logged.logged_mono (h₂.grows.trans .logAll)) (h₂.logged.logged_mono .logAll)
    · exact .arrow (h₁.logged.logged_mono (h₂.grows.trans .logAll)) (h₂.logged.logged_mono .logAll)
  | .record hlv h₁ h₂, hc, hj => by
    refine (h₂.just (h₁.copiesOK hc) (h₁.just hc hj)).logAll fun p hp => ?_
    have e := List.mem_singleton.mp hp
    subst e
    have r := (Extrude.record hlv h₁ h₂).rows
    cases pol
    · exact GStep.sameLabels (hrel := r.1) (ht := r.2) rfl rfl
    · exact GStep.sameLabels (hrel := r.1) (ht := r.2) rfl rfl
  | .sig _ h', hc, hj => by
    refine (h'.just hc hj).logAll fun p hp => ?_
    have hrel := h'.rel
    cases pol
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact sig_just_logAll fun q hq => List.mem_cons_of_mem _ hq
      · exact sigPairs_just_logAll hrel (fun q hq => List.mem_cons_of_mem _ hq) p hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact sig_just_logAll fun q hq => List.mem_cons_of_mem _ hq
      · exact sigPairs_just_logAll hrel (fun q hq => List.mem_cons_of_mem _ hq) p hp
  | .varCopied _ hw, hc, hj => by
    refine hj.logAll fun p hp => ?_
    have e := List.mem_singleton.mp hp
    subst e
    have hb := hc _ _ _ (lookup_mem hw)
    cases pol
    · exact .varR hb
    · exact .varL hb
  | .varPos (s := s) (v := v) (c := c) _ _ _ _ h', hc, hj => by
    have hc₀ : CopiesOK (s.fresh.addUpper v (.var s.next)) (((v, true), s.next) :: c) :=
      (hc.mono (Grows.fresh.trans .addUpper)).cons (pol := true) mem_upper_addUpper
    have j₁ := h'.just hc₀ (hj.grow (Grows.fresh.trans .addUpper) fun _ hp => hp)
    refine (j₁.grow .addLowers fun _ hp => hp).logAll fun p hp => ?_
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .varL (Grows.addLowers.upper _ _ (h'.grows.upper _ _ mem_upper_addUpper))
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hp
      exact .varR (mem_lower_addLowers hl')
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
      obtain ⟨l', hl', hok⟩ := h'.elems hc₀ l hl
      rcases hok with e | ⟨h₁, h₂, h₃, h₄, h₅⟩ | ⟨u, u', rfl, rfl, hb⟩
      · subst e; exact .varR (mem_lower_addLowers hl')
      · exact .viaR (mem_lower_addLowers hl') h₂ h₄ h₁ h₃
          (Logged.mono (Grows.addLowers.trans .logAll) h₅)
      · exact .viaVar (Grows.addLowers.upper _ _ hb) (mem_lower_addLowers hl')
  | .varNeg (s := s) (v := v) (c := c) _ _ _ _ h', hc, hj => by
    have hc₀ : CopiesOK (s.fresh.addLower v (.var s.next)) (((v, false), s.next) :: c) :=
      (hc.mono (Grows.fresh.trans .addLower)).cons (pol := false) mem_lower_addLower
    have j₁ := h'.just hc₀ (hj.grow (Grows.fresh.trans .addLower) fun _ hp => hp)
    refine (j₁.grow .addUppers fun _ hp => hp).logAll fun p hp => ?_
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .varR (Grows.addUppers.lower _ _ (h'.grows.lower _ _ mem_lower_addLower))
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hp
      exact .varL (mem_upper_addUppers hu')
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
      obtain ⟨u', hu', hok⟩ := h'.elems hc₀ u hu
      rcases hok with e | ⟨h₁, h₂, _, h₄, h₅⟩ | ⟨w, w', rfl, rfl, hb⟩
      · subst e; exact .varL (mem_upper_addUppers hu')
      · exact .viaL (mem_upper_addUppers hu') h₂ h₄ h₁
          (Logged.mono (Grows.addUppers.trans .logAll) h₅)
      · exact .viaVar (mem_upper_addUppers hu') (Grows.addUppers.lower _ _ hb)

theorem ExtrudeFields.just : ExtrudeFields s c pol lvl fs fs' s' c' → CopiesOK s c →
    JustExcept s P → JustExcept s' P
  | .nil, _, hj => hj
  | .opt h₁ h₂, hc, hj => h₂.just (h₁.copiesOK hc) (h₁.just hc hj)
  | .cons _ h₁ h₂, hc, hj => h₂.just (h₁.copiesOK hc) (h₁.just hc hj)

theorem ExtrudeParams.just : ExtrudeParams s c pol lvl P' P'' s' c' → CopiesOK s c →
    JustExcept s P → JustExcept s' P
  | .nil, _, hj => hj
  | .cons h₁ h₂, hc, hj => h₂.just (h₁.copiesOK hc) (h₁.just hc hj)

theorem ExtrudeEach.just : ExtrudeEach s c pol lvl ts ts' s' c' → CopiesOK s c →
    JustExcept s P → JustExcept s' P
  | .nil, _, hj => hj
  | .cons h₁ h₂, hc, hj => h₂.just (h₁.copiesOK hc) (h₁.just hc hj)
end

end BoltCore.Alg
