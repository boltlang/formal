import BoltCore.Theorem1

/-!
# Kinds for row variables, and Theorem 1 without assumptions

The kind of a row variable is the set of labels it does *not* represent:
the record it is the tail of lists them. A row `{fs | ρ}` lacks the labels
in `kind ρ` that `fs` does not list (`RowKind`); every type that is not a
row tail lacks nothing (`KEmpty`). The algorithm keeps this discipline
(issue #1):

* every accepted constraint is between *well-kinded* types (`WK`: records
  with a row-variable tail list some labels, all in the tail's kind;
  fields and function components lack nothing), and relates rows that lack
  the same labels (`KOK`). This is what `check_kind` in `lib/typer.ml`
  checks at run time.

It follows that the chains of row-variable tails through upper bounds are
acyclic: an upper bound `{fs | ρ}` of `v` lacks what `v` lacks, so
`kind ρ = kind v ⊎ fs` with `fs` non-empty, and `kind ρ` is strictly
larger. The number of logged labels *not* in a variable's kind is therefore
a rank for `TailRanked` (`kinds_tailRanked`), which discharges the last
assumption of Theorem 1 (`theorem1`).

The kind map is fixed for a run (see `State.kind`), so kinds of existing
variables never change, and no scoping invariant is needed.
-/

namespace BoltCore.Alg

open State

/-! ## Definitions -/

section Defs
variable (K : Nat → List String)

/-- The row with fields `fs` over the row variable `ρ` lacks `l`. -/
def RowKind (fs : SFields) (ρ : Nat) (l : String) : Prop := l ∈ K ρ ∧ l ∉ fs.labels

/-- `a` and `b` lack the same labels, if both are rows over row variables. -/
def KOK (a b : SType) : Prop :=
  ∀ ρ σ, (rowView a).2 = .var ρ → (rowView b).2 = .var σ →
    ∀ l, RowKind K (rowView a).1 ρ l ↔ RowKind K (rowView b).1 σ l

/-- `t` lacks no label (it is a whole type, not a row tail). -/
def KEmpty (t : SType) : Prop :=
  ∀ ρ, (rowView t).2 = .var ρ → ∀ l, ¬ RowKind K (rowView t).1 ρ l

/-- A record over a row variable lists some labels, all lacked by it. -/
def RecOK (t : SType) : Prop :=
  ∀ ρ, (rowView t).2 = .var ρ → (rowView t).1 ≠ .nil ∧ ∀ l ∈ (rowView t).1.labels, l ∈ K ρ

end Defs

mutual
/-- Well-kinded types. -/
def WK (K : Nat → List String) : SType → Prop
  | .arrow a b => WK K a ∧ KEmpty K a ∧ WK K b ∧ KEmpty K b
  | .record fs t => FWK K fs ∧ WK K t ∧ RecOK K (.record fs t)
  | .opt t => WK K t ∧ KEmpty K t
  | .sig P => PWK K P
  | _ => True

def FWK (K : Nat → List String) : SFields → Prop
  | .nil => True
  | .cons _ f fs => WK K f ∧ KEmpty K f ∧ FWK K fs

/-- The types of a signature's parameters are well-kinded whole types. -/
def PWK (K : Nat → List String) : SParams → Prop
  | .nil => True
  | .cons _ _ _ τ P => WK K τ ∧ KEmpty K τ ∧ PWK K P
end

variable {K : Nat → List String}

/-! ## Labels -/

theorem SFields.labels_append : ∀ fs gs : SFields, (fs.append gs).labels = fs.labels ++ gs.labels
  | .nil, _ => rfl
  | .cons _ _ fs, gs => by simp [SFields.append, SFields.labels, SFields.labels_append fs gs]

theorem SFields.append_nil : ∀ fs : SFields, fs.append .nil = fs
  | .nil => rfl
  | .cons _ _ fs => by simp [SFields.append, SFields.append_nil fs]

theorem SFields.mem_labels {l : String} : ∀ fs : SFields, l ∈ fs.labels ↔ (fs.lookup l).isSome
  | .nil => by simp [SFields.labels, SFields.lookup]
  | .cons n f fs => by
    have ih := SFields.mem_labels (l := l) fs
    by_cases h : n = l
    · subst h; simp [SFields.labels, SFields.lookup]
    · have h' : l ≠ n := fun e => h e.symm
      simp [SFields.labels, SFields.lookup, h, h', ih]

theorem SFields.mem_missing {l : String} (fs₀ fs₁ : SFields) :
    l ∈ (fs₀.missing fs₁).labels ↔ l ∈ fs₁.labels ∧ l ∉ fs₀.labels := by
  simp only [SFields.mem_labels, SFields.missing_lookup]
  cases fs₀.lookup l <;> simp

theorem SFields.mem_presentIn {l : String} (Ks : List String) (ms : SFields) :
    l ∈ (ms.presentIn Ks).labels ↔ l ∈ ms.labels ∧ l ∉ Ks := by
  simp only [SFields.mem_labels, SFields.presentIn_lookup]
  by_cases h : l ∈ Ks <;> simp [h]

theorem SFields.labels_absOf : ∀ F : SFields, F.absOf.labels = F.labels
  | .nil => rfl
  | .cons _ _ F => by simp [SFields.absOf, SFields.labels, SFields.labels_absOf F]

/-! ## Row views -/

theorem rowView_record_nonrec {fs : SFields} {t : SType} (ht : ∀ gs u, t ≠ .record gs u) :
    rowView (.record fs t) = (fs, t) := by
  simp [rowView, rowView_of_ne_record t ht, SFields.append_nil]

theorem rowView_restRow {ex : SFields} {t : SType} (ht : ∀ gs u, t ≠ .record gs u) :
    rowView (restRow ex t) = (ex, t) := by
  cases ex with
  | nil => exact rowView_of_ne_record t ht
  | cons => exact rowView_record_nonrec ht

theorem var_ne_record (w : Nat) : ∀ gs u, SType.var w ≠ .record gs u := fun _ _ h => nomatch h

/-! ## Kind lemmas -/

theorem KEmpty.of_nonvar {t : SType} (h : ∀ w, (rowView t).2 ≠ .var w) : KEmpty K t :=
  fun ρ hρ => absurd hρ (h ρ)

theorem KEmpty.abs : KEmpty K .abs := .of_nonvar fun _ h => nomatch h

theorem KOK.of_empty {a b : SType} (ha : KEmpty K a) (hb : KEmpty K b) : KOK K a b :=
  fun ρ σ hρ hσ l => ⟨fun h => absurd h (ha ρ hρ l), fun h => absurd h (hb σ hσ l)⟩

theorem KOK.of_nonvarL {a b : SType} (h : ∀ w, (rowView a).2 ≠ .var w) : KOK K a b :=
  fun ρ _ hρ => absurd hρ (h ρ)

theorem KOK.of_nonvarR {a b : SType} (h : ∀ w, (rowView b).2 ≠ .var w) : KOK K a b :=
  fun _ σ _ hσ => absurd hσ (h σ)

theorem KOK.trans_var {a b : SType} {v : Nat} (h₁ : KOK K a (.var v)) (h₂ : KOK K (.var v) b) :
    KOK K a b :=
  fun ρ σ hρ hσ l => (h₁ ρ v hρ rfl l).trans (h₂ v σ rfl hσ l)

theorem FWK.append : ∀ {fs gs : SFields}, FWK K fs → FWK K gs → FWK K (fs.append gs)
  | .nil, _, _, h => h
  | .cons _ _ _, _, ⟨hf, he, hr⟩, h => ⟨hf, he, FWK.append hr h⟩

theorem WK.rowView : ∀ t : SType, WK K t → FWK K (rowView t).1 ∧ WK K (rowView t).2
  | .record fs t, ⟨hf, ht, _⟩ => by
    have := WK.rowView t ht
    exact ⟨hf.append this.1, this.2⟩
  | .var _, _ | .prim _, _ | .abs, _ | .missing, _ | .nil, _ => ⟨trivial, trivial⟩
  | .arrow _ _, h | .opt _, h | .sig _, h => ⟨trivial, h⟩

/-! ## Argument records

The argument records of a signature are closed: they are well-kinded
whole types when the parameters' types are. -/

theorem rowView_closed (fs : SFields) : (rowView (.record fs .nil)).2 = .nil := by
  simp [rowView]

/-- A closed record of well-kinded fields is a well-kinded whole type. -/
theorem WK.closed {fs : SFields} (h : FWK K fs) :
    WK K (.record fs .nil) ∧ KEmpty K (.record fs .nil) :=
  ⟨⟨h, trivial, fun ρ hρ => by rw [rowView_closed] at hρ; exact nomatch hρ⟩,
    fun ρ hρ => by rw [rowView_closed] at hρ; exact nomatch hρ⟩

theorem PWK.mem : ∀ {P : SParams}, PWK K P → ∀ p ∈ P.toList, WK K p.ty ∧ KEmpty K p.ty
  | .nil, _, _, h => nomatch h
  | .cons _ _ _ _ _, ⟨h₁, h₂, h₃⟩, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨h₁, h₂⟩
    · exact h₃.mem p hp

theorem WK.list : ∀ {τs : List SType}, (∀ τ ∈ τs, WK K τ ∧ KEmpty K τ) →
    WK K (SType.list τs) ∧ KEmpty K (SType.list τs)
  | [], _ => WK.closed trivial
  | τ :: _, h =>
    have hτ := h τ (List.mem_cons_self ..)
    have ih := WK.list fun σ hσ => h σ (List.mem_cons_of_mem _ hσ)
    WK.closed ⟨hτ.1, hτ.2, ih.1, ih.2, trivial⟩

theorem FWK.ofParams : ∀ {ps : List (Param SType)}, (∀ p ∈ ps, WK K p.ty ∧ KEmpty K p.ty) →
    FWK K (SFields.ofParams ps)
  | [], _ => trivial
  | p :: _, h => by
    have hp := h p (List.mem_cons_self ..)
    refine ⟨?_, ?_, FWK.ofParams fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
    · cases ho : p.opt <;> simp only [Bool.false_eq_true, ite_true, ite_false]
      · exact hp.1
      · exact hp
    · cases ho : p.opt <;> simp only [Bool.false_eq_true, ite_true, ite_false]
      · exact hp.2
      · exact .of_nonvar fun _ h => nomatch h

/-- The argument records of a well-kinded signature are well-kinded whole
types. -/
theorem PWK.domain {P : SParams} (h : PWK K P) (k : Nat) :
    WK K (P.domain k) ∧ KEmpty K (P.domain k) :=
  have hl := WK.list (K := K) (τs := Param.pos k P.toList) fun _ hτ => by
    obtain ⟨p, hp, rfl⟩ := Param.mem_pos hτ
    exact h.mem p hp
  WK.closed ⟨hl.1, hl.2, FWK.ofParams fun p hp => h.mem p (Param.mem_named hp)⟩

theorem FWK.lookup {l : String} {f : SType} : ∀ {fs : SFields}, FWK K fs → fs.lookup l = some f →
    WK K f ∧ KEmpty K f
  | .nil, _, h => by simp [SFields.lookup] at h
  | .cons n g fs, ⟨hg, he, hr⟩, h => by
    simp only [SFields.lookup] at h
    split at h
    · cases h; exact ⟨hg, he⟩
    · exact hr.lookup h

theorem FWK.missing (fs₀ : SFields) : ∀ {fs₁ : SFields}, FWK K fs₁ → FWK K (fs₀.missing fs₁)
  | .nil, _ => trivial
  | .cons n f fs, ⟨hf, he, hr⟩ => by
    simp only [SFields.missing]
    split
    · exact FWK.missing fs₀ hr
    · exact ⟨hf, he, FWK.missing fs₀ hr⟩

theorem FWK.presentIn (Ks : List String) : ∀ {fs : SFields}, FWK K fs → FWK K (fs.presentIn Ks)
  | .nil, _ => trivial
  | .cons n f fs, ⟨hf, he, hr⟩ => by
    simp only [SFields.presentIn]
    split
    · exact FWK.presentIn Ks hr
    · exact ⟨hf, he, FWK.presentIn Ks hr⟩

theorem FWK.absentIn (Ks : List String) : ∀ {fs : SFields}, FWK K fs → FWK K (fs.absentIn Ks)
  | .nil, _ => trivial
  | .cons n f fs, ⟨hf, he, hr⟩ => by
    simp only [SFields.absentIn]
    split
    · exact ⟨hf, he, FWK.absentIn Ks hr⟩
    · exact FWK.absentIn Ks hr

theorem FWK.absOf : ∀ {F : SFields}, FWK K F.absOf
  | .nil => trivial
  | .cons _ _ _ => ⟨trivial, .abs, FWK.absOf⟩

theorem KEmpty.missing : KEmpty K .missing := .of_nonvar fun _ h => nomatch h

/-- The field constraints `Abs ≤ f` for the fields `f` of a well-kinded row
are between well-kinded fields that lack nothing. -/
theorem FWK.absPairs : ∀ {fs : SFields}, FWK K fs →
    ∀ p ∈ fs.absPairs, WK K p.1 ∧ WK K p.2 ∧ KEmpty K p.1 ∧ KEmpty K p.2
  | .nil, _, _, h => nomatch h
  | .cons _ f fs, ⟨hf, he, hr⟩, p, hp => by
    simp only [SFields.absPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨trivial, hf, .abs, he⟩
    · exact hr.absPairs p hp

/-- The same for `Missing ≤ f`. -/
theorem FWK.misPairs : ∀ {fs : SFields}, FWK K fs →
    ∀ p ∈ fs.misPairs, WK K p.1 ∧ WK K p.2 ∧ KEmpty K p.1 ∧ KEmpty K p.2
  | .nil, _, _, h => nomatch h
  | .cons _ f fs, ⟨hf, he, hr⟩, p, hp => by
    simp only [SFields.misPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨trivial, hf, .missing, he⟩
    · exact hr.misPairs p hp

/-- The same for `f ≤ Missing`. -/
theorem FWK.toMisPairs : ∀ {fs : SFields}, FWK K fs →
    ∀ p ∈ fs.toMisPairs, WK K p.1 ∧ WK K p.2 ∧ KEmpty K p.1 ∧ KEmpty K p.2
  | .nil, _, _, h => nomatch h
  | .cons _ f fs, ⟨hf, he, hr⟩, p, hp => by
    simp only [SFields.toMisPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨hf, trivial, he, .missing⟩
    · exact hr.toMisPairs p hp

theorem FWK.common {fs₀ : SFields} (h₀ : FWK K fs₀) : ∀ {fs₁ : SFields}, FWK K fs₁ →
    ∀ p ∈ fs₀.common fs₁, WK K p.1 ∧ WK K p.2 ∧ KEmpty K p.1 ∧ KEmpty K p.2
  | .nil, _, _, hp => nomatch hp
  | .cons n f fs, ⟨hf, he, hr⟩, p, hp => by
    simp only [SFields.common] at hp
    split at hp
    · next f₀ hl =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · have h := h₀.lookup hl
        exact ⟨h.1, hf, h.2, he⟩
      · exact FWK.common h₀ hr p hp
    · exact FWK.common h₀ hr p hp

/-! ## The invariant -/

/-- Every accepted constraint is well-kinded and relates rows lacking the
same labels. -/
def KLog (K : Nat → List String) (s : State) : Prop :=
  ∀ p ∈ s.log, WK K p.1 ∧ WK K p.2 ∧ KOK K p.1 p.2

/-- The expansion of `ρ` for labels `L` lacks what `ρ` lacks, and `L`. -/
def KExps (K : Nat → List String) (s : State) : Prop :=
  ∀ v L r, ((v, L), r) ∈ s.exps → ∀ l, l ∈ K r ↔ l ∈ K v ∨ l ∈ L

structure KInv (K : Nat → List String) (s : State) : Prop where
  kind : s.kind = K
  log : KLog K s
  exps : KExps K s

theorem KInv.remember {s : State} {a b : SType} (h : KInv K s) (ha : WK K a) (hb : WK K b)
    (hab : KOK K a b) : KInv K (s.remember a b) := by
  refine ⟨h.kind, fun p hp => ?_, h.exps⟩
  simp only [State.remember, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ⟨ha, hb, hab⟩
  · exact h.log p hp

theorem KInv.addUpper {s : State} (h : KInv K s) : KInv K (s.addUpper v b) :=
  ⟨h.kind, h.log, h.exps⟩

theorem KInv.addLower {s : State} (h : KInv K s) : KInv K (s.addLower v a) :=
  ⟨h.kind, h.log, h.exps⟩

theorem KInv.addExp {s : State} (h : KInv K s) (hr : ∀ l, l ∈ K r ↔ l ∈ K v ∨ l ∈ L) :
    KInv K { s with next := n, exps := ((v, L), r) :: s.exps } := by
  refine ⟨h.kind, h.log, fun w L' r' hm => ?_⟩
  simp only [List.mem_cons, Prod.mk.injEq] at hm
  rcases hm with ⟨⟨rfl, rfl⟩, rfl⟩ | hm
  · exact hr
  · exact h.exps w L' r' hm

/-- What expansion returns: the tail itself if it is not a row variable,
otherwise a row variable lacking the tail's kind and the expanded labels
(the tail itself when nothing is expanded). -/
def ExpRes (K : Nat → List String) (t : SType) (ms : SFields) (t' : SType) : Prop :=
  ((∀ w, t ≠ .var w) ∧ t' = t) ∨
  ∃ ρ r, t = .var ρ ∧ t' = .var r ∧ ∀ l, l ∈ K r ↔ l ∈ K ρ ∨ l ∈ (ms.presentIn (K ρ)).labels

theorem WK.restRow {ex : SFields} {t : SType} (hex : FWK K ex) (ht : WK K t)
    (hnr : ∀ gs u, t ≠ .record gs u) (hl : ∀ ρ, t = .var ρ → ∀ l ∈ ex.labels, l ∈ K ρ) :
    WK K (restRow ex t) := by
  cases ex with
  | nil => exact ht
  | cons n f fs =>
    refine ⟨hex, ht, fun σ hσ => ?_⟩
    rw [rowView_record_nonrec hnr] at hσ ⊢
    exact ⟨(fun h => nomatch h), hl σ hσ⟩

/-- The expansion constraint `ρ ≤ {P | r}` is well-kinded. -/
theorem expansion_wk {ρ r : Nat} {P : SFields} (hP : P ≠ .nil) (hw : FWK K P)
    (hdisj : ∀ l ∈ P.labels, l ∉ K ρ) (hr : ∀ l, l ∈ K r ↔ l ∈ K ρ ∨ l ∈ P.labels) :
    WK K (.var ρ) ∧ WK K (.record P (.var r)) ∧ KOK K (.var ρ) (.record P (.var r)) := by
  have e := rowView_record_nonrec (fs := P) (var_ne_record r)
  refine ⟨trivial, ⟨hw, trivial, fun σ hσ => ?_⟩, fun ρ' σ h₁ h₂ l => ?_⟩
  · rw [e] at hσ ⊢; cases hσ
    exact ⟨hP, fun l hl => (hr l).2 (.inr hl)⟩
  · rw [e] at h₂ ⊢; cases h₂; cases h₁
    simp only [RowKind, rowView, SFields.labels, List.not_mem_nil, not_false_eq_true, and_true]
    constructor
    · intro hl; exact ⟨(hr l).2 (.inl hl), fun hp => hdisj l hp hl⟩
    · intro ⟨hl, hp⟩
      rcases (hr l).1 hl with h | h
      · exact h
      · exact absurd h hp

/-- The rest constraint of a record constraint lacks the right labels. -/
theorem rest_kind {fs₀ fs₁ : SFields} {ρ σ r : Nat}
    (h₀ : ∀ l ∈ fs₀.labels, l ∈ K ρ) (h₁ : ∀ l ∈ fs₁.labels, l ∈ K σ)
    (hk : ∀ l, RowKind K fs₀ ρ l ↔ RowKind K fs₁ σ l)
    (hr : ∀ l, l ∈ K r ↔ l ∈ K ρ ∨ l ∈ ((fs₀.missing fs₁).presentIn (K ρ)).labels) (l : String) :
    RowKind K (fs₁.missing fs₀) r l ↔ RowKind K .nil σ l := by
  have a := hk l
  have b := hr l
  have c := h₀ l
  have d := h₁ l
  simp only [RowKind, SFields.mem_presentIn, SFields.mem_missing, SFields.labels,
    List.not_mem_nil, not_false_eq_true, and_true] at a b c d ⊢
  by_cases x₁ : l ∈ K ρ <;> by_cases x₂ : l ∈ K σ <;> by_cases x₃ : l ∈ fs₀.labels <;>
    by_cases x₄ : l ∈ fs₁.labels <;> by_cases x₅ : l ∈ K r <;> simp_all

mutual
theorem Constrain.kinds : Constrain s a b s' → Inv₂ s → KInv K s →
    WK K a → WK K b → KOK K a b → KInv K s'
  | .cached _, _, k, _, _, _ => k
  | .refl, _, k, _, _, _ => k
  | .arrow _ h₁ h₂, i, k, ha, hb, hab => by
    have k₀ := k.remember ha hb hab
    obtain ⟨wl₀, el₀, wr₀, er₀⟩ := ha
    obtain ⟨wl₁, el₁, wr₁, er₁⟩ := hb
    exact h₂.kinds (h₁.inv₂ i.remember) (h₁.kinds i.remember k₀ wl₁ wl₀ (.of_empty el₁ el₀))
      wr₀ wr₁ (.of_empty er₀ er₁)
  | .absR (a := a) _, _, k, ha, _, hab => k.remember (a := a) (b := .abs) ha trivial hab
  | .absRecord (fs := fs) (t := t) _ h₁ h₂, i, k, _, hb, _ => by
    have k₀ := k.remember (a := .abs) (b := .record fs t) trivial hb
      (.of_nonvarL fun _ h => nomatch h)
    obtain ⟨hfs, ht, _⟩ := hb
    exact h₂.kinds (h₁.inv₂ i.remember) (h₁.kinds i.remember k₀ hfs.absPairs) trivial ht
      (.of_nonvarL fun _ h => nomatch h)
  | .nilRecord (fs := fs) (t := t) _ h₁ h₂, i, k, _, hb, _ => by
    have k₀ := k.remember (a := .nil) (b := .record fs t) trivial hb
      (.of_nonvarL fun _ h => nomatch h)
    obtain ⟨hfs, ht, _⟩ := hb
    exact h₂.kinds (h₁.inv₂ i.remember) (h₁.kinds i.remember k₀ hfs.misPairs) trivial ht
      (.of_nonvarL fun _ h => nomatch h)
  | .recordNil (fa := fa) (ta := ta) _ e₀ h₁ h₂, i, k, ha, _, hab => by
    have v₀ := WK.rowView _ ha
    rw [e₀] at v₀
    have k₀ := k.remember (a := .record fa ta) (b := .nil) ha trivial hab
    exact h₂.kinds (h₁.inv₂ i.remember) (h₁.kinds i.remember k₀ v₀.1.toMisPairs) v₀.2 trivial
      (.of_nonvarR fun _ h => nomatch h)
  | .record (fa := fa) (ta := ta) (fb := fb) (tb := tb) (fs₀ := fs₀) (t₀ := t₀) (fs₁ := fs₁)
      (t₁ := t₁) (t₀' := t₀') _ e₀ e₁ h₁ h₂ h₃, i, k, ha, hb, hab => by
    have v₀ := WK.rowView _ ha
    have v₁ := WK.rowView _ hb
    rw [e₀] at v₀
    rw [e₁] at v₁
    have rec₀ : ∀ ρ, t₀ = .var ρ → ∀ l ∈ fs₀.labels, l ∈ K ρ := fun ρ h => by
      have := ha.2.2 ρ (by rw [e₀]; exact h); rw [e₀] at this; exact this.2
    have rec₁ : ∀ σ, t₁ = .var σ → ∀ l ∈ fs₁.labels, l ∈ K σ := fun σ h => by
      have := hb.2.2 σ (by rw [e₁]; exact h); rw [e₁] at this; exact this.2
    have hk : ∀ ρ σ, t₀ = .var ρ → t₁ = .var σ → ∀ l, RowKind K fs₀ ρ l ↔ RowKind K fs₁ σ l :=
      fun ρ σ h h' l => by
        have := hab ρ σ (by rw [e₀]; exact h) (by rw [e₁]; exact h') l
        rw [e₀, e₁] at this; exact this
    have nr₀ : ∀ gs u, t₀ ≠ .record gs u := by
      have := rowView_tail_ne_record (.record fa ta); rw [e₀] at this; exact this
    have nr₁ : ∀ gs u, t₁ ≠ .record gs u := by
      have := rowView_tail_ne_record (.record fb tb); rw [e₁] at this; exact this
    have k₀ := k.remember ha hb hab
    have i₁ := h₁.inv₂ i.remember
    have k₁ := h₁.kinds i.remember k₀ (FWK.common v₀.1 v₁.1)
    obtain ⟨k₂, res⟩ := h₂.kinds i₁ k₁ (FWK.missing fs₀ v₁.1) v₀.2
    have wex := FWK.missing fs₁ v₀.1
    -- the rest of the left row, over the expanded tail
    have hrest : WK K (restRow (fs₁.missing fs₀) t₀') ∧ KOK K (restRow (fs₁.missing fs₀) t₀') t₁ := by
      rcases res with ⟨hnv, he⟩ | ⟨ρ, r, rfl, rfl, hr⟩
      · rw [he]
        refine ⟨WK.restRow wex v₀.2 nr₀ (fun ρ h => absurd h (hnv ρ)), .of_nonvarL fun w h => ?_⟩
        rw [rowView_restRow nr₀] at h; exact hnv w h
      · have hsub : ∀ l ∈ (fs₁.missing fs₀).labels, l ∈ K r := fun l hl =>
          (hr l).2 (.inl (rec₀ ρ rfl l ((SFields.mem_missing fs₁ fs₀).1 hl).1))
        refine ⟨WK.restRow wex trivial (var_ne_record r) (fun ρ' h => by cases h; exact hsub),
          fun ρ' σ h h' l => ?_⟩
        rw [rowView_restRow (var_ne_record r)] at h ⊢
        cases h
        rw [rowView_of_ne_record t₁ nr₁] at h' ⊢
        cases h'
        exact rest_kind (rec₀ ρ rfl) (rec₁ σ rfl) (hk ρ σ rfl rfl) hr l
    exact h₃.kinds (h₂.inv₂ i₁) k₂ hrest.1 v₁.2 hrest.2
  | .varL (v := v) (b := b) _ _ h', i, k, _, hb, hab =>
    h'.kinds i.remember.addUpper (k.remember (a := .var v) (b := b) trivial hb hab).addUpper fun p hp => by
      simp only [List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      have := k.log _ (i.inLog.2 v x hx)
      exact ⟨this.1, hb, this.2.2.trans_var hab⟩
  | .varR (v := v) (a := a) _ hnv h', i, k, ha, _, hab =>
    h'.kinds (i.remember.addLower hnv) (k.remember (a := a) (b := .var v) ha trivial hab).addLower
      fun p hp => by
      simp only [List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      have := k.log _ (i.inLog.1 v x hx)
      exact ⟨ha, this.2.1, hab.trans_var this.2.2⟩
  | .recordSig (k := k) _ _ _ _ _ h', i, kk, ha, hb, hab =>
    h'.kinds i.remember (kk.remember ha hb hab) ha (PWK.domain hb k).1
      (.of_nonvarR fun w hw => by simp [SParams.domain, rowView_closed] at hw)
  | .sigL _ _ h', i, kk, ha, hb, hab =>
    h'.kinds i.remember (kk.remember ha hb hab) fun p hp => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
      exact ⟨(PWK.domain ha k).1, hb, .of_nonvarL fun w hw => by
        simp [SParams.domain, rowView_closed] at hw⟩

theorem ConstrainEach.kinds : ConstrainEach s ps s' → Inv₂ s → KInv K s →
    (∀ p ∈ ps, WK K p.1 ∧ WK K p.2 ∧ KOK K p.1 p.2) → KInv K s'
  | .nil, _, k, _ => k
  | .cons h₁ h₂, i, k, hps =>
    have hh := hps _ (List.mem_cons_self ..)
    h₂.kinds (h₁.inv₂ i) (h₁.kinds i k hh.1 hh.2.1 hh.2.2)
      fun p hp => hps p (List.mem_cons_of_mem _ hp)

/-- Fields lack nothing, and neither does the type of an optional field. -/
theorem ConstrainField.kinds : ConstrainField s a b s' → Inv₂ s → KInv K s →
    WK K a → WK K b → KEmpty K a → KEmpty K b → KInv K s'
  | .toAbs, _, k, _, _, _, _ | .misMis, _, k, _, _, _, _ | .misOpt, _, k, _, _, _, _ => k
  | .optOpt _ h, i, k, ha, hb, _, _ => h.kinds i k ha.1 hb.1 (.of_empty ha.2 hb.2)
  | .preOpt _ h, i, k, ha, hb, ea, _ => h.kinds i k ha hb.1 (.of_empty ea hb.2)
  | .pre _ _ h, i, k, ha, hb, ea, eb => h.kinds i k ha hb (.of_empty ea eb)

theorem FieldsEach.kinds : FieldsEach s ps s' → Inv₂ s → KInv K s →
    (∀ p ∈ ps, WK K p.1 ∧ WK K p.2 ∧ KEmpty K p.1 ∧ KEmpty K p.2) → KInv K s'
  | .nil, _, k, _ => k
  | .cons h₁ h₂, i, k, hps =>
    have hh := hps _ (List.mem_cons_self ..)
    h₂.kinds (h₁.inv₂ i) (h₁.kinds i k hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)
      fun p hp => hps p (List.mem_cons_of_mem _ hp)

theorem Expand.kinds : Expand s t ms t' s' → Inv₂ s → KInv K s → FWK K ms → WK K t →
    KInv K s' ∧ ExpRes K t ms t'
  | .none (t := t), _, k, _, _ => by
    refine ⟨k, ?_⟩
    cases t with
    | var ρ => exact .inr ⟨ρ, ρ, rfl, rfl, fun l => by simp [SFields.presentIn, SFields.labels]⟩
    | _ => exact .inl ⟨(fun _ h => nomatch h), rfl⟩
  | .abs _ h, i, k, hms, _ => ⟨h.kinds i k hms.absPairs, .inl ⟨(fun _ h => nomatch h), rfl⟩⟩
  | .nil _ h, i, k, hms, _ => ⟨h.kinds i k hms.misPairs, .inl ⟨(fun _ h => nomatch h), rfl⟩⟩
  | .allAbsent (s := s₀) (v := v) _ hp h, i, k, hms, _ => by
    refine ⟨h.kinds i k (FWK.absPairs (FWK.absentIn _ hms)), .inr ⟨v, v, rfl, rfl, fun l => ?_⟩⟩
    rw [← k.kind, hp]; simp [SFields.labels]
  | .memo (s := s₀) (v := v) (r := r) _ hP h₁ hl h₂, i, k, hms, _ => by
    have k₁ := h₁.kinds i k (FWK.absPairs (FWK.absentIn _ hms))
    have hr := k₁.exps _ _ _ (lookup_mem hl)
    have hK : s₀.kind v = K v := congrFun k.kind v
    have hw := expansion_wk (K := K) hP (FWK.presentIn _ hms)
      (fun l hl => hK ▸ ((SFields.mem_presentIn _ _).1 hl).2) hr
    have hr' := hr
    rw [hK] at hr'
    exact ⟨h₂.kinds (h₁.inv₂ i) k₁ hw.1 hw.2.1 hw.2.2, .inr ⟨v, r, rfl, rfl, hr'⟩⟩
  | .fresh (s := s₀) (s₁ := s₁) (v := v) _ hP h₁ _ hkn h₂, i, k, hms, _ => by
    have k₁ := h₁.kinds i k (FWK.absPairs (FWK.absentIn _ hms))
    have hK : s₀.kind v = K v := congrFun k.kind v
    have hr : ∀ l, l ∈ K s₁.next ↔ l ∈ K v ∨ l ∈ (ms.presentIn (s₀.kind v)).labels := by
      intro l; rw [← k.kind, hkn, List.mem_append]
    have hw := expansion_wk (K := K) hP (FWK.presentIn _ hms)
      (fun l hl => hK ▸ ((SFields.mem_presentIn _ _).1 hl).2) hr
    have hr' := hr
    rw [hK] at hr'
    exact ⟨h₂.kinds ((h₁.inv₂ i).of_bounds rfl fun _ hp => hp) (k₁.addExp hr) hw.1 hw.2.1 hw.2.2,
      .inr ⟨v, s₁.next, rfl, rfl, hr'⟩⟩
end

theorem ConstrainTop.kinds {s s' : State} (h : ConstrainTop s a b s') (i : Inv₂ s) (k : KInv K s)
    (ha : WK K a) (hb : WK K b) (hab : KOK K a b) : KInv K s' := by
  obtain ⟨s₁, hc, rfl⟩ := h
  have k₁ := hc.kinds (i.of_bounds rfl fun _ hp => hp) ⟨k.kind, k.log, k.exps⟩ ha hb hab
  exact ⟨k₁.kind, k₁.log, k₁.exps⟩

/-! ## Inferred types -/

/-- The context's types are well-kinded whole types. -/
def CtxK (K : Nat → List String) (Γ : SCtx) : Prop :=
  ∀ x st, Γ.lookup x = some st → WK K st ∧ KEmpty K st

theorem CtxK.cons {Γ : SCtx} (h : CtxK K Γ) (hw : WK K st) (he : KEmpty K st) :
    CtxK K ((x, st) :: Γ) := by
  intro y t hy
  simp only [SCtx.lookup, List.find?_cons] at hy
  split at hy
  · simp at hy; subst hy; exact ⟨hw, he⟩
  · exact h y t hy

/-- A fresh ordinary type variable lacks nothing. -/
theorem KEmpty.var_nil (h : K v = []) : KEmpty K (.var v) := fun ρ hρ l hl => by
  cases hρ
  have h₁ : l ∈ K v := hl.1
  rw [h] at h₁
  exact nomatch h₁

theorem TypeFields.ne_nil : TypeFields Γ s fs F s' → fs ≠ [] → F ≠ .nil
  | .nil, h => absurd rfl h
  | .cons _ _, _ => fun h => nomatch h

theorem SFields.absOf_ne_nil : ∀ {F : SFields}, F ≠ .nil → F.absOf ≠ .nil
  | .nil, h => absurd rfl h
  | .cons _ _ _, _ => fun h => nomatch h

mutual
/-- Typing preserves the kind invariant, and infers well-kinded whole types. -/
theorem TypeTerm.kinds : TypeTerm Γ s t st s' → CtxK K Γ → Inv₂ s → KInv K s →
    KInv K s' ∧ WK K st ∧ KEmpty K st
  | .lit, _, _, k => ⟨k, trivial, .of_nonvar (fun _ h => nomatch h)⟩
  | .var hx, hΓ, _, k => ⟨k, hΓ _ _ hx⟩
  | .lam hn h, hΓ, i, k => by
    have hv := KEmpty.var_nil (k.kind ▸ hn)
    have r := h.kinds (hΓ.cons trivial hv) i.fresh ⟨k.kind, k.log, k.exps⟩
    exact ⟨r.1, ⟨trivial, hv, r.2.1, r.2.2⟩, .of_nonvar (fun _ h => nomatch h)⟩
  | .app hn h₁ h₂ hc, hΓ, i, k => by
    have hv := KEmpty.var_nil (k.kind ▸ hn)
    have r₁ := h₁.kinds hΓ i.fresh ⟨k.kind, k.log, k.exps⟩
    have i₁ := h₁.inv₂ i.fresh
    have r₂ := h₂.kinds hΓ i₁ r₁.1
    exact ⟨hc.kinds (h₂.inv₂ i₁) r₂.1 r₁.2.1 ⟨r₂.2.1, r₂.2.2, trivial, hv⟩
      (.of_nonvarR (fun _ h => nomatch h)), trivial, hv⟩
  | .rcd h, hΓ, i, k => by
    have r := h.kinds hΓ i k
    exact ⟨r.1, ⟨r.2, trivial, fun _ h => nomatch h⟩, .of_nonvar (fun _ h => nomatch h)⟩
  | .sel hn h hc, hΓ, i, k => by
    have hv := KEmpty.var_nil (k.kind ▸ hn)
    have r := h.kinds hΓ i.fresh ⟨k.kind, k.log, k.exps⟩
    exact ⟨hc.kinds (h.inv₂ i.fresh) r.1 r.2.1
      ⟨⟨trivial, hv, trivial⟩, trivial, fun _ h => nomatch h⟩
      (.of_nonvarR (fun _ h => nomatch h)), trivial, hv⟩
  | .ite hn hc h₁ ha h₂ hb h₃, hΓ, i, k => by
    have hv := KEmpty.var_nil (k.kind ▸ hn)
    have rc := hc.kinds hΓ i.fresh ⟨k.kind, k.log, k.exps⟩
    have i₁ := hc.inv₂ i.fresh
    have k₁ := h₁.kinds i₁ rc.1 rc.2.1 trivial (.of_nonvarR (fun _ h => nomatch h))
    have i₂ := h₁.inv₂ i₁
    have ra := ha.kinds hΓ i₂ k₁
    have i₃ := ha.inv₂ i₂
    have k₂ := h₂.kinds i₃ ra.1 ra.2.1 trivial (.of_empty ra.2.2 hv)
    have i₄ := h₂.inv₂ i₃
    have rb := hb.kinds hΓ i₄ k₂
    exact ⟨h₃.kinds (hb.inv₂ i₄) rb.1 rb.2.1 trivial (.of_empty rb.2.2 hv), trivial, hv⟩
  | .selOr hn h hc hd hc', hΓ, i, k => by
    have hv := KEmpty.var_nil (k.kind ▸ hn)
    have r := h.kinds hΓ i.fresh ⟨k.kind, k.log, k.exps⟩
    have i₁ := h.inv₂ i.fresh
    have k₂ := hc.kinds i₁ r.1 r.2.1
      ⟨⟨⟨trivial, hv⟩, .of_nonvar (fun _ h => nomatch h), trivial⟩, trivial, fun _ h => nomatch h⟩
      (.of_nonvarR (fun _ h => nomatch h))
    have i₂ := hc.inv₂ i₁
    have rd := hd.kinds hΓ i₂ k₂
    exact ⟨hc'.kinds (hd.inv₂ i₂) rd.1 rd.2.1 trivial (.of_empty rd.2.2 hv), trivial, hv⟩
  | .ext (F := F) (s₂ := s₂) hfs h₁ h₂ hn hc, hΓ, i, k => by
    have r₁ := h₁.kinds hΓ i k
    have i₁ := h₁.inv₂ i
    have r₂ := h₂.kinds hΓ i₁ r₁.1
    have hF := h₂.ne_nil hfs
    have hn' : K s₂.next = F.labels := r₂.1.kind ▸ hn
    -- `{F' | ρ}` with `ρ` lacking exactly the labels of `F'`
    have row : ∀ F' : SFields, F' ≠ .nil → FWK K F' → F'.labels = F.labels →
        WK K (.record F' (.var s₂.next)) ∧ KEmpty K (.record F' (.var s₂.next)) := by
      intro F' hne hw hl
      have e := rowView_record_nonrec (fs := F') (var_ne_record s₂.next)
      refine ⟨⟨hw, trivial, fun σ hσ => ?_⟩, fun σ hσ l hk => ?_⟩
      · rw [e] at hσ ⊢; cases hσ
        exact ⟨hne, fun l h => by rw [hn', ← hl]; exact h⟩
      · rw [e] at hσ hk; cases hσ
        exact hk.2 (by rw [hl, ← hn']; exact hk.1)
    have rhs := row F.absOf (SFields.absOf_ne_nil hF) FWK.absOf (SFields.labels_absOf F)
    have res := row F hF r₂.2 rfl
    exact ⟨hc.kinds (h₂.inv₂ i₁).fresh ⟨r₂.1.kind, r₂.1.log, r₂.1.exps⟩ r₁.2.1 rhs.1
      (.of_empty r₁.2.2 rhs.2), res⟩
  | .extNil h, hΓ, i, k => h.kinds hΓ i k
  | .letIn h₁ h₂, hΓ, i, k => by
    have r₁ := h₁.kinds hΓ i k
    exact h₂.kinds (hΓ.cons r₁.2.1 r₁.2.2) (h₁.inv₂ i) r₁.1
  | .letRec (x := x) _ hn h₁ hc h₂, hΓ, i, k => by
    have hv := KEmpty.var_nil (k.kind ▸ hn)
    have hΓ' := hΓ.cons (x := x) (st := .var _) trivial hv
    have r₁ := h₁.kinds hΓ' i.fresh ⟨k.kind, k.log, k.exps⟩
    have i₁ := h₁.inv₂ i.fresh
    exact h₂.kinds hΓ' (hc.inv₂ i₁) (hc.kinds i₁ r₁.1 r₁.2.1 trivial (.of_empty r₁.2.2 hv))
  | .fn _ hp h, hΓ, i, k => by
    have rp := hp.kinds hΓ i k
    have r := h.kinds rp.2.2 (hp.inv₂ i) rp.1
    exact ⟨r.1, ⟨rp.2.1, .of_nonvar (fun _ h => nomatch h), r.2.1, r.2.2⟩,
      .of_nonvar (fun _ h => nomatch h)⟩

theorem TypeFields.kinds : TypeFields Γ s fs F s' → CtxK K Γ → Inv₂ s → KInv K s →
    KInv K s' ∧ FWK K F
  | .nil, _, _, k => ⟨k, trivial⟩
  | .cons h₁ h₂, hΓ, i, k => by
    have r₁ := h₁.kinds hΓ i k
    have r₂ := h₂.kinds hΓ (h₁.inv₂ i) r₁.1
    exact ⟨r₂.1, r₁.2.1, r₁.2.2, r₂.2⟩

/-- Parameters: the signature is well-kinded, and so is the body's context. -/
theorem TypeParams.kinds : TypeParams Γ s ps P Γ' s' → CtxK K Γ → Inv₂ s → KInv K s →
    KInv K s' ∧ PWK K P ∧ CtxK K Γ'
  | .nil, hΓ, _, k => ⟨k, trivial, hΓ⟩
  | .req (x := x) hn h, hΓ, i, k => by
    have hv := KEmpty.var_nil (k.kind ▸ hn)
    have r := h.kinds (hΓ.cons (x := x) (st := .var _) trivial hv) i.fresh ⟨k.kind, k.log, k.exps⟩
    exact ⟨r.1, ⟨trivial, hv, r.2.1⟩, r.2.2⟩
  | .dflt (x := x) hn hd hc h, hΓ, i, k => by
    have hv := KEmpty.var_nil (k.kind ▸ hn)
    have rd := hd.kinds hΓ i.fresh ⟨k.kind, k.log, k.exps⟩
    have i₁ := hd.inv₂ i.fresh
    have k₂ := hc.kinds i₁ rd.1 rd.2.1 trivial (.of_empty rd.2.2 hv)
    have r := h.kinds (hΓ.cons (x := x) (st := .var _) trivial hv) (hc.inv₂ i₁) k₂
    exact ⟨r.1, ⟨trivial, hv, r.2.1⟩, r.2.2⟩
end

theorem KInv.init : KInv K (State.initK K) :=
  ⟨rfl, (fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem builtins_K : CtxK K builtins := by
  intro x st h
  have hm := SCtx.lookup_mem h
  simp only [builtins, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [WK, PWK, builtinSig, KEmpty, rowView]

/-! ## Ranking tails by kinds -/

/-- The labels of the rows in accepted constraints. -/
def loggedLabels (s : State) : List String :=
  s.log.flatMap fun p => (rowView p.1).1.labels ++ (rowView p.2).1.labels

/-- The rank of a variable: how many logged labels it does not lack. -/
def kindRank (U : List String) (K : Nat → List String) (v : Nat) : Nat :=
  U.countP fun l => !decide (l ∈ K v)

theorem countP_lt {U A B : List String} {l : String} (hsub : ∀ x, x ∈ A → x ∈ B) (hl : l ∈ U)
    (hB : l ∈ B) (hA : l ∉ A) :
    U.countP (fun x => !decide (x ∈ B)) < U.countP (fun x => !decide (x ∈ A)) := by
  induction U with
  | nil => exact nomatch hl
  | cons y U ih =>
    have mono : U.countP (fun x => !decide (x ∈ B)) ≤ U.countP (fun x => !decide (x ∈ A)) :=
      List.countP_mono_left fun x _ h => by
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h ⊢
        exact fun hx => h (hsub x hx)
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [hB, hA]; omega
    · have := ih hl
      by_cases hyA : y ∈ A
      · simp [hyA, hsub y hyA]; omega
      · by_cases hyB : y ∈ B <;> simp [hyA, hyB] <;> omega

/-- Along a chain of variable bounds, kinds stay the same; the tail of the
record at its end lacks strictly more, including a logged label. -/
theorem clo_kinds {s : State} (k : KInv K s) (i : BoundsInLog s) {v : Nat} {u : SType} {ρ : Nat}
    (hc : Clo s.bounds v u) (hρ : (rowView u).2 = .var ρ) :
    (∀ x, x ∈ K v → x ∈ K ρ) ∧ ∃ l, l ∈ loggedLabels s ∧ l ∈ K ρ ∧ l ∉ K v := by
  induction hc with
  | @here n u hub hnv =>
    have hlog := i.1 _ _ hub
    have hw := (k.log _ hlog).2.1
    have hk := (k.log _ hlog).2.2 n ρ rfl hρ
    simp only [RowKind, rowView, SFields.labels, List.not_mem_nil, not_false_eq_true,
      and_true] at hk
    cases u with
    | var w => exact absurd rfl (hnv w)
    | prim _ | arrow _ _ | abs | missing | opt _ | nil | sig _ => simp [rowView] at hρ
    | record fs t =>
      have hr := hw.2.2 ρ hρ
      match hfs : (rowView (.record fs t)).1, hr with
      | .nil, hr => exact absurd rfl hr.1
      | .cons l f rest, hr =>
        have hl : l ∈ (rowView (.record fs t)).1.labels := by
          rw [hfs]; simp [SFields.labels]
        refine ⟨fun x hx => ((hk x).1 hx).1, l, ?_, hr.2 l (by simp [SFields.labels]), fun hv => ((hk l).1 hv).2 hl⟩
        exact List.mem_flatMap.mpr ⟨_, hlog, List.mem_append_right _ hl⟩
  | @step n m u hm _ ih =>
    have hk := (k.log _ (i.1 _ _ hm)).2.2 n m rfl rfl
    simp only [RowKind, rowView, SFields.labels, List.not_mem_nil, not_false_eq_true,
      and_true] at hk
    obtain ⟨h₁, l, h₂, h₃, h₄⟩ := ih hρ
    exact ⟨fun x hx => h₁ x ((hk x).1 hx), l, h₂, h₃, fun hl => h₄ ((hk l).1 hl)⟩

/-- A non-variable lower bound lacks what its variable lacks; its tail lacks
strictly more, including a logged label. -/
theorem lower_kinds {s : State} (k : KInv K s) (i : BoundsInLog s) {v ρ : Nat} {x : SType}
    (hx : x ∈ (s.bounds v).lower) (hnv : ∀ w, x ≠ .var w) (hρ : (rowView x).2 = .var ρ) :
    (∀ y, y ∈ K v → y ∈ K ρ) ∧ ∃ l, l ∈ loggedLabels s ∧ l ∈ K ρ ∧ l ∉ K v := by
  have hlog := i.2 _ _ hx
  have hw := (k.log _ hlog).1
  have hk := (k.log _ hlog).2.2 ρ v hρ rfl
  simp only [RowKind, rowView, SFields.labels, List.not_mem_nil, not_false_eq_true,
    and_true] at hk
  cases x with
  | var w => exact absurd rfl (hnv w)
  | prim _ | arrow _ _ | abs | missing | opt _ | nil | sig _ => simp [rowView] at hρ
  | record fs t =>
    have hr := hw.2.2 ρ hρ
    match hfs : (rowView (.record fs t)).1, hr with
    | .nil, hr => exact absurd rfl hr.1
    | .cons l f rest, hr =>
      have hl : l ∈ (rowView (.record fs t)).1.labels := by
        rw [hfs]; simp [SFields.labels]
      refine ⟨fun y hy => ((hk y).2 hy).1, l, ?_, hr.2 l (by simp [SFields.labels]),
        fun hv => ((hk l).2 hv).2 hl⟩
      exact List.mem_flatMap.mpr ⟨_, hlog, List.mem_append_left _ hl⟩

/-- **Kinds rank tails**: the kind invariant implies `TailRanked`. -/
theorem kinds_tailRanked {s : State} (k : KInv K s) (i : BoundsInLog s) :
    TailRanked s (kindRank (loggedLabels s) K) where
  clo := fun _ _ _ hc hρ =>
    let ⟨h₁, _, h₂, h₃, h₄⟩ := clo_kinds k i hc hρ
    countP_lt h₁ h₂ h₃ h₄
  upVar := fun v m hm => by
    have hk := (k.log _ (i.1 _ _ hm)).2.2 v m rfl rfl
    simp only [RowKind, rowView, SFields.labels, List.not_mem_nil, not_false_eq_true,
      and_true] at hk
    exact List.countP_mono_left fun x _ h => by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h ⊢
      exact fun hx => h ((hk x).1 hx)
  lower := fun _ _ _ hx hnv hρ =>
    let ⟨h₁, _, h₂, h₃, h₄⟩ := lower_kinds k i hx hnv hρ
    countP_lt h₁ h₂ h₃ h₄

/-! ## Theorem 1 -/

/-- **Theorem 1** (soundness of type inference), with no assumption left:
if the algorithm types `t` with `st` in the built-in context, for the kinds
`K` of its run, ending in state `s'`, then `t : θ(st)` in the declarative
system, where `θ` is the solution of `s'`. -/
theorem theorem1 (h : TypeTerm builtins (State.initK K) t st s') :
    Typ (defsOf s') builtins.toCtx t st.toTy :=
  soundness h (kinds_tailRanked (h.kinds builtins_K Inv₂.init KInv.init).1
    (h.inv₂ Inv₂.init).inLog)

end BoltCore.Alg
