import BoltCore.Locality

/-!
# Justification and consistency

The two invariants of the soundness of constraining (`Soundness.lean`), and
what they are stated with: the ghost log read as a relation (`Logged`), the
one-step justification of a constraint (`GStep`), the growth of a state
(`Grows`), and the invariants with pending pairs (`JustExcept`,
`ConsExcept`).
-/

namespace BoltCore.Alg

open State

/-! ## The one-step justification of a constraint -/

/-- A constraint is accepted by the log: reflexive, or logged. -/
def Logged (s : State) (a b : SType) : Prop := a = b ∨ (a, b) ∈ s.log

/-- A field constraint (mirrors `ConstrainField`): `Abs` is the top field,
`Missing` and a present field are below an optional one. A field is below
itself (the fields of a row expansion are those it was asked for). -/
inductive FieldR (R : SType → SType → Prop) : SType → SType → Prop where
  | refl : FieldR R f f
  | toAbs : FieldR R f .abs
  | misMis : FieldR R .missing .missing
  | misOpt : FieldR R .missing (.opt τ)
  | optOpt : τ₀ ≠ .abs → R τ₀ τ₁ → FieldR R (.opt τ₀) (.opt τ₁)
  | preOpt : f₀.IsPre → R f₀ τ₁ → FieldR R f₀ (.opt τ₁)
  | pre : f₀.IsPre → f₁.IsPre → R f₀ f₁ → FieldR R f₀ f₁

/-- The pair of the fields two lists have at a label is among their common
pairs. -/
theorem SFields.common_mem {f₀ f₁ : SType} {l : String} {fs₀ : SFields} :
    ∀ fs₁ : SFields, fs₁.lookup l = some f₁ → fs₀.lookup l = some f₀ →
      (f₀, f₁) ∈ fs₀.common fs₁
  | .nil, h, _ => by simp [SFields.lookup] at h
  | .cons n g rest, h₁, h₀ => by
    simp only [SFields.lookup] at h₁
    simp only [SFields.common]
    by_cases hn : n = l
    · subst hn
      simp at h₁
      subst h₁
      rw [h₀]
      exact List.mem_cons_self ..
    · simp only [hn, ite_false] at h₁
      have := SFields.common_mem rest h₁ h₀
      split
      · exact List.mem_cons_of_mem _ this
      · exact this

/-- Two field lists with the same labels, related field by field. -/
inductive SFields.Rel (Q : SType → SType → Prop) : SFields → SFields → Prop where
  | nil : SFields.Rel Q .nil .nil
  | cons : Q f g → SFields.Rel Q fs gs → SFields.Rel Q (.cons n f fs) (.cons n g gs)

theorem SFields.Rel.lookup {Q : SType → SType → Prop} {l : String} {g : SType} :
    ∀ {P' P : SFields}, SFields.Rel Q P' P → P.lookup l = some g →
      ∃ f, P'.lookup l = some f ∧ Q f g
  | _, _, .nil, h => by simp [SFields.lookup] at h
  | _, _, @SFields.Rel.cons _ f g' _ _ n hq r, h => by
    simp only [SFields.lookup] at h ⊢
    by_cases hn : n = l
    · simp only [hn, ite_true] at h ⊢; cases h; exact ⟨f, rfl, hq⟩
    · simp only [hn, ite_false] at h ⊢; exact r.lookup h

theorem SFields.Rel.lookup_none {Q : SType → SType → Prop} {l : String} :
    ∀ {P' P : SFields}, SFields.Rel Q P' P → P.lookup l = none → P'.lookup l = none
  | _, _, .nil, _ => rfl
  | _, _, @SFields.Rel.cons _ _ _ _ _ n _ r, h => by
    simp only [SFields.lookup] at h ⊢
    by_cases hn : n = l
    · simp [hn] at h
    · simp only [hn, ite_false] at h ⊢; exact r.lookup_none h

theorem SType.list_isPre : ∀ τs : List SType, (SType.list τs).IsPre
  | [] => trivial
  | _ :: _ => trivial

theorem SFields.append_nil : ∀ fs : SFields, fs.append .nil = fs
  | .nil => rfl
  | .cons _ _ fs => by simp [SFields.append, SFields.append_nil fs]

/-- How the left tail provides missing labels (mirrors `Expand`). A row
variable leaves the labels of *some* set `K` absent (in the algorithm, its
kind) and is expanded for the others. The kind itself plays no role in
soundness: an absent field is checked against `Abs`, the top field.

An expansion of `ρ` for fields `P` over `ρ'` is an *upper bound*
`{P' | ρ'}` of `ρ` whose fields are below those of `P`. The algorithm
model installs `P' = P`; an inferencer with levels installs the extrusion
of `P` when `P` mentions variables of higher level than `ρ`. -/
inductive ExpandG (σ : Nat → Bounds) (R : SType → SType → Prop) :
    SType → SFields → SType → Prop where
  | none : ExpandG σ R t .nil t
  | abs : ms ≠ .nil → (∀ p ∈ ms.absPairs, FieldR R p.1 p.2) → ExpandG σ R .abs ms .abs
  | nil : ms ≠ .nil → (∀ p ∈ ms.misPairs, FieldR R p.1 p.2) → ExpandG σ R .nil ms .nil
  | varAbsent (K : List String) : (∀ p ∈ (ms.absentIn K).absPairs, FieldR R p.1 p.2) →
      ms.presentIn K = .nil → ExpandG σ R (.var v) ms (.var v)
  | var (K : List String) : ms ≠ .nil → (∀ p ∈ (ms.absentIn K).absPairs, FieldR R p.1 p.2) →
      ms.presentIn K ≠ .nil → .record P' (.var r) ∈ (σ v).upper →
      SFields.Rel (FieldR R) P' (ms.presentIn K) →
      ExpandG σ R (.var v) ms (.var r)

/-- One decomposition step of a constraint, as the algorithm performs it,
relative to the bounds `σ` and the accepted constraints `R`. -/
inductive GStep (σ : Nat → Bounds) (R : SType → SType → Prop) : SType → SType → Prop where
  | absR : GStep σ R a .abs
  | arrow : R l₁ l₀ → R r₀ r₁ → GStep σ R (.arrow l₀ r₀) (.arrow l₁ r₁)
  | absRecord : (∀ p ∈ fs.absPairs, FieldR R p.1 p.2) → R .abs t →
      GStep σ R .abs (.record fs t)
  | nilRecord : (∀ p ∈ fs.misPairs, FieldR R p.1 p.2) → R .nil t →
      GStep σ R .nil (.record fs t)
  | recordNil : rowView (.record fa ta) = (fs₀, t₀) →
      (∀ p ∈ fs₀.toMisPairs, FieldR R p.1 p.2) → R t₀ .nil →
      GStep σ R (.record fa ta) .nil
  /-- The fields are compared label by label: the first field of each
  label on the left with the first on the right (a repeated label is
  shadowed, as in `Ty.field`). The algorithm compares every field of the
  right side, which is more than a step needs. -/
  | record : rowView (.record fa ta) = (fs₀, t₀) → rowView (.record fb tb) = (fs₁, t₁) →
      (∀ l f₀ f₁, fs₀.lookup l = some f₀ → fs₁.lookup l = some f₁ → FieldR R f₀ f₁) →
      ExpandG σ R t₀ (fs₀.missing fs₁) t₀' →
      R (restRow (fs₁.missing fs₀) t₀') t₁ →
      GStep σ R (.record fa ta) (.record fb tb)
  | varL : b ∈ (σ v).upper → GStep σ R (.var v) b
  | varR : a ∈ (σ v).lower → GStep σ R a (.var v)
  /-- Through an upper bound: `v ≤ b'` and `b' ≤ b`, between non-variables
  (as extrusion produces: `b'` is the extrusion of `b` to `v`'s level). -/
  | viaL : b' ∈ (σ v).upper → (∀ w, b' ≠ .var w) → b' ≠ .abs → (∀ w, b ≠ .var w) →
      R b' b → GStep σ R (.var v) b
  /-- Through a lower bound: `a ≤ a'` and `a' ≤ v`, between non-variables. -/
  | viaR : a' ∈ (σ v).lower → (∀ w, a' ≠ .var w) → a' ≠ .abs → (∀ w, a ≠ .var w) →
      a ≠ .abs → R a a' → GStep σ R a (.var v)
  /-- Between variables, through a variable `m` that is an upper bound of
  `v` and a lower bound of `w`. Extrusion produces this: when `v` is a
  lower bound of `u` and both are copied, the copy `m` of `v` is an upper
  bound of `v` and a lower bound of the copy `w` of `u`, and consistency
  at `u` asks for `v ≤ w`. -/
  | viaVar : .var m ∈ (σ v).upper → .var m ∈ (σ w).lower → GStep σ R (.var v) (.var w)
  /-- A record below a signature: it is below one of its argument records. -/
  | recordSig : d ∈ P.domains → R (.record fa ta) d → GStep σ R (.record fa ta) (.sig P)
  /-- A signature below a record or a signature: each argument record is. -/
  | sigL : b.IsRecSig → (∀ d ∈ P.domains, R d b) → GStep σ R (.sig P) b

/-! ## Growth of the state -/

/-- The algorithm only ever adds bounds, log entries and cache entries. -/
structure Grows (s s' : State) : Prop where
  lower : ∀ v x, x ∈ (s.bounds v).lower → x ∈ (s'.bounds v).lower
  upper : ∀ v x, x ∈ (s.bounds v).upper → x ∈ (s'.bounds v).upper
  log : ∀ p, p ∈ s.log → p ∈ s'.log
  cache : ∀ p, p ∈ s.cache → p ∈ s'.cache
  /-- Kinds never change. -/
  kind : s'.kind = s.kind
  /-- Neither do levels. -/
  level : s'.level = s.level

namespace Grows

theorem refl : Grows s s := ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, rfl, rfl⟩

theorem trans (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) : Grows s₁ s₃ :=
  ⟨fun v x h => h₂.lower v x (h₁.lower v x h), fun v x h => h₂.upper v x (h₁.upper v x h),
   fun p h => h₂.log p (h₁.log p h), fun p h => h₂.cache p (h₁.cache p h),
   h₂.kind.trans h₁.kind, h₂.level.trans h₁.level⟩

theorem remember : Grows s (s.remember a b) :=
  ⟨fun _ _ h => h, fun _ _ h => h,
   fun _ h => List.mem_cons_of_mem _ h, fun _ h => List.mem_cons_of_mem _ h, rfl, rfl⟩

theorem addUpper : Grows s (s.addUpper v t) := by
  refine ⟨fun w x h => ?_, fun w x h => ?_, fun _ h => h, fun _ h => h, rfl, rfl⟩
  · simp only [State.addUpper]; split <;> simpa
  · simp only [State.addUpper]; split
    · next he => subst he; exact List.mem_cons_of_mem _ h
    · exact h

theorem addLower : Grows s (s.addLower v t) := by
  refine ⟨fun w x h => ?_, fun w x h => ?_, fun _ h => h, fun _ h => h, rfl, rfl⟩
  · simp only [State.addLower]; split
    · next he => subst he; exact List.mem_cons_of_mem _ h
    · exact h
  · simp only [State.addLower]; split <;> simpa

theorem expand : Grows s { s with next := n, exps := e } :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, rfl, rfl⟩

theorem fresh : Grows s s.fresh :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, rfl, rfl⟩

theorem logAll : Grows s (s.logAll ps) :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => List.mem_append_right _ h, fun _ h => h, rfl, rfl⟩

theorem addUppers : Grows s (s.addUppers v ts) := by
  refine ⟨fun w x h => ?_, fun w x h => ?_, fun _ h => h, fun _ h => h, rfl, rfl⟩
  · simp only [State.addUppers]; split <;> simpa
  · simp only [State.addUppers]; split
    · next he => subst he; exact List.mem_append_right _ h
    · exact h

theorem addLowers : Grows s (s.addLowers v ts) := by
  refine ⟨fun w x h => ?_, fun w x h => ?_, fun _ h => h, fun _ h => h, rfl, rfl⟩
  · simp only [State.addLowers]; split
    · next he => subst he; exact List.mem_append_right _ h
    · exact h
  · simp only [State.addLowers]; split <;> simpa

end Grows

theorem mem_upper_addUpper {s : State} {v : Nat} {t : SType} : t ∈ ((s.addUpper v t).bounds v).upper := by
  simp [State.addUpper]

theorem mem_lower_addLower {s : State} {v : Nat} {t : SType} : t ∈ ((s.addLower v t).bounds v).lower := by
  simp [State.addLower]

theorem lower_addUpper {s : State} {v w : Nat} {t : SType} : ((s.addUpper v t).bounds w).lower = (s.bounds w).lower := by
  simp only [State.addUpper]; split <;> rfl

theorem upper_addLower {s : State} {v w : Nat} {t : SType} : ((s.addLower v t).bounds w).upper = (s.bounds w).upper := by
  simp only [State.addLower]; split <;> rfl

theorem mem_upper_addUpper_inv {s : State} {v w : Nat} {t x : SType} (h : x ∈ ((s.addUpper v t).bounds w).upper) :
    (w = v ∧ x = t) ∨ x ∈ (s.bounds w).upper := by
  simp only [State.addUpper] at h
  split at h
  · next he => simp at h; rcases h with h | h; exact Or.inl ⟨he, h⟩; exact Or.inr (he ▸ h)
  · exact Or.inr h

theorem mem_lower_addLower_inv {s : State} {v w : Nat} {t x : SType} (h : x ∈ ((s.addLower v t).bounds w).lower) :
    (w = v ∧ x = t) ∨ x ∈ (s.bounds w).lower := by
  simp only [State.addLower] at h
  split at h
  · next he => simp at h; rcases h with h | h; exact Or.inl ⟨he, h⟩; exact Or.inr (he ▸ h)
  · exact Or.inr h

/-! ## Monotonicity of the justification -/

theorem Logged.mono (g : Grows s s') : Logged s a b → Logged s' a b
  | .inl h => .inl h
  | .inr h => .inr (g.log _ h)

theorem SFields.Rel.refl_logged {s : State} : ∀ fs : SFields, SFields.Rel (FieldR (Logged s)) fs fs
  | .nil => .nil
  | .cons _ _ fs => .cons .refl (SFields.Rel.refl_logged fs)

theorem FieldR.mono (hR : ∀ x y, R x y → R' x y) : FieldR R a b → FieldR R' a b
  | .refl => .refl
  | .toAbs => .toAbs
  | .misMis => .misMis
  | .misOpt => .misOpt
  | .optOpt h₀ h => .optOpt h₀ (hR _ _ h)
  | .preOpt h₀ h => .preOpt h₀ (hR _ _ h)
  | .pre h₀ h₁ h => .pre h₀ h₁ (hR _ _ h)

theorem SFields.Rel.mono {Q Q' : SType → SType → Prop} (hQ : ∀ x y, Q x y → Q' x y) :
    SFields.Rel Q fs gs → SFields.Rel Q' fs gs
  | .nil => .nil
  | .cons h r => .cons (hQ _ _ h) (r.mono hQ)

theorem ExpandG.mono (hσ : ∀ v x, x ∈ (σ v).upper → x ∈ (σ' v).upper)
    (hR : ∀ x y, R x y → R' x y) : ExpandG σ R t ms t' → ExpandG σ' R' t ms t'
  | .none => .none
  | .abs hm h => .abs hm (fun p hp => (h p hp).mono hR)
  | .nil hm h => .nil hm (fun p hp => (h p hp).mono hR)
  | .varAbsent K h hp => .varAbsent K (fun p q => (h p q).mono hR) hp
  | .var K hm h hp hu hrel =>
    .var K hm (fun p q => (h p q).mono hR) hp (hσ _ _ hu) (hrel.mono fun _ _ h => h.mono hR)

theorem GStep.mono (g : Grows s s') :
    GStep s.bounds (Logged s) a b → GStep s'.bounds (Logged s') a b
  | .absR => .absR
  | .arrow h₁ h₂ => .arrow (h₁.mono g) (h₂.mono g)
  | .absRecord hf ht => .absRecord (fun p hp => (hf p hp).mono fun _ _ => Logged.mono g) (ht.mono g)
  | .nilRecord hf ht => .nilRecord (fun p hp => (hf p hp).mono fun _ _ => Logged.mono g) (ht.mono g)
  | .recordNil h₀ hf ht =>
    .recordNil h₀ (fun p hp => (hf p hp).mono fun _ _ => Logged.mono g) (ht.mono g)
  | .record h₀ h₁ hf he ht =>
    .record h₀ h₁ (fun l f₀ f₁ e₀ e₁ => (hf l f₀ f₁ e₀ e₁).mono fun _ _ => Logged.mono g)
      (he.mono g.upper fun _ _ => Logged.mono g) (ht.mono g)
  | .varL h => .varL (g.upper _ _ h)
  | .varR h => .varR (g.lower _ _ h)
  | .viaL h h₁ h₂ h₃ h₄ => .viaL (g.upper _ _ h) h₁ h₂ h₃ (h₄.mono g)
  | .viaR h h₁ h₂ h₃ h₄ h₅ => .viaR (g.lower _ _ h) h₁ h₂ h₃ h₄ (h₅.mono g)
  | .viaVar h₁ h₂ => .viaVar (g.upper _ _ h₁) (g.lower _ _ h₂)
  | .recordSig hd h => .recordSig hd (h.mono g)
  | .sigL hb h => .sigL hb fun d hd => (h d hd).mono g

/-- A step stays one when the bounds and the accepted constraints grow. -/
theorem GStep.imp {σ σ' : Nat → Bounds} {R R' : SType → SType → Prop}
    (hu : ∀ v x, x ∈ (σ v).upper → x ∈ (σ' v).upper)
    (hl : ∀ v x, x ∈ (σ v).lower → x ∈ (σ' v).lower) (hR : ∀ x y, R x y → R' x y) :
    GStep σ R a b → GStep σ' R' a b
  | .absR => .absR
  | .arrow h₁ h₂ => .arrow (hR _ _ h₁) (hR _ _ h₂)
  | .absRecord hf ht => .absRecord (fun p hp => (hf p hp).mono hR) (hR _ _ ht)
  | .nilRecord hf ht => .nilRecord (fun p hp => (hf p hp).mono hR) (hR _ _ ht)
  | .recordNil h₀ hf ht => .recordNil h₀ (fun p hp => (hf p hp).mono hR) (hR _ _ ht)
  | .record h₀ h₁ hf he ht =>
    .record h₀ h₁ (fun l f₀ f₁ e₀ e₁ => (hf l f₀ f₁ e₀ e₁).mono hR) (he.mono hu hR) (hR _ _ ht)
  | .varL h => .varL (hu _ _ h)
  | .varR h => .varR (hl _ _ h)
  | .viaL h h₁ h₂ h₃ h₄ => .viaL (hu _ _ h) h₁ h₂ h₃ (hR _ _ h₄)
  | .viaR h h₁ h₂ h₃ h₄ h₅ => .viaR (hl _ _ h) h₁ h₂ h₃ h₄ (hR _ _ h₅)
  | .viaVar h₁ h₂ => .viaVar (hu _ _ h₁) (hl _ _ h₂)
  | .recordSig hd h => .recordSig hd (hR _ _ h)
  | .sigL hb h => .sigL hb fun d hd => hR _ _ (h d hd)

/-! ## Justification -/

/-- Every logged constraint is justified, except possibly the `pending` ones
(whose justification is still being computed). -/
def JustExcept (s : State) (pending : List (SType × SType)) : Prop :=
  ∀ p, p ∈ s.log → p ∈ pending ∨ GStep s.bounds (Logged s) p.1 p.2

def Justified (s : State) : Prop := JustExcept s []

theorem JustExcept.grow (g : Grows s s') (hlog : ∀ p, p ∈ s'.log → p ∈ s.log)
    (h : JustExcept s P) : JustExcept s' P := fun p hp =>
  (h p (hlog p hp)).imp id (GStep.mono g)

/-- Remembering a pair makes it pending. -/
theorem JustExcept.remember (h : JustExcept s P) : JustExcept (s.remember a b) ((a, b) :: P) := by
  intro p hp
  simp only [State.remember, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact .inl (List.mem_cons_self ..)
  · exact (h p hp).imp (List.mem_cons_of_mem _) (GStep.mono .remember)

/-- A pending pair whose step now holds is no longer pending. -/
theorem JustExcept.close (h : JustExcept s ((a, b) :: P))
    (hs : GStep s.bounds (Logged s) a b) : JustExcept s P := by
  intro p hp
  rcases h p hp with hq | hg
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact .inr hs
    · exact .inl hq
  · exact .inr hg

/-! ## Consistency -/

/-- Every lower bound of a variable is logged below each of its upper
bounds, except possibly for the `pending` pairs. -/
def ConsExcept (s : State) (pending : List (SType × SType)) : Prop :=
  ∀ v l u, l ∈ (s.bounds v).lower → u ∈ (s.bounds v).upper → Logged s l u ∨ (l, u) ∈ pending

def Consistent (s : State) : Prop := ConsExcept s []

theorem ConsExcept.weaken (h : ConsExcept s P) (hP : ∀ p, p ∈ P → p ∈ P') : ConsExcept s P' :=
  fun v l u hl hu => (h v l u hl hu).imp id (hP _)

theorem ConsExcept.remember (h : ConsExcept s P) : ConsExcept (s.remember a b) P :=
  fun v l u hl hu => (h v l u hl hu).imp (Logged.mono .remember) id

theorem ConsExcept.expand (h : ConsExcept s P) :
    ConsExcept { s with next := n, exps := e } P := h

/-- Installing an upper bound `b` on `v` makes `(l, b)` pending for every
lower bound `l` of `v`. -/
theorem ConsExcept.addUpper (h : ConsExcept s P) :
    ConsExcept (s.addUpper v b) ((s.bounds v).lower.map (·, b) ++ P) := by
  intro w l u hl hu
  rw [lower_addUpper] at hl
  rcases mem_upper_addUpper_inv hu with ⟨rfl, rfl⟩ | hu
  · exact .inr (List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩))
  · exact (h w l u hl hu).imp (Logged.mono .addUpper) (List.mem_append_right _)

theorem ConsExcept.addLower (h : ConsExcept s P) :
    ConsExcept (s.addLower v a) ((s.bounds v).upper.map (a, ·) ++ P) := by
  intro w l u hl hu
  rw [upper_addLower] at hu
  rcases mem_lower_addLower_inv hl with ⟨rfl, rfl⟩ | hl
  · exact .inr (List.mem_append_left _ (List.mem_map.mpr ⟨u, hu, rfl⟩))
  · exact (h w l u hl hu).imp (Logged.mono .addLower) (List.mem_append_right _)

/-! ## Bounds are logged -/

/-- Every bound was installed by a logged constraint. -/
def BoundsInLog (s : State) : Prop :=
  (∀ v x, x ∈ (s.bounds v).upper → (.var v, x) ∈ s.log) ∧
  (∀ v x, x ∈ (s.bounds v).lower → (x, .var v) ∈ s.log)

end BoltCore.Alg
