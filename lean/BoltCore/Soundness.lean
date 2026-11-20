import BoltCore.Algorithm

/-!
# Soundness of constraining, at the level of the bound graph

The paper's Lemma 2 (soundness of constraining) says that when
`constrain` succeeds, the bounds stay consistent and the constrained types
become subtypes. Proving it directly on coalesced types mixes two
difficulties: the algorithm's bookkeeping (the cache, propagation, and the
temporarily broken consistency the paper warns about) and coalescing bounds
into recursive types. This file does the first part, on the algorithm's
state; relating it to `Sub` through coalescing is the next step.

The model's state has a ghost `log` of every constraint ever accepted. We
prove that two invariants hold of every state the algorithm reaches:

* **Justification** (`Justified`): every logged constraint is justified by
  one decomposition step (`GStep`) with respect to the current bounds: the
  two halves of an arrow constraint are logged, the bound of a variable is
  present, the fields, expansion and tail of a record constraint are
  logged. Read coinductively, the log is a self-justifying set of
  constraints, and a cache hit is a use of the coinductive hypothesis.
* **Consistency** (`Consistent`): for every variable, each lower bound is
  logged below each upper bound.

Right after a bound is installed, consistency fails until propagation is
done (Sec. 3.2.2 of the paper). The proofs therefore carry a set of
*pending* pairs (`ConsExcept`, `JustExcept`), which shrinks as the
propagation calls succeed.
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

/-- Two field lists with the same labels, related field by field. -/
inductive SFields.Rel (Q : SType → SType → Prop) : SFields → SFields → Prop where
  | nil : SFields.Rel Q .nil .nil
  | cons : Q f g → SFields.Rel Q fs gs → SFields.Rel Q (.cons n f fs) (.cons n g gs)

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
  | record : rowView (.record fa ta) = (fs₀, t₀) → rowView (.record fb tb) = (fs₁, t₁) →
      (∀ p ∈ fs₀.common fs₁, FieldR R p.1 p.2) →
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

namespace Grows

theorem refl : Grows s s := ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, rfl⟩

theorem trans (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) : Grows s₁ s₃ :=
  ⟨fun v x h => h₂.lower v x (h₁.lower v x h), fun v x h => h₂.upper v x (h₁.upper v x h),
   fun p h => h₂.log p (h₁.log p h), fun p h => h₂.cache p (h₁.cache p h),
   h₂.kind.trans h₁.kind⟩

theorem remember : Grows s (s.remember a b) :=
  ⟨fun _ _ h => h, fun _ _ h => h,
   fun _ h => List.mem_cons_of_mem _ h, fun _ h => List.mem_cons_of_mem _ h, rfl⟩

theorem addUpper : Grows s (s.addUpper v t) := by
  refine ⟨fun w x h => ?_, fun w x h => ?_, fun _ h => h, fun _ h => h, rfl⟩
  · simp only [State.addUpper]; split <;> simpa
  · simp only [State.addUpper]; split
    · next he => subst he; exact List.mem_cons_of_mem _ h
    · exact h

theorem addLower : Grows s (s.addLower v t) := by
  refine ⟨fun w x h => ?_, fun w x h => ?_, fun _ h => h, fun _ h => h, rfl⟩
  · simp only [State.addLower]; split
    · next he => subst he; exact List.mem_cons_of_mem _ h
    · exact h
  · simp only [State.addLower]; split <;> simpa

theorem expand : Grows s { s with next := n, exps := e } :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, rfl⟩

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

mutual
theorem Constrain.grows : Constrain s a b s' → Grows s s'
  | .cached _ => .refl
  | .refl => .refl
  | .arrow _ h₁ h₂ => Grows.remember.trans (h₁.grows.trans h₂.grows)
  | .absR _ => .remember
  | .absRecord _ h₁ h₂ => Grows.remember.trans (h₁.grows.trans h₂.grows)
  | .nilRecord _ h₁ h₂ => Grows.remember.trans (h₁.grows.trans h₂.grows)
  | .recordNil _ _ h₁ h₂ => Grows.remember.trans (h₁.grows.trans h₂.grows)
  | .record _ _ _ h₁ h₂ h₃ => Grows.remember.trans (h₁.grows.trans (h₂.grows.trans h₃.grows))
  | .varL _ _ h => (Grows.remember.trans .addUpper).trans h.grows
  | .varR _ _ h => (Grows.remember.trans .addLower).trans h.grows
  | .recordSig _ _ _ _ _ h => Grows.remember.trans h.grows
  | .sigL _ _ h => Grows.remember.trans h.grows

theorem ConstrainEach.grows : ConstrainEach s ps s' → Grows s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.grows.trans h₂.grows

theorem ConstrainField.grows : ConstrainField s a b s' → Grows s s'
  | .toAbs | .misMis | .misOpt => .refl
  | .optOpt _ h | .preOpt _ h | .pre _ _ h => h.grows

theorem FieldsEach.grows : FieldsEach s ps s' → Grows s s'
  | .nil => .refl
  | .cons h₁ h₂ => h₁.grows.trans h₂.grows

theorem Expand.grows : Expand s t ms t' s' → Grows s s'
  | .none => .refl
  | .abs _ h | .nil _ h => h.grows
  | .allAbsent _ _ h => h.grows
  | .memo _ _ h₁ _ h₂ => h₁.grows.trans h₂.grows
  | .fresh _ _ h₁ _ _ h₂ => h₁.grows.trans (Grows.expand.trans h₂.grows)
end

/-! ## Monotonicity of the justification -/

theorem Logged.mono (g : Grows s s') : Logged s a b → Logged s' a b
  | .inl h => .inl h
  | .inr h => .inr (g.log _ h)

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
    .record h₀ h₁ (fun p hp => (hf p hp).mono fun _ _ => Logged.mono g)
      (he.mono g.upper fun _ _ => Logged.mono g) (ht.mono g)
  | .varL h => .varL (g.upper _ _ h)
  | .varR h => .varR (g.lower _ _ h)
  | .viaL h h₁ h₂ h₃ h₄ => .viaL (g.upper _ _ h) h₁ h₂ h₃ (h₄.mono g)
  | .viaR h h₁ h₂ h₃ h₄ h₅ => .viaR (g.lower _ _ h) h₁ h₂ h₃ h₄ (h₅.mono g)
  | .recordSig hd h => .recordSig hd (h.mono g)
  | .sigL hb h => .sigL hb fun d hd => (h d hd).mono g

/-! ## Every accepted constraint is logged -/

/-- Cache hits are uses of logged constraints; a cached constraint with a
variable on the left (and not `Abs` on the right) has installed its upper
bound, since only `varL` caches such constraints. -/
def CacheInLog (s : State) : Prop :=
  (∀ p, p ∈ s.cache → p ∈ s.log) ∧
  (∀ v b, (.var v, b) ∈ s.cache → b ≠ .abs → b ∈ (s.bounds v).upper)

theorem CacheInLog.remember (h : CacheInLog s)
    (h' : (∀ w, a ≠ .var w) ∨ b = .abs := by
      first | exact .inr rfl | exact .inl ‹_› | exact .inl (fun _ h => nomatch h)) :
    CacheInLog (s.remember a b) := by
  refine ⟨fun p hp => ?_, fun v x hx hxa => ?_⟩
  · simp only [State.remember, List.mem_cons] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr (h.1 p hp)
  · simp only [State.remember, List.mem_cons] at hx
    rcases hx with hx | hx
    · cases hx
      rcases h' with h' | h'
      · exact absurd rfl (h' v)
      · exact absurd h' hxa
    · exact h.2 v x hx hxa

theorem CacheInLog.addUpper (h : CacheInLog s) : CacheInLog (s.addUpper v t) :=
  ⟨h.1, fun w x hx hxa => Grows.addUpper.upper w x (h.2 w x hx hxa)⟩

theorem CacheInLog.addLower (h : CacheInLog s) : CacheInLog (s.addLower v t) :=
  ⟨h.1, fun w x hx hxa => by rw [upper_addLower]; exact h.2 w x hx hxa⟩

/-- Caching `v ≤ b` and installing the bound together. -/
theorem CacheInLog.rememberUpper (h : CacheInLog s) :
    CacheInLog ((s.remember (.var v) b).addUpper v b) := by
  refine ⟨fun p hp => ?_, fun w x hx hxa => ?_⟩
  · simp only [State.addUpper, State.remember, List.mem_cons] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr (h.1 p hp)
  · simp only [State.addUpper, State.remember, List.mem_cons] at hx
    rcases hx with hx | hx
    · simp only [Prod.mk.injEq, SType.var.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact mem_upper_addUpper
    · exact Grows.addUpper.upper w x (Grows.remember.upper w x (h.2 w x hx hxa))

theorem remember_logged {s : State} {a b : SType} : Logged (s.remember a b) a b := .inr (List.mem_cons_self ..)

/-- Constraining a variable below a non-variable installs the bound. -/
theorem Constrain.installs (h : Constrain s (.var v) b s') (hc : CacheInLog s) (hb : b ≠ .abs)
    (hnv : ∀ w, b ≠ .var w) : b ∈ (s'.bounds v).upper := by
  cases h with
  | cached hm => exact hc.2 v b hm hb
  | refl => exact absurd rfl (hnv v)
  | absR => exact absurd rfl hb
  | varL _ _ h' => exact h'.grows.upper _ _ mem_upper_addUpper
  | varR _ hnv' _ => exact absurd rfl (hnv' v)

theorem SFields.Rel.refl_logged {s : State} : ∀ fs : SFields, SFields.Rel (FieldR (Logged s)) fs fs
  | .nil => .nil
  | .cons _ _ fs => .cons .refl (SFields.Rel.refl_logged fs)

mutual
theorem Constrain.logged : Constrain s a b s' → CacheInLog s → CacheInLog s' ∧ Logged s' a b
  | .cached hm, hc => ⟨hc, .inr (hc.1 _ hm)⟩
  | .refl, hc => ⟨hc, .inl rfl⟩
  | .arrow _ h₁ h₂, hc =>
    have r₁ := h₁.logged hc.remember
    have r₂ := h₂.logged r₁.1
    ⟨r₂.1, remember_logged.mono (h₁.grows.trans h₂.grows)⟩
  | .absR _, hc => ⟨hc.remember, remember_logged⟩
  | .absRecord _ h₁ h₂, hc =>
    have r₁ := h₁.logged hc.remember
    have r₂ := h₂.logged r₁.1
    ⟨r₂.1, remember_logged.mono (h₁.grows.trans h₂.grows)⟩
  | .nilRecord _ h₁ h₂, hc =>
    have r₁ := h₁.logged hc.remember
    have r₂ := h₂.logged r₁.1
    ⟨r₂.1, remember_logged.mono (h₁.grows.trans h₂.grows)⟩
  | .recordNil _ _ h₁ h₂, hc =>
    have r₁ := h₁.logged hc.remember
    have r₂ := h₂.logged r₁.1
    ⟨r₂.1, remember_logged.mono (h₁.grows.trans h₂.grows)⟩
  | .record _ _ _ h₁ h₂ h₃, hc =>
    have r₁ := h₁.logged hc.remember
    have r₂ := h₂.logged r₁.1
    have r₃ := h₃.logged r₂.1
    ⟨r₃.1, remember_logged.mono (h₁.grows.trans (h₂.grows.trans h₃.grows))⟩
  | .varL _ _ h, hc =>
    have r := h.logged hc.rememberUpper
    ⟨r.1, (remember_logged.mono Grows.addUpper).mono h.grows⟩
  | .varR _ _ h, hc =>
    have r := h.logged hc.remember.addLower
    ⟨r.1, (remember_logged.mono Grows.addLower).mono h.grows⟩
  | .recordSig _ _ _ _ _ h, hc =>
    have r := h.logged hc.remember
    ⟨r.1, remember_logged.mono h.grows⟩
  | .sigL _ _ h, hc =>
    have r := h.logged hc.remember
    ⟨r.1, remember_logged.mono h.grows⟩

theorem ConstrainEach.logged :
    ConstrainEach s ps s' → CacheInLog s → CacheInLog s' ∧ ∀ p ∈ ps, Logged s' p.1 p.2
  | .nil, hc => ⟨hc, fun _ h => nomatch h⟩
  | .cons h₁ h₂, hc =>
    have r₁ := h₁.logged hc
    have r₂ := h₂.logged r₁.1
    ⟨r₂.1, fun p hp => by
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact r₁.2.mono h₂.grows
      · exact r₂.2 p hp⟩

theorem ConstrainField.logged :
    ConstrainField s a b s' → CacheInLog s → CacheInLog s' ∧ FieldR (Logged s') a b
  | .toAbs, hc => ⟨hc, .toAbs⟩
  | .misMis, hc => ⟨hc, .misMis⟩
  | .misOpt, hc => ⟨hc, .misOpt⟩
  | .optOpt h₀ h, hc => have r := h.logged hc; ⟨r.1, .optOpt h₀ r.2⟩
  | .preOpt h₀ h, hc => have r := h.logged hc; ⟨r.1, .preOpt h₀ r.2⟩
  | .pre h₀ h₁ h, hc => have r := h.logged hc; ⟨r.1, .pre h₀ h₁ r.2⟩

theorem FieldsEach.logged :
    FieldsEach s ps s' → CacheInLog s → CacheInLog s' ∧ ∀ p ∈ ps, FieldR (Logged s') p.1 p.2
  | .nil, hc => ⟨hc, fun _ h => nomatch h⟩
  | .cons h₁ h₂, hc =>
    have r₁ := h₁.logged hc
    have r₂ := h₂.logged r₁.1
    ⟨r₂.1, fun p hp => by
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact r₁.2.mono fun _ _ => Logged.mono h₂.grows
      · exact r₂.2 p hp⟩

theorem Expand.logged :
    Expand s t ms t' s' → CacheInLog s → CacheInLog s' ∧ ExpandG s'.bounds (Logged s') t ms t'
  | .none, hc => ⟨hc, .none⟩
  | .abs hm h, hc => have r := h.logged hc; ⟨r.1, .abs hm r.2⟩
  | .nil hm h, hc => have r := h.logged hc; ⟨r.1, .nil hm r.2⟩
  | .allAbsent (s := s₀) (v := v) _ hp h, hc =>
    have r := h.logged hc; ⟨r.1, .varAbsent (s₀.kind v) r.2 hp⟩
  | .memo (s := s₀) (v := v) hm hp h₁ _ h₂, hc =>
    have r₁ := h₁.logged hc
    have r₂ := h₂.logged r₁.1
    ⟨r₂.1, .var (s₀.kind v) hm (fun p q => (r₁.2 p q).mono fun _ _ => Logged.mono h₂.grows) hp
      (h₂.installs r₁.1 (fun h => nomatch h) (fun _ h => nomatch h)) (SFields.Rel.refl_logged _)⟩
  | .fresh (s := s₀) (v := v) hm hp h₁ _ _ h₂, hc =>
    have r₁ := h₁.logged hc
    have r₂ := h₂.logged r₁.1
    ⟨r₂.1, .var (s₀.kind v) hm
      (fun p q => (r₁.2 p q).mono fun _ _ => Logged.mono (Grows.expand.trans h₂.grows)) hp
      (h₂.installs r₁.1 (fun h => nomatch h) (fun _ h => nomatch h)) (SFields.Rel.refl_logged _)⟩
end

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

mutual
theorem Constrain.just : Constrain s a b s' → CacheInLog s → JustExcept s P → JustExcept s' P
  | .cached _, _, h => h
  | .refl, _, h => h
  | .arrow _ h₁ h₂, hc, h =>
    have j₂ := h₂.just (h₁.logged hc.remember).1 (h₁.just hc.remember h.remember)
    j₂.close (.arrow ((h₁.logged hc.remember).2.mono h₂.grows) (h₂.logged (h₁.logged hc.remember).1).2)
  | .absR _, _, h => h.remember.close .absR
  | .absRecord _ h₁ h₂, hc, h =>
    have r₁ := h₁.logged hc.remember
    have j₂ := h₂.just r₁.1 (h₁.just hc.remember h.remember)
    j₂.close (.absRecord (fun p hp => (r₁.2 p hp).mono fun _ _ => Logged.mono h₂.grows)
      (h₂.logged r₁.1).2)
  | .nilRecord _ h₁ h₂, hc, h =>
    have r₁ := h₁.logged hc.remember
    have j₂ := h₂.just r₁.1 (h₁.just hc.remember h.remember)
    j₂.close (.nilRecord (fun p hp => (r₁.2 p hp).mono fun _ _ => Logged.mono h₂.grows)
      (h₂.logged r₁.1).2)
  | .recordNil _ e₀ h₁ h₂, hc, h =>
    have r₁ := h₁.logged hc.remember
    have j₂ := h₂.just r₁.1 (h₁.just hc.remember h.remember)
    j₂.close (.recordNil e₀ (fun p hp => (r₁.2 p hp).mono fun _ _ => Logged.mono h₂.grows)
      (h₂.logged r₁.1).2)
  | .record _ e₀ e₁ h₁ h₂ h₃, hc, h =>
    have r₁ := h₁.logged hc.remember
    have r₂ := h₂.logged r₁.1
    have j₃ := h₃.just r₂.1 (h₂.just r₁.1 (h₁.just hc.remember h.remember))
    j₃.close (.record e₀ e₁
      (fun p hp => (r₁.2 p hp).mono fun _ _ => Logged.mono (h₂.grows.trans h₃.grows))
      (r₂.2.mono h₃.grows.upper fun _ _ => Logged.mono h₃.grows) (h₃.logged r₂.1).2)
  | .varL (s := s₀) (v := v) (b := b) _ _ h, hc, hj =>
    have j := h.just hc.rememberUpper
      ((hj.remember (a := .var v) (b := b)).grow .addUpper fun _ hp => hp)
    j.close (.varL (h.grows.upper _ _ mem_upper_addUpper))
  | .varR (s := s₀) (v := v) (a := a) _ _ h, hc, hj =>
    have j := h.just hc.remember.addLower
      ((hj.remember (a := a) (b := .var v)).grow .addLower fun _ hp => hp)
    j.close (.varR (h.grows.lower _ _ mem_lower_addLower))
  | .recordSig (k := k) _ _ _ _ hk h, hc, hj =>
    (h.just hc.remember hj.remember).close
      (.recordSig (List.mem_map.mpr ⟨k, hk, rfl⟩) (h.logged hc.remember).2)
  | .sigL _ hb h, hc, hj =>
    have r := h.logged hc.remember
    (h.just hc.remember hj.remember).close
      (.sigL hb fun d hd => r.2 (d, _) (List.mem_map.mpr ⟨d, hd, rfl⟩))

theorem ConstrainEach.just :
    ConstrainEach s ps s' → CacheInLog s → JustExcept s P → JustExcept s' P
  | .nil, _, h => h
  | .cons h₁ h₂, hc, h => h₂.just (h₁.logged hc).1 (h₁.just hc h)

theorem ConstrainField.just :
    ConstrainField s a b s' → CacheInLog s → JustExcept s P → JustExcept s' P
  | .toAbs, _, h | .misMis, _, h | .misOpt, _, h => h
  | .optOpt _ h, hc, hj | .preOpt _ h, hc, hj | .pre _ _ h, hc, hj => h.just hc hj

theorem FieldsEach.just :
    FieldsEach s ps s' → CacheInLog s → JustExcept s P → JustExcept s' P
  | .nil, _, h => h
  | .cons h₁ h₂, hc, h => h₂.just (h₁.logged hc).1 (h₁.just hc h)

theorem Expand.just : Expand s t ms t' s' → CacheInLog s → JustExcept s P → JustExcept s' P
  | .none, _, h => h
  | .abs _ h, hc, hj | .nil _ h, hc, hj => h.just hc hj
  | .allAbsent _ _ h, hc, hj => h.just hc hj
  | .memo _ _ h₁ _ h₂, hc, hj => h₂.just (h₁.logged hc).1 (h₁.just hc hj)
  | .fresh _ _ h₁ _ _ h₂, hc, hj =>
    h₂.just (h₁.logged hc).1 ((h₁.just hc hj).grow .expand fun _ hp => hp)
end

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

mutual
theorem Constrain.consist :
    Constrain s a b s' → CacheInLog s → ConsExcept s P → ConsExcept s' P
  | .cached _, _, h => h
  | .refl, _, h => h
  | .arrow _ h₁ h₂, hc, h =>
    h₂.consist (h₁.logged hc.remember).1 (h₁.consist hc.remember h.remember)
  | .absR _, _, h => h.remember
  | .absRecord _ h₁ h₂, hc, h | .nilRecord _ h₁ h₂, hc, h | .recordNil _ _ h₁ h₂, hc, h =>
    h₂.consist (h₁.logged hc.remember).1 (h₁.consist hc.remember h.remember)
  | .record _ _ _ h₁ h₂ h₃, hc, h =>
    have r₁ := h₁.logged hc.remember
    h₃.consist (h₂.logged r₁.1).1 (h₂.consist r₁.1 (h₁.consist hc.remember h.remember))
  | .varL _ _ h, hc, hs => h.consist hc.rememberUpper hs.remember.addUpper
  | .varR _ _ h, hc, hs => h.consist hc.remember.addLower hs.remember.addLower
  | .recordSig _ _ _ _ _ h, hc, hs => h.consist hc.remember hs.remember
  | .sigL _ _ h, hc, hs =>
    h.consist hc.remember (hs.remember.weaken fun _ hp => List.mem_append_right _ hp)

/-- Propagation: processing the pending pairs `ps` discharges them. -/
theorem ConstrainEach.consist :
    ConstrainEach s ps s' → CacheInLog s → ConsExcept s (ps ++ P) → ConsExcept s' P
  | .nil, _, h => h
  | .cons (a := a) (b := b) (rest := rest) h₁ h₂, hc, h =>
    have r₁ := h₁.logged hc
    have c₁ := h₁.consist hc h
    h₂.consist r₁.1 fun v l u hl hu => by
      rcases c₁ v l u hl hu with hlog | hp
      · exact .inl hlog
      · simp only [List.cons_append, List.mem_cons] at hp
        rcases hp with hp | hp
        · cases hp; exact .inl r₁.2
        · exact .inr hp

theorem ConstrainField.consist :
    ConstrainField s a b s' → CacheInLog s → ConsExcept s P → ConsExcept s' P
  | .toAbs, _, h | .misMis, _, h | .misOpt, _, h => h
  | .optOpt _ h, hc, hs | .preOpt _ h, hc, hs | .pre _ _ h, hc, hs => h.consist hc hs

theorem FieldsEach.consist :
    FieldsEach s ps s' → CacheInLog s → ConsExcept s P → ConsExcept s' P
  | .nil, _, h => h
  | .cons h₁ h₂, hc, h => h₂.consist (h₁.logged hc).1 (h₁.consist hc h)

theorem Expand.consist :
    Expand s t ms t' s' → CacheInLog s → ConsExcept s P → ConsExcept s' P
  | .none, _, h => h
  | .abs _ h, hc, hs | .nil _ h, hc, hs => h.consist hc hs
  | .allAbsent _ _ h, hc, hs => h.consist hc hs
  | .memo _ _ h₁ _ h₂, hc, hs => h₂.consist (h₁.logged hc).1 (h₁.consist hc hs)
  | .fresh _ _ h₁ _ _ h₂, hc, hs => h₂.consist (h₁.logged hc).1 (h₁.consist hc hs).expand
end

/-! ## Lemma 2, at the level of the bound graph -/

/-- The invariant of states the algorithm reaches between calls. -/
structure Inv (s : State) : Prop where
  just : Justified s
  cons : Consistent s

/-- **Soundness of constraining** (graph form of the paper's Lemma 2): a
successful top-level `constrain` call preserves the invariant, and the
constraint it was asked to solve is accepted. -/
theorem ConstrainTop.sound (h : ConstrainTop s a b s') (hi : Inv s) :
    Inv s' ∧ Logged s' a b := by
  obtain ⟨s₁, hc, rfl⟩ := h
  have hc₀ : CacheInLog { s with cache := [] } := ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  exact ⟨⟨hc.just hc₀ hi.just, hc.consist hc₀ hi.cons⟩, (hc.logged hc₀).2⟩

theorem Inv.fresh (h : Inv s) : Inv s.fresh := ⟨h.just, h.cons⟩

mutual
/-- Typing a term preserves the invariant. -/
theorem TypeTerm.inv : TypeTerm Γ s t st s' → Inv s → Inv s'
  | .lit, h => h
  | .var _, h => h
  | .lam _ h, hi => h.inv hi.fresh
  | .app _ h₁ h₂ hc, hi => (hc.sound (h₂.inv (h₁.inv hi.fresh))).1
  | .rcd h, hi => h.inv hi
  | .sel _ h hc, hi => (hc.sound (h.inv hi.fresh)).1
  | .ite _ hc h₁ ha h₂ hb h₃, hi =>
    (h₃.sound (hb.inv (h₂.sound (ha.inv (h₁.sound (hc.inv hi.fresh)).1)).1)).1
  | .selOr _ h hc hd hc', hi => (hc'.sound (hd.inv (hc.sound (h.inv hi.fresh)).1)).1
  | .ext _ h₁ h₂ _ hc, hi => (hc.sound (h₂.inv (h₁.inv hi)).fresh).1
  | .extNil h, hi => h.inv hi
  | .letIn h₁ h₂, hi => h₂.inv (h₁.inv hi)
  | .letRec _ _ h₁ hc h₂, hi => h₂.inv (hc.sound (h₁.inv hi.fresh)).1
  | .fn _ hp h, hi => h.inv (hp.inv hi)

theorem TypeFields.inv : TypeFields Γ s fs F s' → Inv s → Inv s'
  | .nil, h => h
  | .cons h₁ h₂, hi => h₂.inv (h₁.inv hi)

theorem TypeParams.inv : TypeParams Γ s ps P Γ' s' → Inv s → Inv s'
  | .nil, h => h
  | .req _ h, hi => h.inv hi.fresh
  | .dflt _ hd hc h, hi => h.inv (hc.sound (hd.inv hi.fresh)).1
end

theorem Inv.init {K : Nat → List String} : Inv (State.initK K) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h _ => nomatch h)⟩

/-- Every state reached by typing a term from scratch satisfies the
invariant. -/
theorem TypeTerm.inv_init {K : Nat → List String} (h : TypeTerm Γ (State.initK K) t st s') : Inv s' := h.inv .init

end BoltCore.Alg
