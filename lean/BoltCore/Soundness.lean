import BoltCore.Instantiate

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

/-! ## Growth of the state -/

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
  | .varL _ _ _ h => (Grows.remember.trans .addUpper).trans h.grows
  | .varR _ _ _ h => (Grows.remember.trans .addLower).trans h.grows
  | .extLHit _ _ _ hx _ => Grows.remember.trans hx.grows
  | .extLNew _ _ _ hx _ h =>
    (Grows.remember.trans hx.grows).trans ((Grows.remember.trans .addUpper).trans h.grows)
  | .extRHit _ _ _ hx _ => Grows.remember.trans hx.grows
  | .extRNew _ _ _ hx _ h =>
    (Grows.remember.trans hx.grows).trans ((Grows.remember.trans .addLower).trans h.grows)
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
  | .fresh _ _ h₁ _ _ _ h₂ => h₁.grows.trans (Grows.expand.trans h₂.grows)
end

/-! ## Every accepted constraint is logged -/

/-- What a cached `v ≤ b`, with `b` not a variable, has installed: `b` as
an upper bound of `v` if its level is low enough (`varL`); otherwise its
extrusion to the level of `v`. Of the extrusion we keep what a row
expansion needs: if `b` is a record over a row variable of low level, a
record over the same variable whose fields are below those of `b`. -/
structure Installed (s : State) (v : Nat) (b : SType) : Prop where
  low : b.level s.level ≤ s.level v → b ∈ (s.bounds v).upper
  row : ∀ P r, b = .record P (.var r) → s.level r ≤ s.level v →
    ∃ P', .record P' (.var r) ∈ (s.bounds v).upper ∧ SFields.Rel (FieldR (Logged s)) P' P

theorem Installed.of_mem {s : State} {v : Nat} {b : SType} (h : b ∈ (s.bounds v).upper) :
    Installed s v b :=
  ⟨fun _ => h, fun P _ e _ => ⟨P, e ▸ h, SFields.Rel.refl_logged P⟩⟩

theorem Installed.mono {s s' : State} {v : Nat} {b : SType} (g : Grows s s')
    (h : Installed s v b) : Installed s' v b := by
  refine ⟨fun hl => ?_, fun P r e hr => ?_⟩
  · rw [g.level] at hl; exact g.upper _ _ (h.low hl)
  · rw [g.level] at hr
    obtain ⟨P', hm, hrel⟩ := h.row P r e hr
    exact ⟨P', g.upper _ _ hm, hrel.mono fun _ _ f => f.mono fun _ _ => Logged.mono g⟩

/-- Cache hits are uses of logged constraints, and a cached constraint
with a variable on one side and a non-variable on the other has installed
a bound: on the left, see `Installed`; on the right, the left side itself
if its level is low enough (`varR`). An expansion variable has the level
of its row variable. -/
structure CacheInLog (s : State) : Prop where
  log : ∀ p, p ∈ s.cache → p ∈ s.log
  inst : ∀ v b, (.var v, b) ∈ s.cache → b ≠ .abs → (∀ w, b ≠ .var w) → Installed s v b
  instR : ∀ a v, (a, .var v) ∈ s.cache → (∀ w, a ≠ .var w) → a.level s.level ≤ s.level v →
    a ∈ (s.bounds v).lower
  exps : ExpLevel s

/-- What a newly cached pair has to have installed. -/
def NewOK (s : State) (p : SType × SType) : Prop :=
  (∀ v b, p = (.var v, b) → b ≠ .abs → (∀ w, b ≠ .var w) → Installed s v b) ∧
  (∀ a v, p = (a, .var v) → (∀ w, a ≠ .var w) → a.level s.level ≤ s.level v →
    a ∈ (s.bounds v).lower)

/-- The invariant in a later state with the same expansions, whose new
cache entries are logged and have installed their bounds. -/
theorem CacheInLog.ofCache {s s' : State} (h : CacheInLog s) (g : Grows s s')
    (he : s'.exps = s.exps)
    (hnew : ∀ p ∈ s'.cache, p ∈ s.cache ∨ (p ∈ s'.log ∧ NewOK s' p)) : CacheInLog s' := by
  refine ⟨fun p hp => ?_, fun v b hm hb hnv => ?_, fun a v hm hnv hl => ?_, fun v L r hm => ?_⟩
  · rcases hnew p hp with hp | hp
    · exact g.log _ (h.log p hp)
    · exact hp.1
  · rcases hnew _ hm with hm | hm
    · exact (h.inst v b hm hb hnv).mono g
    · exact hm.2.1 v b rfl hb hnv
  · rcases hnew _ hm with hm | hm
    · rw [g.level] at hl; exact g.lower _ _ (h.instR a v hm hnv hl)
    · exact hm.2.2 a v rfl hnv hl
  · rw [g.level]; exact h.exps v L r (he ▸ hm)

/-- Remembering a constraint between non-variables, or below `Abs`. -/
theorem CacheInLog.remember (h : CacheInLog s)
    (h' : ((∀ w, a ≠ .var w) ∧ (∀ w, b ≠ .var w)) ∨ b = .abs := by
      first
        | exact .inr rfl
        | exact .inl ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩) :
    CacheInLog (s.remember a b) := by
  refine h.ofCache .remember rfl fun p hp => ?_
  rcases List.mem_cons.mp hp with rfl | hp
  · refine .inr ⟨List.mem_cons_self .., fun v x e hx hxv => ?_, fun x v e hxv _ => ?_⟩
    · cases e
      rcases h' with h' | h'
      · exact absurd rfl (h'.1 v)
      · exact absurd h' hx
    · cases e
      rcases h' with h' | h'
      · exact absurd rfl (h'.2 v)
      · exact nomatch h'
  · exact .inl hp

/-- Caching `v ≤ b` and installing the bound together. -/
theorem CacheInLog.rememberUpper (h : CacheInLog s) :
    CacheInLog ((s.remember (.var v) b).addUpper v b) := by
  refine h.ofCache (Grows.remember.trans .addUpper) rfl fun p hp => ?_
  rcases List.mem_cons.mp hp with rfl | hp
  · refine .inr ⟨List.mem_cons_self .., fun w x e _ _ => ?_, fun x w e hxv _ => ?_⟩
    · cases e; exact .of_mem mem_upper_addUpper
    · cases e; exact absurd rfl (hxv v)
  · exact .inl hp

/-- Caching `a ≤ v` and installing the bound together. -/
theorem CacheInLog.rememberLower (h : CacheInLog s) :
    CacheInLog ((s.remember a (.var v)).addLower v a) := by
  refine h.ofCache (Grows.remember.trans .addLower) rfl fun p hp => ?_
  rcases List.mem_cons.mp hp with rfl | hp
  · refine .inr ⟨List.mem_cons_self .., fun w x e _ hxv => ?_, fun x w e _ _ => ?_⟩
    · cases e; exact absurd rfl (hxv v)
    · cases e; exact mem_lower_addLower
  · exact .inl hp

/-- Adding an expansion variable of the right level. -/
theorem CacheInLog.addExp {s : State} {v r n : Nat} {L : List String} (h : CacheInLog s)
    (hl : s.level r = s.level v) :
    CacheInLog { s with next := n, exps := ((v, L), r) :: s.exps } :=
  ⟨h.log, fun v' b hm hb hnv => ⟨(h.inst v' b hm hb hnv).low, (h.inst v' b hm hb hnv).row⟩,
    h.instR, fun v' L' r' hm => by
    rcases List.mem_cons.mp hm with e | hm
    · cases e; exact hl
    · exact h.exps v' L' r' hm⟩

theorem remember_logged {s : State} {a b : SType} : Logged (s.remember a b) a b := .inr (List.mem_cons_self ..)

/-- A successful constraint is accepted, given only that cache hits are
logged. -/
theorem Constrain.accepts (h : Constrain s a b s') (hc : ∀ p ∈ s.cache, p ∈ s.log) :
    Logged s' a b := by
  cases h with
  | cached hm => exact .inr (hc _ hm)
  | refl => exact .inl rfl
  | arrow _ h₁ h₂ => exact remember_logged.mono (h₁.grows.trans h₂.grows)
  | absR _ => exact remember_logged
  | absRecord _ h₁ h₂ => exact remember_logged.mono (h₁.grows.trans h₂.grows)
  | nilRecord _ h₁ h₂ => exact remember_logged.mono (h₁.grows.trans h₂.grows)
  | recordNil _ _ h₁ h₂ => exact remember_logged.mono (h₁.grows.trans h₂.grows)
  | record _ _ _ h₁ h₂ h₃ =>
    exact remember_logged.mono (h₁.grows.trans (h₂.grows.trans h₃.grows))
  | varL _ _ _ h => exact (remember_logged.mono Grows.addUpper).mono h.grows
  | varR _ _ _ h => exact (remember_logged.mono Grows.addLower).mono h.grows
  | extLHit _ _ _ hx _ => exact remember_logged.mono hx.grows
  | extLNew _ _ _ hx _ h =>
    exact remember_logged.mono (hx.grows.trans ((Grows.remember.trans .addUpper).trans h.grows))
  | extRHit _ _ _ hx _ => exact remember_logged.mono hx.grows
  | extRNew _ _ _ hx _ h =>
    exact remember_logged.mono (hx.grows.trans ((Grows.remember.trans .addLower).trans h.grows))
  | recordSig _ _ _ _ _ h => exact remember_logged.mono h.grows
  | sigL _ _ h => exact remember_logged.mono h.grows

/-! ### Extrusion in a constraint -/

/-- An extruded record over a row variable of low level is a record over
the same variable, with fields below. -/
theorem Extrude.record_low {P : SFields} {r : Nat}
    (h : Extrude s c false lvl (.record P (.var r)) b' s' c') (hr : s.level r ≤ lvl) :
    ∃ P', b' = .record P' (.var r) ∧ SFields.Rel (FieldR (Logged s')) P' P := by
  cases h with
  | low _ => exact ⟨P, rfl, SFields.Rel.refl_logged P⟩
  | record _ hf ht =>
    cases ht with
    | low _ => exact ⟨_, rfl, hf.rel.rel_mono .logAll⟩
    | varCopied hl _ =>
      rw [hf.same.level] at hl; exact absurd hl (Nat.not_lt.mpr hr)
    | varNeg hl _ _ _ _ =>
      rw [hf.same.level] at hl; exact absurd hl (Nat.not_lt.mpr hr)

theorem Extrude.nonvar (h : Extrude s c pol lvl t t' s' c') (hnv : ∀ w, t ≠ .var w) :
    ∀ w, t' ≠ .var w := by
  rcases h.con with rfl | hc
  · exact hnv
  · exact hc.nonvar hnv

/-- A type of positive level is not `Abs`. -/
theorem SType.ne_abs_of_level {L : Nat → Nat} {t : SType} {n : Nat} (h : n < t.level L) :
    t ≠ .abs := fun e => by subst e; simp [SType.level] at h

/-- After extruding `b` to the level of `v`, the copy as a bound of `v`
is what caching `v ≤ b` has to install. -/
theorem Installed.ofExt {s₀ s₁ s₂ : State} {v : Nat} {b b' : SType} {c : Copies}
    (hx : Extrude s₀ [] false (s₀.level v) b b' s₁ c) (hlv : s₀.level v < b.level s₀.level)
    (g : Grows s₁ s₂) (hin : b' ∈ (s₂.bounds v).upper) : Installed s₂ v b := by
  have gl : s₂.level = s₀.level := g.level.trans hx.same.level
  refine ⟨fun hl => ?_, fun P r e hr => ?_⟩
  · rw [gl] at hl; exact absurd hl (Nat.not_le.mpr hlv)
  · subst e
    rw [gl] at hr
    obtain ⟨P', rfl, hrel⟩ := hx.record_low hr
    exact ⟨P', hin, hrel.mono fun _ _ f => f.mono fun _ _ => Logged.mono g⟩

/-- The copy of the right side is a bound already, when the constraint
against it is cached. -/
theorem extL_hit {s s₁ : State} {v : Nat} {b b' : SType} {c : Copies} (hc : CacheInLog s)
    (hnv : ∀ w, b ≠ .var w) (hlv : s.level v < b.level s.level)
    (hx : Extrude (s.remember (.var v) b) [] false (s.level v) b b' s₁ c)
    (hm : (.var v, b') ∈ s₁.cache) : b' ∈ (s₁.bounds v).upper := by
  have hl : b'.level s.level ≤ s.level v := (hx.level_le rfl CopiesLow.nil).1
  have hne : b' ≠ b := fun e => absurd (e ▸ hl) (Nat.not_le.mpr hlv)
  rw [hx.same.cache] at hm
  rcases List.mem_cons.mp hm with e | hm
  · exact absurd (Prod.mk.inj e).2 hne
  · exact (Grows.remember.trans hx.grows).upper _ _
      ((hc.inst v b' hm (hx.ne_abs (SType.ne_abs_of_level hlv)) (hx.nonvar hnv)).low hl)

/-- The same on the other side. -/
theorem extR_hit {s s₁ : State} {v : Nat} {a a' : SType} {c : Copies} (hc : CacheInLog s)
    (hnv : ∀ w, a ≠ .var w) (hlv : s.level v < a.level s.level)
    (hx : Extrude (s.remember a (.var v)) [] true (s.level v) a a' s₁ c)
    (hm : (a', .var v) ∈ s₁.cache) : a' ∈ (s₁.bounds v).lower := by
  have hl : a'.level s.level ≤ s.level v := (hx.level_le rfl CopiesLow.nil).1
  have hne : a' ≠ a := fun e => absurd (e ▸ hl) (Nat.not_le.mpr hlv)
  rw [hx.same.cache] at hm
  rcases List.mem_cons.mp hm with e | hm
  · exact absurd (Prod.mk.inj e).1 hne
  · exact (Grows.remember.trans hx.grows).lower _ _ (hc.instR a' v hm (hx.nonvar hnv) hl)

/-- The cache after extruding the right side of `v ≤ b`, given that the
copy is a bound of `v`. -/
theorem CacheInLog.extL {s s₁ : State} {v : Nat} {b b' : SType} {c : Copies} (hc : CacheInLog s)
    (hlv : s.level v < b.level s.level)
    (hx : Extrude (s.remember (.var v) b) [] false (s.level v) b b' s₁ c)
    (hin : b' ∈ (s₁.bounds v).upper) : CacheInLog s₁ := by
  refine hc.ofCache (Grows.remember.trans hx.grows) hx.same.exps fun p hp => ?_
  rw [hx.same.cache] at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine .inr ⟨hx.grows.log _ (List.mem_cons_self ..), fun w x e _ _ => ?_,
      fun x w e hxv _ => ?_⟩
    · cases e; exact .ofExt hx hlv .refl hin
    · cases e; exact absurd rfl (hxv v)
  · exact .inl hp

/-- The cache after extruding the right side of `v ≤ b` and installing
the copy. -/
theorem CacheInLog.extLNew {s s₁ : State} {v : Nat} {b b' : SType} {c : Copies}
    (hc : CacheInLog s) (hlv : s.level v < b.level s.level)
    (hx : Extrude (s.remember (.var v) b) [] false (s.level v) b b' s₁ c) :
    CacheInLog ((s₁.remember (.var v) b').addUpper v b') := by
  have g := Grows.addUpper (s := s₁.remember (.var v) b') (v := v) (t := b')
  refine hc.ofCache ((Grows.remember.trans hx.grows).trans (Grows.remember.trans g))
    hx.same.exps fun p hp => ?_
  rcases List.mem_cons.mp hp with rfl | hp
  · refine .inr ⟨List.mem_cons_self .., fun w x e _ _ => ?_, fun x w e hxv _ => ?_⟩
    · cases e; exact .of_mem mem_upper_addUpper
    · cases e; exact absurd rfl (hxv v)
  have hp' : p ∈ s₁.cache := hp
  rw [hx.same.cache] at hp'
  rcases List.mem_cons.mp hp' with rfl | hp'
  · refine .inr ⟨List.mem_cons_of_mem _ (hx.grows.log _ (List.mem_cons_self ..)),
      fun w x e _ _ => ?_, fun x w e hxv _ => ?_⟩
    · cases e; exact .ofExt hx hlv (Grows.remember.trans g) mem_upper_addUpper
    · cases e; exact absurd rfl (hxv v)
  · exact .inl hp'

/-- The cache after extruding the left side of `a ≤ v`. -/
theorem CacheInLog.extR {s s₁ : State} {v : Nat} {a a' : SType} {c : Copies} (hc : CacheInLog s)
    (hlv : s.level v < a.level s.level)
    (hx : Extrude (s.remember a (.var v)) [] true (s.level v) a a' s₁ c) : CacheInLog s₁ := by
  refine hc.ofCache (Grows.remember.trans hx.grows) hx.same.exps fun p hp => ?_
  rw [hx.same.cache] at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine .inr ⟨hx.grows.log _ (List.mem_cons_self ..), fun w x e _ hxv => ?_,
      fun x w e _ hl => ?_⟩
    · cases e; exact absurd rfl (hxv v)
    · cases e
      rw [hx.same.level] at hl
      exact absurd hl (Nat.not_le.mpr hlv)
  · exact .inl hp

/-- The cache after extruding the left side of `a ≤ v` and installing the
copy. -/
theorem CacheInLog.extRNew {s s₁ : State} {v : Nat} {a a' : SType} {c : Copies}
    (hc : CacheInLog s) (hlv : s.level v < a.level s.level)
    (hx : Extrude (s.remember a (.var v)) [] true (s.level v) a a' s₁ c) :
    CacheInLog ((s₁.remember a' (.var v)).addLower v a') := by
  have h₁ := hc.extR hlv hx
  refine h₁.ofCache (Grows.remember.trans .addLower) rfl fun p hp => ?_
  rcases List.mem_cons.mp hp with rfl | hp
  · refine .inr ⟨List.mem_cons_self .., fun w x e _ hxv => ?_, fun x w e _ _ => ?_⟩
    · cases e; exact absurd rfl (hxv v)
    · cases e; exact mem_lower_addLower
  · exact .inl hp

/-- Constraining a variable below a non-variable installs a bound. -/
theorem Constrain.installs (h : Constrain s (.var v) b s') (hc : CacheInLog s) (hb : b ≠ .abs)
    (hnv : ∀ w, b ≠ .var w) : Installed s' v b := by
  cases h with
  | cached hm => exact hc.inst v b hm hb hnv
  | refl => exact absurd rfl (hnv v)
  | absR => exact absurd rfl hb
  | varL _ _ _ h' => exact .of_mem (h'.grows.upper _ _ mem_upper_addUpper)
  | varR _ _ _ _ => exact absurd rfl (hnv _)
  | extLHit _ _ hlv hx hm => exact .ofExt hx hlv .refl (extL_hit hc hnv hlv hx hm)
  | extLNew _ _ hlv hx _ h' =>
    exact .ofExt hx hlv ((Grows.remember.trans .addUpper).trans h'.grows)
      (h'.grows.upper _ _ mem_upper_addUpper)
  | extRHit _ hnv' _ _ _ => exact absurd rfl (hnv' v)
  | extRNew _ hnv' _ _ _ _ => exact absurd rfl (hnv' v)

mutual
theorem Constrain.logged : Constrain s a b s' → CacheInLog s → CacheInLog s' ∧ Logged s' a b
  | .cached hm, hc => ⟨hc, .inr (hc.log _ hm)⟩
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
  | .varL _ _ _ h, hc =>
    have r := h.logged hc.rememberUpper
    ⟨r.1, (remember_logged.mono Grows.addUpper).mono h.grows⟩
  | .varR _ _ _ h, hc =>
    have r := h.logged hc.rememberLower
    ⟨r.1, (remember_logged.mono Grows.addLower).mono h.grows⟩
  | .extLHit _ hnv hlv hx hm, hc =>
    ⟨hc.extL hlv hx (extL_hit hc hnv hlv hx hm), remember_logged.mono hx.grows⟩
  | .extLNew _ _ hlv hx _ h, hc =>
    have r := h.logged (hc.extLNew hlv hx)
    ⟨r.1, remember_logged.mono (hx.grows.trans ((Grows.remember.trans .addUpper).trans h.grows))⟩
  | .extRHit _ _ hlv hx _, hc => ⟨hc.extR hlv hx, remember_logged.mono hx.grows⟩
  | .extRNew _ _ hlv hx _ h, hc =>
    have r := h.logged (hc.extRNew hlv hx)
    ⟨r.1, remember_logged.mono (hx.grows.trans ((Grows.remember.trans .addLower).trans h.grows))⟩
  | .recordSig _ _ _ _ _ h, hc =>
    have r := h.logged hc.remember
    ⟨r.1, remember_logged.mono h.grows⟩
  | .sigL (b := b) _ hb h, hc =>
    have r := h.logged (hc.remember (.inl ⟨(fun _ h => nomatch h), hb.nonvar⟩))
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
  | .memo (s := s₀) (v := v) hm hp h₁ hl h₂, hc => by
    have r₁ := h₁.logged hc
    have r₂ := h₂.logged r₁.1
    have hi := h₂.installs r₁.1 (fun h => nomatch h) (fun _ h => nomatch h)
    obtain ⟨P', hu, hrel⟩ := hi.row _ _ rfl
      (by rw [h₂.grows.level]; exact Nat.le_of_eq (r₁.1.exps _ _ _ (lookup_mem hl)))
    exact ⟨r₂.1, .var (s₀.kind v) hm
      (fun p q => (r₁.2 p q).mono fun _ _ => Logged.mono h₂.grows) hp hu hrel⟩
  | .fresh (s := s₀) (v := v) hm hp h₁ _ _ hlv h₂, hc => by
    have r₁ := h₁.logged hc
    have hlv' := h₁.grows.level ▸ hlv
    have r₂ := h₂.logged (r₁.1.addExp hlv')
    have hi := h₂.installs (r₁.1.addExp hlv') (fun h => nomatch h) (fun _ h => nomatch h)
    obtain ⟨P', hu, hrel⟩ := hi.row _ _ rfl (by rw [h₂.grows.level]; exact Nat.le_of_eq hlv')
    exact ⟨r₂.1, .var (s₀.kind v) hm
      (fun p q => (r₁.2 p q).mono fun _ _ => Logged.mono (Grows.expand.trans h₂.grows)) hp
      hu hrel⟩
end

/-! ## Justification -/

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
      (fun _ _ _ l₀ l₁ => (r₁.2 _ (SFields.common_mem _ l₁ l₀)).mono
        fun _ _ => Logged.mono (h₂.grows.trans h₃.grows))
      (r₂.2.mono h₃.grows.upper fun _ _ => Logged.mono h₃.grows) (h₃.logged r₂.1).2)
  | .varL (s := s₀) (v := v) (b := b) _ _ _ h, hc, hj =>
    have j := h.just hc.rememberUpper
      ((hj.remember (a := .var v) (b := b)).grow .addUpper fun _ hp => hp)
    j.close (.varL (h.grows.upper _ _ mem_upper_addUpper))
  | .varR (s := s₀) (v := v) (a := a) _ _ _ h, hc, hj =>
    have j := h.just hc.rememberLower
      ((hj.remember (a := a) (b := .var v)).grow .addLower fun _ hp => hp)
    j.close (.varR (h.grows.lower _ _ mem_lower_addLower))
  -- `v ≤ b` holds through the copy `b'`: `v ≤ b'` as a bound, and `b' ≤ b`
  | .extLHit _ hnv hlv hx hm, hc, hj =>
    (hx.just .nil hj.remember).close
      (.viaL (extL_hit hc hnv hlv hx hm) (hx.nonvar hnv)
        (hx.ne_abs (SType.ne_abs_of_level hlv)) hnv hx.logged)
  | .extLNew (v := v) (b' := b') _ hnv hlv hx _ h, hc, hj =>
    have g := (Grows.remember (a := .var v) (b := b')).trans (.addUpper (v := v) (t := b'))
    have j := h.just (hc.extLNew hlv hx)
      (((hx.just .nil hj.remember).remember (a := .var v) (b := b')).grow .addUpper
        fun _ hp => hp)
    have hin := h.grows.upper _ _ (mem_upper_addUpper (v := v) (t := b'))
    (j.close (.varL hin)).close
      (.viaL hin (hx.nonvar hnv) (hx.ne_abs (SType.ne_abs_of_level hlv)) hnv
        (hx.logged.logged_mono (g.trans h.grows)))
  | .extRHit _ hnv hlv hx hm, hc, hj =>
    (hx.just .nil hj.remember).close
      (.viaR (extR_hit hc hnv hlv hx hm) (hx.nonvar hnv)
        (hx.ne_abs (SType.ne_abs_of_level hlv)) hnv (SType.ne_abs_of_level hlv) hx.logged)
  | .extRNew (v := v) (a' := a') _ hnv hlv hx _ h, hc, hj =>
    have g := (Grows.remember (a := a') (b := .var v)).trans (.addLower (v := v) (t := a'))
    have j := h.just (hc.extRNew hlv hx)
      (((hx.just .nil hj.remember).remember (a := a') (b := .var v)).grow .addLower
        fun _ hp => hp)
    have hin := h.grows.lower _ _ (mem_lower_addLower (v := v) (t := a'))
    (j.close (.varR hin)).close
      (.viaR hin (hx.nonvar hnv) (hx.ne_abs (SType.ne_abs_of_level hlv)) hnv
        (SType.ne_abs_of_level hlv) (hx.logged.logged_mono (g.trans h.grows)))
  | .recordSig (k := k) _ _ _ _ hk h, hc, hj =>
    (h.just hc.remember hj.remember).close
      (.recordSig (List.mem_map.mpr ⟨k, hk, rfl⟩) (h.logged hc.remember).2)
  | .sigL (s := s₀) (P := Q) (b := b) _ hb h, hc, hj =>
    have hc' : CacheInLog (s₀.remember (.sig Q) b) :=
      hc.remember (.inl ⟨(fun _ h => nomatch h), hb.nonvar⟩)
    have r := h.logged hc'
    (h.just hc' hj.remember).close
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
  | .fresh _ _ h₁ _ _ hlv h₂, hc, hj =>
    h₂.just ((h₁.logged hc).1.addExp (h₁.grows.level ▸ hlv))
      ((h₁.just hc hj).grow .expand fun _ hp => hp)
end

/-! ## Consistency

Extrusion needs the copies to be fresh (`Extrude.consist`), so consistency
is proved for a state in scope, on types in scope. -/

theorem Scope.addUpper {s : State} {v : Nat} {t : SType} (h : Scope s) (hv : v < s.next)
    (ht : t.In (· < s.next)) : Scope (s.addUpper v t) :=
  ⟨h.bounds.addUpper hv ht, h.exps, h.expLevel⟩

theorem Scope.addLower {s : State} {v : Nat} {t : SType} (h : Scope s) (hv : v < s.next)
    (ht : t.In (· < s.next)) : Scope (s.addLower v t) :=
  ⟨h.bounds.addLower hv ht, h.exps, h.expLevel⟩

/-- Allocating an expansion variable of the right level. -/
theorem Scope.addExp {s : State} {v : Nat} {L : List String} (h : Scope s) (hv : v < s.next)
    (hl : s.level s.next = s.level v) :
    Scope { s with next := s.next + 1, exps := ((v, L), s.next) :: s.exps } :=
  ⟨fun w b hb => ⟨Nat.lt_succ_of_lt (h.bounds w b hb).1,
      (h.bounds w b hb).2.mono fun _ hw => Nat.lt_succ_of_lt hw⟩,
    fun e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨Nat.lt_succ_of_lt hv, Nat.lt_succ_self _⟩
      · exact ⟨Nat.lt_succ_of_lt (h.exps e he).1, Nat.lt_succ_of_lt (h.exps e he).2⟩,
    fun v' L' r' hm => by
      rcases List.mem_cons.mp hm with e | hm
      · cases e; exact hl
      · exact h.expLevel v' L' r' hm⟩

mutual
theorem Constrain.consist : Constrain s a b s' → Scope s → a.In (· < s.next) →
    b.In (· < s.next) → CacheInLog s → ConsExcept s P → ConsExcept s' P
  | .cached _, _, _, _, _, h => h
  | .refl, _, _, _, _, h => h
  | .arrow _ h₁ h₂, hs, ha, hb, hc, h => by
    have ha' := SType.in_arrow.mp ha
    have hb' := SType.in_arrow.mp hb
    have n₁ := h₁.keeps.next
    exact h₂.consist (h₁.scope hs.remember hb'.1 ha'.1) (ha'.2.scope_mono n₁)
      (hb'.2.scope_mono n₁) (h₁.logged hc.remember).1
      (h₁.consist hs.remember hb'.1 ha'.1 hc.remember h.remember)
  | .absR _, _, _, _, _, h => h.remember
  | .absRecord _ h₁ h₂, hs, _, hb, hc, h => by
    have hb' := SType.in_record.mp hb
    exact h₂.consist (h₁.scope hs.remember hb'.1.absPairs) SType.in_abs
      (hb'.2.scope_mono h₁.keeps.next) (h₁.logged hc.remember).1
      (h₁.consist hs.remember hb'.1.absPairs hc.remember h.remember)
  | .nilRecord _ h₁ h₂, hs, _, hb, hc, h => by
    have hb' := SType.in_record.mp hb
    exact h₂.consist (h₁.scope hs.remember hb'.1.misPairs) SType.in_nil
      (hb'.2.scope_mono h₁.keeps.next) (h₁.logged hc.remember).1
      (h₁.consist hs.remember hb'.1.misPairs hc.remember h.remember)
  | .recordNil _ e₀ h₁ h₂, hs, ha, _, hc, h => by
    have hv := rowView_in _ ha
    rw [e₀] at hv
    exact h₂.consist (h₁.scope hs.remember hv.1.toMisPairs) (hv.2.scope_mono h₁.keeps.next)
      SType.in_nil (h₁.logged hc.remember).1
      (h₁.consist hs.remember hv.1.toMisPairs hc.remember h.remember)
  | .record _ e₀ e₁ h₁ h₂ h₃, hs, ha, hb, hc, h => by
    have v₀ := rowView_in _ ha
    have v₁ := rowView_in _ hb
    rw [e₀] at v₀
    rw [e₁] at v₁
    have n₁ := h₁.keeps.next
    have n₂ := Nat.le_trans n₁ h₂.keeps.next
    have hs₁ := h₁.scope hs.remember (v₀.1.common v₁.1)
    have r₁ := h₁.logged hc.remember
    have hs₂ := h₂.scope hs₁ (v₀.2.scope_mono n₁) (v₁.1.missing.scope_mono n₁)
    exact h₃.consist hs₂.1 (restRow_in (v₀.1.missing.scope_mono n₂) hs₂.2)
      (v₁.2.scope_mono n₂) (h₂.logged r₁.1).1
      (h₂.consist hs₁ (v₀.2.scope_mono n₁) (v₁.1.missing.scope_mono n₁) r₁.1
        (h₁.consist hs.remember (v₀.1.common v₁.1) hc.remember h.remember))
  | .varL (s := s₀) (v := v) (b := b) _ _ _ h', hs, ha, hb, hc, h => by
    have hv : v < s₀.next := (SType.in_var (X := (· < s₀.next))).mp ha
    exact h'.consist (Scope.addUpper (s := s₀.remember (.var v) b) hs.remember hv hb)
      (fun p hp => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
        exact ⟨(hs.bounds v l (.inr hl)).2, hb⟩)
      hc.rememberUpper h.remember.addUpper
  | .varR (s := s₀) (v := v) (a := a) _ _ _ h', hs, ha, hb, hc, h => by
    have hv : v < s₀.next := (SType.in_var (X := (· < s₀.next))).mp hb
    exact h'.consist (Scope.addLower (s := s₀.remember a (.var v)) hs.remember hv ha)
      (fun p hp => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
        exact ⟨ha, (hs.bounds v u (.inl hu)).2⟩)
      hc.rememberLower h.remember.addLower
  | .extLHit _ _ _ hx _, hs, _, hb, _, h =>
    hx.consist hs.remember.bounds hb (fun _ h => nomatch h) h.remember
  | .extLNew (s := s₀) (v := v) (b' := b') (s₁ := s₁) _ _ hlv hx _ h', hs, ha, hb, hc, h => by
    have hv : v < s₁.next :=
      Nat.lt_of_lt_of_le ((SType.in_var (X := (· < s₀.next))).mp ha) hx.same.next
    have sc := hx.scope hs.remember hb (fun _ h => nomatch h)
    have c₁ := hx.consist hs.remember.bounds hb (fun _ h => nomatch h) h.remember
    exact h'.consist (Scope.addUpper (s := s₁.remember (.var v) b') sc.1.remember hv sc.2)
      (fun p hp => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
        exact ⟨(sc.1.bounds v l (.inr hl)).2, sc.2⟩)
      (hc.extLNew hlv hx) c₁.remember.addUpper
  | .extRHit _ _ _ hx _, hs, ha, _, _, h =>
    hx.consist hs.remember.bounds ha (fun _ h => nomatch h) h.remember
  | .extRNew (s := s₀) (v := v) (a' := a') (s₁ := s₁) _ _ hlv hx _ h', hs, ha, hb, hc, h => by
    have hv : v < s₁.next :=
      Nat.lt_of_lt_of_le ((SType.in_var (X := (· < s₀.next))).mp hb) hx.same.next
    have sc := hx.scope hs.remember ha (fun _ h => nomatch h)
    have c₁ := hx.consist hs.remember.bounds ha (fun _ h => nomatch h) h.remember
    exact h'.consist (Scope.addLower (s := s₁.remember a' (.var v)) sc.1.remember hv sc.2)
      (fun p hp => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
        exact ⟨sc.2, (sc.1.bounds v u (.inl hu)).2⟩)
      (hc.extRNew hlv hx) c₁.remember.addLower
  | .recordSig (k := k) _ _ _ _ _ h', hs, ha, hb, hc, h =>
    h'.consist hs.remember ha ((SType.in_sig.mp hb).domain k) hc.remember h.remember
  | .sigL (s := s₀) (P := Q) (b := b) _ hb' h', hs, ha, hb, hc, h => by
    have hc' : CacheInLog (s₀.remember (.sig Q) b) :=
      hc.remember (.inl ⟨(fun _ h => nomatch h), hb'.nonvar⟩)
    exact h'.consist hs.remember
      (fun p hp => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
        exact ⟨(SType.in_sig.mp ha).domain k, hb⟩)
      hc' (h.remember.weaken fun _ hp => List.mem_append_right _ hp)

/-- Propagation: processing the pending pairs `ps` discharges them. -/
theorem ConstrainEach.consist : ConstrainEach s ps s' → Scope s →
    (∀ p ∈ ps, p.1.In (· < s.next) ∧ p.2.In (· < s.next)) → CacheInLog s →
    ConsExcept s (ps ++ P) → ConsExcept s' P
  | .nil, _, _, _, h => h
  | .cons (a := a) (b := b) (rest := rest) h₁ h₂, hs, hp, hc, h =>
    have p₁ := hp _ (List.mem_cons_self ..)
    have r₁ := h₁.logged hc
    have c₁ := h₁.consist hs p₁.1 p₁.2 hc h
    h₂.consist (h₁.scope hs p₁.1 p₁.2)
      (pairs_scope_mono (fun p h => hp p (List.mem_cons_of_mem _ h)) h₁.keeps.next) r₁.1
      fun v l u hl hu => by
        rcases c₁ v l u hl hu with hlog | hp
        · exact .inl hlog
        · simp only [List.cons_append, List.mem_cons] at hp
          rcases hp with hp | hp
          · cases hp; exact .inl r₁.2
          · exact .inr hp

theorem ConstrainField.consist : ConstrainField s a b s' → Scope s → a.In (· < s.next) →
    b.In (· < s.next) → CacheInLog s → ConsExcept s P → ConsExcept s' P
  | .toAbs, _, _, _, _, h | .misMis, _, _, _, _, h | .misOpt, _, _, _, _, h => h
  | .optOpt _ h', hs, ha, hb, hc, h =>
    h'.consist hs (SType.in_opt.mp ha) (SType.in_opt.mp hb) hc h
  | .preOpt _ h', hs, ha, hb, hc, h => h'.consist hs ha (SType.in_opt.mp hb) hc h
  | .pre _ _ h', hs, ha, hb, hc, h => h'.consist hs ha hb hc h

theorem FieldsEach.consist : FieldsEach s ps s' → Scope s →
    (∀ p ∈ ps, p.1.In (· < s.next) ∧ p.2.In (· < s.next)) → CacheInLog s →
    ConsExcept s P → ConsExcept s' P
  | .nil, _, _, _, h => h
  | .cons h₁ h₂, hs, hp, hc, h =>
    have p₁ := hp _ (List.mem_cons_self ..)
    h₂.consist (h₁.scope hs p₁.1 p₁.2)
      (pairs_scope_mono (fun p h => hp p (List.mem_cons_of_mem _ h)) h₁.keeps.next)
      (h₁.logged hc).1 (h₁.consist hs p₁.1 p₁.2 hc h)

theorem Expand.consist : Expand s t ms t' s' → Scope s → t.In (· < s.next) →
    ms.In (· < s.next) → CacheInLog s → ConsExcept s P → ConsExcept s' P
  | .none, _, _, _, _, h => h
  | .abs _ h', hs, _, hm, hc, h => h'.consist hs hm.absPairs hc h
  | .nil _ h', hs, _, hm, hc, h => h'.consist hs hm.misPairs hc h
  | .allAbsent _ _ h', hs, _, hm, hc, h => h'.consist hs hm.absentIn.absPairs hc h
  | .memo (s₁ := s₁) _ _ h₁ hl h₂, hs, ht, hm, hc, h => by
    have hs₁ := h₁.scope hs hm.absentIn.absPairs
    have n₁ := h₁.keeps.next
    exact h₂.consist hs₁ (ht.scope_mono n₁)
      (SType.in_record.mpr ⟨hm.presentIn.scope_mono n₁,
        (SType.in_var (X := (· < s₁.next))).mpr (hs₁.exps _ (lookup_mem hl)).2⟩)
      (h₁.logged hc).1 (h₁.consist hs hm.absentIn.absPairs hc h)
  | .fresh (s₁ := s₁) _ _ h₁ _ _ hlv h₂, hs, ht, hm, hc, h => by
    have hs₁ := h₁.scope hs hm.absentIn.absPairs
    have n₁ := Nat.le_trans h₁.keeps.next (Nat.le_succ _)
    have hlv' := h₁.grows.level ▸ hlv
    exact h₂.consist
      (hs₁.addExp ((SType.in_var (X := (· < s₁.next))).mp (ht.scope_mono h₁.keeps.next)) hlv')
      (ht.scope_mono n₁)
      (SType.in_record.mpr ⟨hm.presentIn.scope_mono n₁,
        (SType.in_var (X := (· < s₁.next + 1))).mpr (Nat.lt_succ_self _)⟩)
      ((h₁.logged hc).1.addExp hlv') (h₁.consist hs hm.absentIn.absPairs hc h).expand
end

/-! ## Lemma 2, at the level of the bound graph -/

/-- The invariant of states the algorithm reaches between calls. -/
structure Inv (s : State) : Prop where
  just : Justified s
  cons : Consistent s

/-- **Soundness of constraining** (graph form of the paper's Lemma 2): a
successful top-level `constrain` call on types in scope preserves the
invariant, and the constraint it was asked to solve is accepted. -/
theorem ConstrainTop.sound (h : ConstrainTop s a b s') (hs : Scope s) (ha : a.In (· < s.next))
    (hb : b.In (· < s.next)) (hi : Inv s) : Inv s' ∧ Logged s' a b := by
  obtain ⟨s₁, hc, rfl⟩ := h
  have hs₀ : Scope { s with cache := [] } := ⟨hs.bounds, hs.exps, hs.expLevel⟩
  have hc₀ : CacheInLog { s with cache := [] } :=
    ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ _ h => nomatch h), hs.expLevel⟩
  exact ⟨⟨hc.just hc₀ hi.just, hc.consist hs₀ ha hb hc₀ hi.cons⟩, (hc.logged hc₀).2⟩

/-- A top-level `constrain` call keeps the state in scope and the
invariant. -/
theorem ConstrainTop.step (h : ConstrainTop s a b s') (hs : Scope s) (hi : Inv s)
    (ha : a.In (· < s.next)) (hb : b.In (· < s.next)) : Scope s' ∧ Inv s' :=
  ⟨h.scope hs ha hb, (h.sound hs ha hb hi).1⟩

/-- A top-level `constrain` call keeps the bounds consistent. -/
theorem ConstrainTop.consistent (h : ConstrainTop s a b s') (hs : Scope s)
    (ha : a.In (· < s.next)) (hb : b.In (· < s.next)) (hc : Consistent s) : Consistent s' := by
  obtain ⟨s₁, h, rfl⟩ := h
  have hs₀ : Scope { s with cache := [] } := ⟨hs.bounds, hs.exps, hs.expLevel⟩
  have hc₀ : CacheInLog { s with cache := [] } :=
    ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ _ h => nomatch h), hs.expLevel⟩
  exact h.consist hs₀ ha hb hc₀ hc

/-- Every constraint a top-level `constrain` call logs is justified when
it returns. -/
theorem ConstrainTop.justNew (h : ConstrainTop s a b s') (hs : Scope s) :
    ∀ p ∈ s'.log, p ∈ s.log ∨ GStep s'.bounds (Logged s') p.1 p.2 := by
  obtain ⟨s₁, h, rfl⟩ := h
  have hc₀ : CacheInLog { s with cache := [] } :=
    ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ _ h => nomatch h), hs.expLevel⟩
  exact h.just hc₀ (P := s.log) fun p hp => .inl hp

theorem Inv.fresh (h : Inv s) : Inv s.fresh := ⟨h.just, h.cons⟩

theorem SType.in_prim {X : Nat → Prop} {n : String} : (SType.prim n).In X :=
  fun _ h => by simp [SType.vars] at h

theorem SParams.In.scope_mono {P : SParams} {n m : Nat} (h : P.In (· < n)) (hnm : n ≤ m) :
    P.In (· < m) := fun w hw => Nat.lt_of_lt_of_le (h w hw) hnm

/-- The fresh variable is in scope once allocated. -/
theorem in_fresh (s : State) : (SType.var s.next).In (· < s.fresh.next) :=
  (SType.in_var (X := (· < s.next + 1))).mpr (Nat.lt_succ_self _)

theorem Inv.init {K : Nat → List String} {L : Nat → Nat} : Inv (State.initKL K L) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h _ => nomatch h)⟩

theorem Scope.init {K : Nat → List String} {L : Nat → Nat} : Scope (State.initKL K L) :=
  ⟨(fun _ _ h => h.elim (fun h => nomatch h) (fun h => nomatch h)), (fun _ h => nomatch h),
    (fun _ _ _ h => nomatch h)⟩

end BoltCore.Alg
