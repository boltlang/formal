import BoltCore.PolyLet

/-!
# An executable certificate checker (roadmap 6b)

Boolean checks for everything `PTyp.sound_top` asks of a certificate and
a typing skeleton, each proved to imply the property it checks:

* `Certificate.check c = true → c.Valid` (`Certificate.check_valid`);
* `infer c Γ a = some st → PTyp c Γ a.erase st` (`infer_sound`), where `a`
  is an *annotated term* (`Ann`): the term, with the types a skeleton
  cannot compute bottom-up (the parameter type of a `fun`, the result type
  of an application or selection, the tail of an extension, the
  generalized variables of a `let`, the renaming at each use of a
  let-bound name).

Together (`check_sound`): an accepted certificate types the term in the
declarative system (`Typing.lean`). Only this direction matters for trusting the checker:
a bug in the inferencer or the certificate printer can make the checker
reject, never accept, a wrong typing. Whether every run of the inferencer
yields an accepted certificate is the adequacy question, tested on the
examples instead (`scripts/check-certs.sh`, with `Main.lean`).

The universal quantifiers of `Valid` range over all variables and all
labels; the checks range over the finite lists of the certificate, using
that unlisted variables have no bounds and that only labels in some kind
can be lacked.
-/

namespace BoltCore.Alg

open State

deriving instance DecidableEq for SType, SFields

/-! ## Variables with bounds -/

theorem lookup_some_mem {β : Type} {l : List (Nat × β)} {a : Nat} {b : β}
    (h : l.lookup a = some b) : a ∈ l.map (·.1) :=
  List.mem_map.mpr ⟨_, lookup_mem h, rfl⟩

namespace Certificate

/-- The variables the certificate lists bounds for. -/
def keys (c : Certificate) : List Nat := c.vars.map (·.1)

theorem bounds_of_not_key {c : Certificate} {v : Nat} (h : v ∉ c.keys) : c.bounds v = {} := by
  simp only [bounds]
  cases hl : c.vars.lookup v with
  | none => rfl
  | some _ => exact absurd (lookup_some_mem hl) h

/-- A property of the bounds that holds of no bounds holds of every
variable if it holds of the listed ones. -/
theorem forall_bounds {c : Certificate} {P : Nat → Bounds → Prop} (h₀ : ∀ v, P v {})
    (h : ∀ v ∈ c.keys, P v (c.bounds v)) (v : Nat) : P v (c.bounds v) := by
  by_cases hv : v ∈ c.keys
  · exact h v hv
  · rw [bounds_of_not_key hv]; exact h₀ v

instance (c : Certificate) (a b : SType) : Decidable (c.Accepts a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

end Certificate

instance (s : State) (a b : SType) : Decidable (Logged s a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ## Justification -/

def SType.nonVar : SType → Bool
  | .var _ => false
  | _ => true

theorem SType.nonVar_sound : ∀ {b : SType}, b.nonVar = true → ∀ w, b ≠ .var w
  | .var _, h, _ => by simp [SType.nonVar] at h
  | .prim _, _, _ | .arrow _ _, _, _ | .record _ _, _, _ | .abs, _, _ => fun h => nomatch h

section Just
variable (σ : Nat → Bounds) (K : Nat → List String) (R : SType → SType → Prop) [DecidableRel R]

/-- `FieldR R f g`: `g` is `Abs`, or both are present and related. -/
def fieldB (f g : SType) : Bool := g == .abs || (f != .abs && g != .abs && decide (R f g))

variable {σ K R}

theorem fieldB_sound {f g : SType} (h : fieldB R f g = true) : FieldR R f g := by
  by_cases hg : g = .abs
  · subst hg; exact .toAbs
  · simp [fieldB, hg] at h
    exact .pre h.1 hg h.2

variable (R) in
def relB : SFields → SFields → Bool
  | .nil, .nil => true
  | .cons n f fs, .cons m g gs => n == m && fieldB R f g && relB fs gs
  | _, _ => false

theorem relB_sound : ∀ {fs gs : SFields}, relB R fs gs = true → SFields.Rel (FieldR R) fs gs
  | .nil, .nil, _ => .nil
  | .cons n f fs, .cons m g gs, h => by
    simp only [relB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, h₁⟩, h₂⟩ := h
    exact .cons (fieldB_sound h₁) (relB_sound h₂)
  | .nil, .cons .., h | .cons .., .nil, h => by simp [relB] at h

variable (R) in
def pairsB (ps : List (SType × SType)) : Bool := ps.all fun p => fieldB R p.1 p.2

theorem pairsB_sound {ps : List (SType × SType)} (h : pairsB R ps = true) :
    ∀ p ∈ ps, FieldR R p.1 p.2 :=
  fun p hp => fieldB_sound (List.all_eq_true.mp h p hp)

variable (σ K R) in
/-- The tails `t'` such that `ExpandG σ R t ms t'` holds (with the kind
`K v` for a row variable `v`). -/
def expandRes (t : SType) (ms : SFields) : List SType :=
  if ms = .nil then [t]
  else match t with
    | .abs => if pairsB R ms.absPairs then [.abs] else []
    | .var v =>
      if pairsB R (ms.absentIn (K v)).absPairs then
        if ms.presentIn (K v) = .nil then [.var v]
        else (σ v).upper.filterMap fun u =>
          match u with
          | .record P' (.var r) => if relB R P' (ms.presentIn (K v)) then some (.var r) else none
          | _ => none
      else []
    | _ => []

theorem expandRes_sound {t ms t' : _} (h : t' ∈ expandRes σ K R t ms) : ExpandG σ R t ms t' := by
  unfold expandRes at h
  split at h
  · next hm => subst hm; simp at h; subst h; exact .none
  · next hm =>
    split at h
    · split at h
      · next hp => simp at h; subst h; exact .abs hm (pairsB_sound hp)
      · simp at h
    · next v =>
      split at h
      · next hp =>
        split at h
        · next hn => simp at h; subst h; exact .varAbsent (K v) (pairsB_sound hp) hn
        · next hn =>
          obtain ⟨u, hu, hu'⟩ := List.mem_filterMap.mp h
          split at hu'
          · split at hu'
            · next hr => cases hu'; exact .var (K v) hm (pairsB_sound hp) hn hu (relB_sound hr)
            · cases hu'
          · cases hu'
      · simp at h
    · simp at h

variable (σ K R) in
/-- The structural rules of `GStep`. -/
def structB : SType → SType → Bool
  | .arrow l₀ r₀, .arrow l₁ r₁ => decide (R l₁ l₀) && decide (R r₀ r₁)
  | .abs, .record fs t => pairsB R fs.absPairs && decide (R .abs t)
  | .record fa ta, .record fb tb =>
    pairsB R ((rowView (.record fa ta)).1.common (rowView (.record fb tb)).1) &&
      (expandRes σ K R (rowView (.record fa ta)).2
          ((rowView (.record fa ta)).1.missing (rowView (.record fb tb)).1)).any fun t₀' =>
        decide (R (restRow ((rowView (.record fb tb)).1.missing (rowView (.record fa ta)).1) t₀')
          (rowView (.record fb tb)).2)
  | _, _ => false

theorem structB_sound : ∀ {a b : SType}, structB σ K R a b = true → GStep σ R a b
  | .arrow l₀ r₀, .arrow l₁ r₁, h => by
    simp only [structB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .arrow h.1 h.2
  | .abs, .record fs t, h => by
    simp only [structB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .absRecord (pairsB_sound h.1) h.2
  | .record fa ta, .record fb tb, h => by
    simp only [structB, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨hf, t₀', he, ht⟩ := h
    exact .record rfl rfl (pairsB_sound hf) (expandRes_sound he) ht
  | .var _, _, h | .prim _, _, h => by simp [structB] at h
  | .arrow _ _, .var _, h | .arrow _ _, .prim _, h | .arrow _ _, .record _ _, h
  | .arrow _ _, .abs, h => by simp [structB] at h
  | .record _ _, .var _, h | .record _ _, .prim _, h | .record _ _, .arrow _ _, h
  | .record _ _, .abs, h => by simp [structB] at h
  | .abs, .var _, h | .abs, .prim _, h | .abs, .arrow _ _, h | .abs, .abs, h => by
    simp [structB] at h

variable (σ R) in
/-- A variable on the left: its upper bound, or through one (`viaL`). -/
def varLB : SType → SType → Bool
  | .var v, b => decide (b ∈ (σ v).upper) ||
      (b.nonVar && (σ v).upper.any fun b' => b'.nonVar && b' != .abs && decide (R b' b))
  | _, _ => false

theorem varLB_sound : ∀ {a b : SType}, varLB σ R a b = true → GStep σ R a b
  | .var v, b, h => by
    simp only [varLB, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.any_eq_true,
      bne_iff_ne, ne_eq] at h
    rcases h with h | ⟨hb, b', hb', ⟨hn, ha⟩, hR⟩
    · exact .varL h
    · exact .viaL hb' (SType.nonVar_sound hn) ha (SType.nonVar_sound hb) hR
  | .prim _, _, h | .arrow _ _, _, h | .record _ _, _, h | .abs, _, h => by simp [varLB] at h

variable (σ R) in
/-- A variable on the right: its lower bound, or through one (`viaR`). -/
def varRB : SType → SType → Bool
  | a, .var v => decide (a ∈ (σ v).lower) ||
      (a.nonVar && a != .abs && (σ v).lower.any fun a' => a'.nonVar && a' != .abs && decide (R a a'))
  | _, _ => false

theorem varRB_sound : ∀ {a b : SType}, varRB σ R a b = true → GStep σ R a b
  | a, .var v, h => by
    simp only [varRB, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.any_eq_true,
      bne_iff_ne, ne_eq] at h
    rcases h with h | ⟨⟨ha, ha'⟩, a', hl, ⟨hn, hab⟩, hR⟩
    · exact .varR h
    · exact .viaR hl (SType.nonVar_sound hn) hab (SType.nonVar_sound ha) ha' hR
  | _, .prim _, h | _, .arrow _ _, h | _, .record _ _, h | _, .abs, h => by simp [varRB] at h

variable (σ K R) in
/-- One justification step (`GStep`). -/
def gstepB (a b : SType) : Bool :=
  b == .abs || structB σ K R a b || varLB σ R a b || varRB σ R a b

theorem gstepB_sound {a b : SType} (h : gstepB σ K R a b = true) : GStep σ R a b := by
  simp only [gstepB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · subst h; exact .absR
  · exact structB_sound h
  · exact varLB_sound h
  · exact varRB_sound h

end Just

/-! ## Sorts and kinds -/

mutual
def SType.nacB : SType → Bool
  | .arrow a b => a != .abs && b != .abs && a.nacB && b.nacB
  | .record fs t => fs.nacB && t.nacB
  | .var _ | .prim _ | .abs => true

def SFields.nacB : SFields → Bool
  | .nil => true
  | .cons _ f fs => f.nacB && fs.nacB
end

mutual
theorem SType.nacB_sound : ∀ {t : SType}, t.nacB = true → t.NAC
  | .arrow a b, h => by
    simp only [SType.nacB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨h.1.1.1, h.1.1.2, SType.nacB_sound h.1.2, SType.nacB_sound h.2⟩
  | .record fs t, h => by
    simp only [SType.nacB, Bool.and_eq_true] at h
    exact ⟨SFields.nacB_sound h.1, SType.nacB_sound h.2⟩
  | .var _, _ | .prim _, _ | .abs, _ => trivial

theorem SFields.nacB_sound : ∀ {fs : SFields}, fs.nacB = true → fs.NAC
  | .nil, _ => trivial
  | .cons _ f fs, h => by
    simp only [SFields.nacB, Bool.and_eq_true] at h
    exact ⟨SType.nacB_sound h.1, SFields.nacB_sound h.2⟩
end

section Kinds
variable (K : Nat → List String)

instance (fs : SFields) (ρ : Nat) (l : String) : Decidable (RowKind K fs ρ l) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `KEmpty`: a row over a row variable lists every label the variable lacks. -/
def kemptyB (t : SType) : Bool :=
  match (rowView t).2 with
  | .var ρ => (K ρ).all fun l => decide (l ∈ (rowView t).1.labels)
  | _ => true

/-- `RecOK`: a record over a row variable lists some labels, all lacked by it. -/
def recOKB (t : SType) : Bool :=
  match (rowView t).2 with
  | .var ρ => (rowView t).1 != .nil && (rowView t).1.labels.all fun l => decide (l ∈ K ρ)
  | _ => true

/-- `KOK`: only labels in the kinds of the two tails can be lacked. -/
def kokB (a b : SType) : Bool :=
  match (rowView a).2, (rowView b).2 with
  | .var ρ, .var σ => (K ρ ++ K σ).all fun l =>
      decide (RowKind K (rowView a).1 ρ l ↔ RowKind K (rowView b).1 σ l)
  | _, _ => true

mutual
def SType.wkB : SType → Bool
  | .arrow a b => a.wkB && kemptyB K a && b.wkB && kemptyB K b
  | .record fs t => fs.wkB && t.wkB && recOKB K (.record fs t)
  | .var _ | .prim _ | .abs => true

def SFields.wkB : SFields → Bool
  | .nil => true
  | .cons _ f fs => f.wkB && kemptyB K f && fs.wkB
end

variable {K}

theorem kemptyB_sound {t : SType} (h : kemptyB K t = true) : KEmpty K t := by
  intro ρ hρ l ⟨hl, hn⟩
  simp only [kemptyB, hρ, List.all_eq_true, decide_eq_true_eq] at h
  exact hn (h l hl)

theorem recOKB_sound {t : SType} (h : recOKB K t = true) : RecOK K t := by
  intro ρ hρ
  simp only [recOKB, hρ, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  exact h

theorem kokB_sound {a b : SType} (h : kokB K a b = true) : KOK K a b := by
  intro ρ σ hρ hσ l
  simp only [kokB, hρ, hσ, List.all_eq_true, decide_eq_true_eq] at h
  by_cases hl : l ∈ K ρ ++ K σ
  · exact h l hl
  · simp only [List.mem_append, not_or] at hl
    exact ⟨fun h => absurd h.1 hl.1, fun h => absurd h.1 hl.2⟩

mutual
theorem SType.wkB_sound : ∀ {t : SType}, t.wkB K = true → WK K t
  | .arrow a b, h => by
    simp only [SType.wkB, Bool.and_eq_true] at h
    exact ⟨SType.wkB_sound h.1.1.1, kemptyB_sound h.1.1.2, SType.wkB_sound h.1.2,
      kemptyB_sound h.2⟩
  | .record fs t, h => by
    simp only [SType.wkB, Bool.and_eq_true] at h
    exact ⟨SFields.wkB_sound h.1.1, SType.wkB_sound h.1.2, recOKB_sound h.2⟩
  | .var _, _ | .prim _, _ | .abs, _ => trivial

theorem SFields.wkB_sound : ∀ {fs : SFields}, fs.wkB K = true → FWK K fs
  | .nil, _ => trivial
  | .cons _ f fs, h => by
    simp only [SFields.wkB, Bool.and_eq_true] at h
    exact ⟨SType.wkB_sound h.1.1, kemptyB_sound h.1.2, SFields.wkB_sound h.2⟩
end

end Kinds

/-! ## Validity -/

namespace Certificate

variable (c : Certificate)

/-- Every accepted constraint is justified by one step. -/
def justB : Bool := c.log.all fun p => gstepB c.bounds c.kind (Logged c.state) p.1 p.2

/-- Each lower bound of a variable is accepted below each upper bound. -/
def consB : Bool :=
  c.keys.all fun v => (c.bounds v).lower.all fun l => (c.bounds v).upper.all fun u =>
    decide (c.Accepts l u)

/-- Every bound is an accepted constraint. -/
def inLogB : Bool :=
  c.keys.all fun v =>
    (c.bounds v).upper.all (fun x => decide ((SType.var v, x) ∈ c.log)) &&
    (c.bounds v).lower.all (fun x => decide ((x, SType.var v) ∈ c.log))

/-- `Abs` is never a function parameter or result. -/
def nacB : Bool := c.log.all fun p => p.1.nacB && p.2.nacB

/-- The kind discipline. -/
def kindsB : Bool := c.log.all fun p => p.1.wkB c.kind && p.2.wkB c.kind && kokB c.kind p.1 p.2

/-- The ranks exclude structural recursive types. -/
def rankedB : Bool :=
  c.keys.all fun v => ((c.bounds v).upper ++ (c.bounds v).lower).all fun b =>
    match b with
    | .var w => decide (c.rank w ≤ c.rank v)
    | _ => b.vars.all fun w => decide (c.rank w < c.rank v)

/-- The certificate checker. -/
def check : Bool := c.justB && c.consB && c.inLogB && c.nacB && c.kindsB && c.rankedB

variable {c}

theorem justB_sound (h : c.justB = true) : Justified c.state :=
  fun p hp => .inr (gstepB_sound (List.all_eq_true.mp h p hp))

theorem consB_sound (h : c.consB = true) : Consistent c.state := by
  intro v l u hl hu
  refine .inl ?_
  revert l u
  refine forall_bounds (P := fun _ b => ∀ l u, l ∈ b.lower → u ∈ b.upper → c.Accepts l u)
    (fun _ _ _ h => nomatch h) (fun v hv => ?_) v
  intro l u hl hu
  simp only [consB, List.all_eq_true, decide_eq_true_eq] at h
  exact h v hv l hl u hu

theorem inLogB_sound (h : c.inLogB = true) : BoundsInLog c.state := by
  simp only [inLogB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun v x hx => ?_, fun v x hx => ?_⟩
  · revert x
    exact forall_bounds (P := fun v b => ∀ x, x ∈ b.upper → (SType.var v, x) ∈ c.log)
      (fun _ _ h => nomatch h) (fun v hv => (h v hv).1) v
  · revert x
    exact forall_bounds (P := fun v b => ∀ x, x ∈ b.lower → (x, SType.var v) ∈ c.log)
      (fun _ _ h => nomatch h) (fun v hv => (h v hv).2) v

theorem nacB_sound (h : c.nacB = true) : LogNAC c.state := fun p hp => by
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true] at this
  exact ⟨SType.nacB_sound this.1, SType.nacB_sound this.2⟩

theorem kindsB_sound (h : c.kindsB = true) : KLog c.kind c.state := fun p hp => by
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true] at this
  exact ⟨SType.wkB_sound this.1.1, SType.wkB_sound this.1.2, kokB_sound this.2⟩

theorem rankedB_sound (h : c.rankedB = true) : StructRanked c.bounds c.rank := by
  intro v b hb
  revert b
  refine forall_bounds (P := fun v bs => ∀ b, (b ∈ bs.upper ∨ b ∈ bs.lower) →
      (∀ w, b = .var w → c.rank w ≤ c.rank v) ∧
        ((∀ w, b ≠ .var w) → ∀ w ∈ b.vars, c.rank w < c.rank v))
    (fun _ _ h => by rcases h with h | h <;> exact nomatch h) (fun v hv => ?_) v
  intro b hb
  have := List.all_eq_true.mp (List.all_eq_true.mp h v hv) b (List.mem_append.mpr hb)
  cases b with
  | var w =>
    simp only [decide_eq_true_eq] at this
    exact ⟨fun w' e => by cases e; exact this, fun h => absurd rfl (h w)⟩
  | prim _ | arrow _ _ | record _ _ | abs =>
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact ⟨fun _ e => (nomatch e), fun _ => this⟩

/-- **The checker is sound**: an accepted certificate is valid. -/
theorem check_valid (h : c.check = true) : c.Valid := by
  simp only [check, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hj, hc, hl, hn, hk, hr⟩ := h
  exact ⟨⟨justB_sound hj, consB_sound hc⟩, inLogB_sound hl, nacB_sound hn, kindsB_sound hk,
    rankedB_sound hr⟩

end Certificate

/-! ## Generalization and instantiation -/

instance (σ : Nat → Bounds) (gen' : List Nat) (e : CEntry) : Decidable (e.Avoids σ gen') := by
  cases e <;> simp only [CEntry.Avoids] <;> infer_instance

namespace Certificate

variable (c : Certificate)

/-- `GenOK`: no other variable's bounds, and nothing in the context,
mention `gen`. -/
def genB (Γ : PCtx) (gen : List Nat) : Bool :=
  (c.keys.all fun v => decide (v ∈ gen) ||
    ((c.bounds v).upper ++ (c.bounds v).lower).all fun b => decide (Av gen b)) &&
  Γ.all fun p => decide (p.2.Avoids c.bounds gen)

/-- The renaming a list of pairs gives: unlisted variables are fixed. -/
def renameOf (ρ : List (Nat × Nat)) (v : Nat) : Nat := (ρ.lookup v).getD v

/-- `InstOK` for `renameOf ρ`: only `gen` is renamed, and the copies'
renamed bounds are accepted. -/
def instB (gen : List Nat) (ρ : List (Nat × Nat)) : Bool :=
  (ρ.all fun p => decide (p.1 ∈ gen)) &&
  gen.all fun α =>
    (c.bounds α).upper.all (fun u => decide (c.Accepts (.var (renameOf ρ α)) (u.rename (renameOf ρ)))) &&
    (c.bounds α).lower.all (fun l => decide (c.Accepts (l.rename (renameOf ρ)) (.var (renameOf ρ α))))

variable {c}

theorem genB_sound {Γ : PCtx} {gen : List Nat} (h : c.genB Γ gen = true) : GenOK c Γ gen := by
  simp only [genB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  refine ⟨fun v hv b hb => ?_, h.2⟩
  revert b hv
  refine forall_bounds (P := fun v bs => v ∉ gen → ∀ b, (b ∈ bs.upper ∨ b ∈ bs.lower) → Av gen b)
    (fun _ _ _ h => by rcases h with h | h <;> exact nomatch h) (fun v hk => ?_) v
  intro hv b hb
  rcases h.1 v hk with h' | h'
  · exact absurd h' hv
  · exact h' b (List.mem_append.mpr hb)

theorem renameOf_fix {ρ : List (Nat × Nat)} {gen : List Nat} (h : ∀ p ∈ ρ, p.1 ∈ gen) {v : Nat}
    (hv : v ∉ gen) : renameOf ρ v = v := by
  simp only [renameOf]
  cases hl : ρ.lookup v with
  | none => rfl
  | some _ =>
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (lookup_some_mem hl)
    exact absurd (h p hp) hv

theorem instB_sound {gen : List Nat} {ρ : List (Nat × Nat)} (h : c.instB gen ρ = true) :
    InstOK c gen (renameOf ρ) := by
  simp only [instB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨fun _ hv => renameOf_fix h.1 hv, fun α hα => (h.2 α hα).1, fun α hα => (h.2 α hα).2⟩

end Certificate

/-! ## Annotated terms -/

mutual
/-- A term with the types its skeleton needs but cannot compute. -/
inductive Ann where
  | lit : Int → Ann
  /-- A monomorphic variable. -/
  | var : String → Ann
  /-- A use of a let-bound name, with the renaming of its generalized
  variables (unlisted variables are fixed). -/
  | inst : String → List (Nat × Nat) → Ann
  /-- `fun x -> t`, with the type of `x`. -/
  | lam : String → SType → Ann → Ann
  /-- An application, with its result type. -/
  | app : Ann → Ann → SType → Ann
  | rcd : AFields → Ann
  /-- `t.l`, with the type of the field. -/
  | sel : Ann → String → SType → Ann
  /-- `t with {fs}`, with the row of the other fields. -/
  | ext : Ann → AFields → SType → Ann
  /-- `let x = r in b`, generalizing `gen`. -/
  | letIn : String → List Nat → Ann → Ann → Ann
  /-- `let rec x = r in b`, with the type of `x`, generalizing `gen`. -/
  | letRec : String → List Nat → SType → Ann → Ann → Ann

inductive AFields where
  | nil
  | cons : String → Ann → AFields → AFields
end

mutual
def Ann.erase : Ann → Term
  | .lit n => .lit n
  | .var x | .inst x _ => .var x
  | .lam x _ t => .lam x t.erase
  | .app f a _ => .app f.erase a.erase
  | .rcd fs => .rcd fs.erase
  | .sel t l _ => .sel t.erase l
  | .ext t fs _ => .ext t.erase fs.erase
  | .letIn x _ r b => .letIn false x r.erase b.erase
  | .letRec x _ _ r b => .letIn true x r.erase b.erase

def AFields.erase : AFields → List (String × Term)
  | .nil => []
  | .cons l t fs => (l, t.erase) :: fs.erase
end

/-! ## Checking skeletons -/

section Infer
variable (c : Certificate)

mutual
/-- The skeleton's type for an annotated term, if it checks. -/
def infer (Γ : PCtx) : Ann → Option SType
  | .lit _ => some (.prim "int")
  | .var x =>
    match Γ.lookup x with
    | some (.mono st) => some st
    | _ => none
  | .inst x ρ =>
    match Γ.lookup x with
    | some (.poly gen st) => if c.instB gen ρ then some (st.rename (Certificate.renameOf ρ)) else none
    | _ => none
  | .lam x st₁ t =>
    match infer ((x, .mono st₁) :: Γ) t with
    | some st₂ => some (.arrow st₁ st₂)
    | none => none
  | .app f a st =>
    match infer Γ f, infer Γ a with
    | some stf, some sta =>
      if stf ≠ .abs ∧ c.Accepts stf (.arrow sta st) then some st else none
    | _, _ => none
  | .rcd fs =>
    match inferFields Γ fs with
    | some F => some (.record F .abs)
    | none => none
  | .sel t l st =>
    match infer Γ t with
    | some st₀ =>
      if st₀ ≠ .abs ∧ c.Accepts st₀ (.record (.cons l st .nil) .abs) ∧ st ≠ .abs
      then some st else none
    | none => none
  | .ext t .nil _ => infer Γ t
  | .ext t (.cons l a fs) ρ =>
    match infer Γ t, inferFields Γ (.cons l a fs) with
    | some st₀, some F =>
      if st₀ ≠ .abs ∧ c.Accepts st₀ (.record F.absOf ρ) then some (.record F ρ) else none
    | _, _ => none
  | .letIn x gen r b =>
    match infer Γ r with
    | some str => if c.genB Γ gen then infer ((x, .poly gen str) :: Γ) b else none
    | none => none
  | .letRec x gen stx r b =>
    match r with
    | .lam .. =>
      match infer ((x, .mono stx) :: Γ) r with
      | some inf =>
        if inf ≠ .abs ∧ c.Accepts inf stx ∧ c.genB Γ gen then infer ((x, .poly gen stx) :: Γ) b
        else none
      | none => none
    | _ => none

def inferFields (Γ : PCtx) : AFields → Option SFields
  | .nil => some .nil
  | .cons l t fs =>
    match infer Γ t, inferFields Γ fs with
    | some st, some F => if st ≠ .abs then some (.cons l st F) else none
    | _, _ => none
end

variable {c}

mutual
/-- **Skeleton checking is sound**: a checked annotated term has a typing
skeleton at the type `infer` computes. -/
theorem infer_sound : ∀ {Γ : PCtx} {a : Ann} {st : SType}, infer c Γ a = some st →
    PTyp c Γ a.erase st
  | Γ, .lit _, st, h => by simp only [infer, Option.some.injEq] at h; subst h; exact .lit
  | Γ, .var x, st, h => by
    simp only [infer] at h
    split at h
    · next hx => cases h; exact .var hx
    · cases h
  | Γ, .inst x ρ, st, h => by
    simp only [infer] at h
    split at h
    · next hx =>
      split at h
      · next hi => cases h; exact .inst hx (Certificate.instB_sound hi)
      · cases h
    · cases h
  | Γ, .lam x st₁ t, st, h => by
    simp only [infer] at h
    split at h
    · next ht => cases h; exact .lam (infer_sound ht)
    · cases h
  | Γ, .app f a st', st, h => by
    simp only [infer] at h
    split at h
    · next hf ha =>
      split at h
      · next hc => cases h; exact .app (infer_sound hf) (infer_sound ha) hc.1 hc.2
      · cases h
    · cases h
  | Γ, .rcd fs, st, h => by
    simp only [infer] at h
    split at h
    · next hF => cases h; exact .rcd (inferFields_sound hF)
    · cases h
  | Γ, .sel t l st', st, h => by
    simp only [infer] at h
    split at h
    · next ht =>
      split at h
      · next hc => cases h; exact .sel (infer_sound ht) hc.1 hc.2.1 hc.2.2
      · cases h
    · cases h
  | Γ, .ext t .nil _, st, h => by
    simp only [infer] at h
    exact .extNil (infer_sound h)
  | Γ, .ext t (.cons l a fs) ρ, st, h => by
    simp only [infer] at h
    split at h
    · next ht hF =>
      split at h
      · next hc =>
        cases h
        exact .ext (infer_sound ht) (inferFields_sound (Γ := Γ) (fs := .cons l a fs) hF) hc.1 hc.2
      · cases h
    · cases h
  | Γ, .letIn x gen r b, st, h => by
    simp only [infer] at h
    split at h
    · next hr =>
      split at h
      · next hg => exact .letIn (infer_sound hr) (Certificate.genB_sound hg) (infer_sound h)
      · cases h
    · cases h
  | Γ, .letRec x gen stx r b, st, h => by
    simp only [infer] at h
    split at h
    · next x' st₁ t =>
      split at h
      · next hr =>
        split at h
        · next hc =>
          exact .letRec trivial (infer_sound hr) hc.1 hc.2.1 (Certificate.genB_sound hc.2.2)
            (infer_sound h)
        · cases h
      · cases h
    · cases h

theorem inferFields_sound : ∀ {Γ : PCtx} {fs : AFields} {F : SFields}, inferFields c Γ fs = some F →
    PFields c Γ fs.erase F
  | Γ, .nil, F, h => by simp only [inferFields, Option.some.injEq] at h; subst h; exact .nil
  | Γ, .cons l t fs, F, h => by
    simp only [inferFields] at h
    split at h
    · next ht hF =>
      split at h
      · next hne => cases h; exact .cons (infer_sound ht) hne (inferFields_sound hF)
      · cases h
    · cases h
end

end Infer

/-! ## The checker -/

/-- The built-ins of `lib/typer.ml`, with `if : ∀α. bool → α → α → α` for
the variable `α = k` (the certificate gives it no bounds, so the scheme is
the expected one, with no constraints). -/
def pbuiltins (k : Nat) : PCtx :=
  builtins.map (fun p => (p.1, .mono p.2)) ++
    [("if", .poly [k] (.arrow (.prim "bool") (.arrow (.var k) (.arrow (.var k) (.var k)))))]

/-- **Theorem 1 for the executable checker**: if the certificate checks,
and the annotated term checks against it, the term has the computed type
in the declarative system, over the certificate's solution. -/
theorem check_sound {c : Certificate} {Γ : PCtx} {a : Ann} {st : SType} (hc : c.check = true)
    (h : infer c Γ a = some st) :
    Typ (defsOf c.state) (Γ.toCtx c.bounds .gv) a.erase st.toTy :=
  PTyp.sound_top (Certificate.check_valid hc) (infer_sound h)

end BoltCore.Alg
