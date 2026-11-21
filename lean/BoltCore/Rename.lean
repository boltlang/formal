import BoltCore.Justify

/-!
# Renaming type variables

Instantiation renames the generalized variables of a scheme
(`SType.rename`). This file has what a renaming commutes with: the
variables and the level of a type, the row operations of constraining, the
argument records of a signature, and one step of justification
(`GStep.rename`): a renaming of a justified constraint is justified, when
the bounds and the accepted constraints are closed under it.
-/

namespace BoltCore.Alg

open State

/-! ## Variables -/

mutual
theorem SType.vars_rename (ρ : Nat → Nat) : ∀ t : SType, (t.rename ρ).vars = t.vars.map ρ
  | .var _ | .prim _ | .abs | .missing | .nil => rfl
  | .opt t => by simp only [SType.rename, SType.vars, SType.vars_rename ρ t]
  | .arrow a b => by
    simp only [SType.rename, SType.vars, SType.vars_rename ρ a, SType.vars_rename ρ b,
      List.map_append]
  | .record fs t => by
    simp only [SType.rename, SType.vars, SFields.vars_rename ρ fs, SType.vars_rename ρ t,
      List.map_append]
  | .sig P => by simp only [SType.rename, SType.vars, SParams.vars_rename ρ P]

theorem SFields.vars_rename (ρ : Nat → Nat) : ∀ fs : SFields, (fs.rename ρ).vars = fs.vars.map ρ
  | .nil => rfl
  | .cons _ f fs => by
    simp only [SFields.rename, SFields.vars, SType.vars_rename ρ f, SFields.vars_rename ρ fs,
      List.map_append]

theorem SParams.vars_rename (ρ : Nat → Nat) : ∀ P : SParams, (P.rename ρ).vars = P.vars.map ρ
  | .nil => rfl
  | .cons _ _ _ τ P => by
    simp only [SParams.rename, SParams.vars, SType.vars_rename ρ τ, SParams.vars_rename ρ P,
      List.map_append]
end

/-- A renamed type is in `X` when the renaming sends its variables there. -/
theorem SType.in_rename {X : Nat → Prop} {ρ : Nat → Nat} {t : SType}
    (h : ∀ w ∈ t.vars, X (ρ w)) : (t.rename ρ).In X := by
  intro w hw
  rw [SType.vars_rename] at hw
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
  exact h u hu

mutual
/-- A renaming that fixes the variables of a type fixes the type. -/
theorem SType.rename_fix {ρ : Nat → Nat} : ∀ {t : SType}, (∀ w ∈ t.vars, ρ w = w) → t.rename ρ = t
  | .var v, h => by simp only [SType.rename, h v (by simp [SType.vars])]
  | .prim _, _ | .abs, _ | .missing, _ | .nil, _ => rfl
  | .opt t, h => by simp only [SType.rename, SType.rename_fix (t := t) h]
  | .arrow a b, h => by
    simp only [SType.rename,
      SType.rename_fix (t := a) fun w hw => h w (by simp [SType.vars, hw]),
      SType.rename_fix (t := b) fun w hw => h w (by simp [SType.vars, hw])]
  | .record fs t, h => by
    simp only [SType.rename,
      SFields.rename_fix (fs := fs) fun w hw => h w (by simp [SType.vars, hw]),
      SType.rename_fix (t := t) fun w hw => h w (by simp [SType.vars, hw])]
  | .sig P, h => by simp only [SType.rename, SParams.rename_fix (P := P) h]

theorem SFields.rename_fix {ρ : Nat → Nat} : ∀ {fs : SFields}, (∀ w ∈ fs.vars, ρ w = w) →
    fs.rename ρ = fs
  | .nil, _ => rfl
  | .cons _ f fs, h => by
    simp only [SFields.rename,
      SType.rename_fix (t := f) fun w hw => h w (by simp [SFields.vars, hw]),
      SFields.rename_fix (fs := fs) fun w hw => h w (by simp [SFields.vars, hw])]

theorem SParams.rename_fix {ρ : Nat → Nat} : ∀ {P : SParams}, (∀ w ∈ P.vars, ρ w = w) →
    P.rename ρ = P
  | .nil, _ => rfl
  | .cons _ _ _ τ P, h => by
    simp only [SParams.rename,
      SType.rename_fix (t := τ) fun w hw => h w (by simp [SParams.vars, hw]),
      SParams.rename_fix (P := P) fun w hw => h w (by simp [SParams.vars, hw])]
end

/-! ## Levels -/

mutual
/-- The level of a type is at most `k` when its variables' levels are. -/
theorem SType.level_le {L : Nat → Nat} {k : Nat} : ∀ {t : SType},
    t.level L ≤ k ↔ t.In (fun w => L w ≤ k)
  | .var v => by simp [SType.level, SType.In, SType.vars]
  | .prim _ | .abs | .missing | .nil => by simp [SType.level, SType.In, SType.vars]
  | .opt t => by
    rw [SType.in_opt]; simp only [SType.level]; exact SType.level_le
  | .arrow a b => by
    rw [SType.in_arrow]; simp only [SType.level, Nat.max_le]
    exact and_congr SType.level_le SType.level_le
  | .record fs t => by
    rw [SType.in_record]; simp only [SType.level, Nat.max_le]
    exact and_congr SFields.level_le SType.level_le
  | .sig P => by
    rw [SType.in_sig]; simp only [SType.level]; exact SParams.level_le

theorem SFields.level_le {L : Nat → Nat} {k : Nat} : ∀ {fs : SFields},
    fs.level L ≤ k ↔ fs.In (fun w => L w ≤ k)
  | .nil => by simp [SFields.level, SFields.In, SFields.vars]
  | .cons _ f fs => by
    rw [SFields.in_cons]; simp only [SFields.level, Nat.max_le]
    exact and_congr SType.level_le SFields.level_le

theorem SParams.level_le {L : Nat → Nat} {k : Nat} : ∀ {P : SParams},
    P.level L ≤ k ↔ P.In (fun w => L w ≤ k)
  | .nil => by simp [SParams.level, SParams.In, SParams.vars]
  | .cons _ _ _ τ P => by
    rw [SParams.in_cons]; simp only [SParams.level, Nat.max_le]
    exact and_congr SType.level_le SParams.level_le
end

/-! ## Rows -/

theorem SFields.rename_append (ρ : Nat → Nat) : ∀ fs gs : SFields,
    (fs.append gs).rename ρ = (fs.rename ρ).append (gs.rename ρ)
  | .nil, _ => rfl
  | .cons _ _ fs, gs => by simp only [SFields.append, SFields.rename, SFields.rename_append ρ fs gs]

theorem rowView_rename (ρ : Nat → Nat) : ∀ t : SType,
    rowView (t.rename ρ) = ((rowView t).1.rename ρ, (rowView t).2.rename ρ)
  | .record fs t => by
    simp only [SType.rename, rowView, rowView_rename ρ t, SFields.rename_append]
  | .var _ | .prim _ | .abs | .missing | .nil | .arrow _ _ | .opt _ | .sig _ => rfl

theorem SFields.labels_rename (ρ : Nat → Nat) : ∀ fs : SFields, (fs.rename ρ).labels = fs.labels
  | .nil => rfl
  | .cons _ _ fs => by simp only [SFields.rename, SFields.labels, SFields.labels_rename ρ fs]

theorem SFields.lookup_rename (ρ : Nat → Nat) (l : String) : ∀ fs : SFields,
    (fs.rename ρ).lookup l = (fs.lookup l).map (·.rename ρ)
  | .nil => rfl
  | .cons n f fs => by
    simp only [SFields.rename, SFields.lookup]
    by_cases h : n = l
    · simp [h]
    · simp [h, SFields.lookup_rename ρ l fs]

theorem SFields.missing_rename (ρ : Nat → Nat) (fs₀ : SFields) : ∀ fs₁ : SFields,
    (fs₀.rename ρ).missing (fs₁.rename ρ) = (fs₀.missing fs₁).rename ρ
  | .nil => rfl
  | .cons n f fs => by
    simp only [SFields.rename, SFields.missing, SFields.lookup_rename]
    cases fs₀.lookup n with
    | none => simp [SFields.rename, SFields.missing_rename ρ fs₀ fs]
    | some _ => simp [SFields.missing_rename ρ fs₀ fs]

theorem SFields.absentIn_rename (ρ : Nat → Nat) (K : List String) : ∀ fs : SFields,
    (fs.rename ρ).absentIn K = (fs.absentIn K).rename ρ
  | .nil => rfl
  | .cons n f fs => by
    simp only [SFields.rename, SFields.absentIn]
    by_cases h : n ∈ K
    · simp [h, SFields.rename, SFields.absentIn_rename ρ K fs]
    · simp [h, SFields.absentIn_rename ρ K fs]

theorem SFields.presentIn_rename (ρ : Nat → Nat) (K : List String) : ∀ fs : SFields,
    (fs.rename ρ).presentIn K = (fs.presentIn K).rename ρ
  | .nil => rfl
  | .cons n f fs => by
    simp only [SFields.rename, SFields.presentIn]
    by_cases h : n ∈ K
    · simp [h, SFields.presentIn_rename ρ K fs]
    · simp [h, SFields.rename, SFields.presentIn_rename ρ K fs]

/-- A list of pairs, renamed. -/
def renPairs (ρ : Nat → Nat) (ps : List (SType × SType)) : List (SType × SType) :=
  ps.map fun p => (p.1.rename ρ, p.2.rename ρ)

theorem mem_renPairs {ρ : Nat → Nat} {ps : List (SType × SType)} {a b : SType}
    (h : (a, b) ∈ ps) : (a.rename ρ, b.rename ρ) ∈ renPairs ρ ps :=
  List.mem_map.mpr ⟨(a, b), h, rfl⟩

theorem SFields.absPairs_rename (ρ : Nat → Nat) : ∀ fs : SFields,
    (fs.rename ρ).absPairs = renPairs ρ fs.absPairs
  | .nil => rfl
  | .cons _ _ fs => by
    simp only [SFields.rename, SFields.absPairs, renPairs, List.map_cons, SType.rename]
    exact congrArg _ (SFields.absPairs_rename ρ fs)

theorem SFields.misPairs_rename (ρ : Nat → Nat) : ∀ fs : SFields,
    (fs.rename ρ).misPairs = renPairs ρ fs.misPairs
  | .nil => rfl
  | .cons _ _ fs => by
    simp only [SFields.rename, SFields.misPairs, renPairs, List.map_cons, SType.rename]
    exact congrArg _ (SFields.misPairs_rename ρ fs)

theorem SFields.toMisPairs_rename (ρ : Nat → Nat) : ∀ fs : SFields,
    (fs.rename ρ).toMisPairs = renPairs ρ fs.toMisPairs
  | .nil => rfl
  | .cons _ _ fs => by
    simp only [SFields.rename, SFields.toMisPairs, renPairs, List.map_cons, SType.rename]
    exact congrArg _ (SFields.toMisPairs_rename ρ fs)

theorem restRow_rename (ρ : Nat → Nat) (ex : SFields) (t : SType) :
    (restRow ex t).rename ρ = restRow (ex.rename ρ) (t.rename ρ) := by
  cases ex <;> rfl

theorem SFields.rename_eq_nil {ρ : Nat → Nat} : ∀ {fs : SFields}, fs.rename ρ = .nil ↔ fs = .nil
  | .nil => by simp [SFields.rename]
  | .cons _ _ _ => by simp [SFields.rename]

theorem SType.rename_nonvar {ρ : Nat → Nat} : ∀ {t : SType}, (∀ w, t ≠ .var w) →
    ∀ w, t.rename ρ ≠ .var w
  | .var v, h => absurd rfl (h v)
  | .prim _, _ | .abs, _ | .missing, _ | .nil, _ | .opt _, _ | .arrow _ _, _ | .record _ _, _
  | .sig _, _ => fun _ e => nomatch e

/-! ## Argument records -/

theorem SType.list_rename (ρ : Nat → Nat) : ∀ τs : List SType,
    (SType.list τs).rename ρ = SType.list (τs.map (·.rename ρ))
  | [] => rfl
  | _ :: τs => by
    simp only [SType.list, SType.rename, SFields.rename, List.map_cons, SType.list_rename ρ τs]

theorem SFields.ofParams_rename (ρ : Nat → Nat) : ∀ ps : List (Param SType),
    (SFields.ofParams ps).rename ρ = SFields.ofParams (ps.map (Param.map (·.rename ρ)))
  | [] => rfl
  | p :: ps => by
    simp only [SFields.ofParams, SFields.rename, List.map_cons, SFields.ofParams_rename ρ ps,
      Param.map]
    cases p.opt <;> rfl

theorem SParams.domain_rename (ρ : Nat → Nat) (P : SParams) (k : Nat) :
    (P.rename ρ).domain k = (P.domain k).rename ρ := by
  simp only [SParams.domain, SType.rename, SFields.rename, SParams.toList_rename, Param.pos_map,
    Param.named_map, SType.list_rename, SFields.ofParams_rename]

theorem SParams.domains_rename (ρ : Nat → Nat) (P : SParams) :
    (P.rename ρ).domains = P.domains.map (·.rename ρ) := by
  simp only [SParams.domains, SParams.toList_rename, Param.counts_map, List.map_map]
  exact List.map_congr_left fun k _ => SParams.domain_rename ρ P k

theorem SType.IsRecSig.rename {ρ : Nat → Nat} : ∀ {b : SType}, b.IsRecSig → (b.rename ρ).IsRecSig
  | .record _ _, _ | .sig _, _ => trivial

/-! ## One step of justification -/

section
variable {ρ : Nat → Nat} {R R' : SType → SType → Prop}

theorem FieldR.rename (hR : ∀ a b, R a b → R' (a.rename ρ) (b.rename ρ)) {f g : SType} :
    FieldR R f g → FieldR R' (f.rename ρ) (g.rename ρ)
  | .refl => .refl
  | .toAbs => .toAbs
  | .misMis => .misMis
  | .misOpt => .misOpt
  | .optOpt h₀ h => .optOpt (SType.rename_ne_abs h₀) (hR _ _ h)
  | .preOpt h₀ h => .preOpt h₀.rename (hR _ _ h)
  | .pre h₀ h₁ h => .pre h₀.rename h₁.rename (hR _ _ h)

theorem FieldR.renPairs (hR : ∀ a b, R a b → R' (a.rename ρ) (b.rename ρ))
    {ps : List (SType × SType)} (h : ∀ p ∈ ps, FieldR R p.1 p.2) :
    ∀ p ∈ renPairs ρ ps, FieldR R' p.1 p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (h q hq).rename hR

theorem SFields.Rel.rename {Q Q' : SType → SType → Prop}
    (hQ : ∀ a b, Q a b → Q' (a.rename ρ) (b.rename ρ)) :
    ∀ {fs gs : SFields}, SFields.Rel Q fs gs → SFields.Rel Q' (fs.rename ρ) (gs.rename ρ)
  | _, _, .nil => .nil
  | _, _, .cons h r => .cons (hQ _ _ h) (r.rename hQ)

variable {σ σ' : Nat → Bounds}

theorem ExpandG.rename (hu : ∀ v b, b ∈ (σ v).upper → b.rename ρ ∈ (σ' (ρ v)).upper)
    (hR : ∀ a b, R a b → R' (a.rename ρ) (b.rename ρ)) {t t' : SType} {ms : SFields} :
    ExpandG σ R t ms t' → ExpandG σ' R' (t.rename ρ) (ms.rename ρ) (t'.rename ρ)
  | .none => .none
  | .abs hm h =>
    .abs (fun e => hm (SFields.rename_eq_nil.mp e))
      (by rw [SFields.absPairs_rename]; exact FieldR.renPairs hR h)
  | .nil hm h =>
    .nil (fun e => hm (SFields.rename_eq_nil.mp e))
      (by rw [SFields.misPairs_rename]; exact FieldR.renPairs hR h)
  | .varAbsent K h hp =>
    .varAbsent K
      (by rw [SFields.absentIn_rename, SFields.absPairs_rename]; exact FieldR.renPairs hR h)
      (by rw [SFields.presentIn_rename, hp]; rfl)
  | .var K hm h hp hub hrel =>
    .var K (fun e => hm (SFields.rename_eq_nil.mp e))
      (by rw [SFields.absentIn_rename, SFields.absPairs_rename]; exact FieldR.renPairs hR h)
      (by rw [SFields.presentIn_rename]; exact fun e => hp (SFields.rename_eq_nil.mp e))
      (hu _ _ hub)
      (by rw [SFields.presentIn_rename]; exact hrel.rename fun _ _ f => f.rename hR)

/-- **A renaming of a justified constraint is justified**, when the
renamed bounds are bounds of the renamed variables and the renamed
accepted constraints are accepted. -/
theorem GStep.rename (hu : ∀ v b, b ∈ (σ v).upper → b.rename ρ ∈ (σ' (ρ v)).upper)
    (hl : ∀ v b, b ∈ (σ v).lower → b.rename ρ ∈ (σ' (ρ v)).lower)
    (hR : ∀ a b, R a b → R' (a.rename ρ) (b.rename ρ)) {a b : SType} :
    GStep σ R a b → GStep σ' R' (a.rename ρ) (b.rename ρ)
  | .absR => .absR
  | .arrow h₁ h₂ => .arrow (hR _ _ h₁) (hR _ _ h₂)
  | .absRecord hf ht =>
    .absRecord (by rw [SFields.absPairs_rename]; exact FieldR.renPairs hR hf) (hR _ _ ht)
  | .nilRecord hf ht =>
    .nilRecord (by rw [SFields.misPairs_rename]; exact FieldR.renPairs hR hf) (hR _ _ ht)
  | .recordNil (fa := fa) (ta := ta) e₀ hf ht =>
    .recordNil (fs₀ := _) (t₀ := _)
      (by rw [← SType.rename, rowView_rename, e₀])
      (by rw [SFields.toMisPairs_rename]; exact FieldR.renPairs hR hf) (hR _ _ ht)
  | .record (fa := fa) (ta := ta) (fb := fb) (tb := tb) e₀ e₁ hf he ht =>
    .record (by rw [← SType.rename, rowView_rename, e₀]) (by rw [← SType.rename, rowView_rename, e₁])
      (fun l f₀ f₁ h₀ h₁ => by
        rw [SFields.lookup_rename] at h₀ h₁
        obtain ⟨g₀, e₀', rfl⟩ := Option.map_eq_some_iff.mp h₀
        obtain ⟨g₁, e₁', rfl⟩ := Option.map_eq_some_iff.mp h₁
        exact (hf l g₀ g₁ e₀' e₁').rename hR)
      (by rw [SFields.missing_rename]; exact he.rename hu hR)
      (by rw [SFields.missing_rename, ← restRow_rename]; exact hR _ _ ht)
  | .varL h => .varL (hu _ _ h)
  | .varR h => .varR (hl _ _ h)
  | .viaL h h₁ h₂ h₃ h₄ =>
    .viaL (hu _ _ h) (SType.rename_nonvar h₁) (SType.rename_ne_abs h₂) (SType.rename_nonvar h₃)
      (hR _ _ h₄)
  | .viaR h h₁ h₂ h₃ h₄ h₅ =>
    .viaR (hl _ _ h) (SType.rename_nonvar h₁) (SType.rename_ne_abs h₂) (SType.rename_nonvar h₃)
      (SType.rename_ne_abs h₄) (hR _ _ h₅)
  | .viaVar h₁ h₂ => .viaVar (hu _ _ h₁) (hl _ _ h₂)
  | .recordSig hd h =>
    .recordSig (by rw [SParams.domains_rename]; exact List.mem_map.mpr ⟨_, hd, rfl⟩) (hR _ _ h)
  | .sigL hb h =>
    .sigL hb.rename fun d hd => by
      rw [SParams.domains_rename] at hd
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
      exact hR _ _ (h d' hd')

end

end BoltCore.Alg
