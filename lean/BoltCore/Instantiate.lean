import BoltCore.Levels
import BoltCore.ExtrusionSound

/-!
# Instantiation

What instantiating a scheme does to a state (`State.instantiate`): the
state grows, the bounds of the copies are logged, the state stays in
scope, consistent and with bounds of the right levels, and a closed set of
variables that contains the copies and what the scheme mentions stays
closed.
-/

namespace BoltCore.Alg

open State

section
variable {s : State} {lvl : Nat} {gen : List Nat} {ρ : Nat → Nat}

/-! ## The bounds after an instantiation -/

theorem find?_unique {l : List Nat} {p : Nat → Bool} {a : Nat} :
    a ∈ l → p a = true → (∀ b ∈ l, p b = true → b = a) → l.find? p = some a := by
  intro ha hp hu
  induction l with
  | nil => exact nomatch ha
  | cons x xs ih =>
    simp only [List.find?_cons]
    cases hx : p x with
    | true => rw [hu x (List.mem_cons_self ..) hx]
    | false =>
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [hp] at hx; exact nomatch hx
      · exact ih ha' fun b hb => hu b (List.mem_cons_of_mem _ hb)

/-- The bounds of a copy: the renamed bounds of its original, before what
it had. -/
theorem bounds_instantiate_copy (hi : IsInst s lvl gen ρ) {α : Nat} (hα : α ∈ gen) :
    (s.instantiate gen ρ).bounds (ρ α) =
      ⟨(s.bounds α).lower.map (·.rename ρ) ++ (s.bounds (ρ α)).lower,
        (s.bounds α).upper.map (·.rename ρ) ++ (s.bounds (ρ α)).upper⟩ := by
  have : gen.find? (fun β => ρ β = ρ α) = some α :=
    find?_unique hα (by simp) fun β hβ h => hi.inj β hβ α hα (by simpa using h)
  simp only [State.instantiate, this]

/-- The bounds of a variable that is not a copy are unchanged. -/
theorem bounds_instantiate_other {w : Nat} (h : ∀ α ∈ gen, ρ α ≠ w) :
    (s.instantiate gen ρ).bounds w = s.bounds w := by
  have : gen.find? (fun α => ρ α = w) = none :=
    List.find?_eq_none.mpr fun α hα => by simpa using h α hα
  simp only [State.instantiate, this]

/-- An upper bound after an instantiation: a renamed bound of the original
of a copy, or a bound from before. -/
theorem mem_upper_instantiate {w : Nat} {x : SType}
    (hx : x ∈ ((s.instantiate gen ρ).bounds w).upper) :
    (∃ α ∈ gen, ρ α = w ∧ ∃ u ∈ (s.bounds α).upper, x = u.rename ρ) ∨ x ∈ (s.bounds w).upper := by
  simp only [State.instantiate] at hx
  split at hx
  · next α hf =>
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact .inl ⟨α, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, u, hu, rfl⟩
    · exact .inr hx
  · exact .inr hx

theorem mem_lower_instantiate {w : Nat} {x : SType}
    (hx : x ∈ ((s.instantiate gen ρ).bounds w).lower) :
    (∃ α ∈ gen, ρ α = w ∧ ∃ l ∈ (s.bounds α).lower, x = l.rename ρ) ∨ x ∈ (s.bounds w).lower := by
  simp only [State.instantiate] at hx
  split at hx
  · next α hf =>
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      exact .inl ⟨α, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, l, hl, rfl⟩
    · exact .inr hx
  · exact .inr hx

/-- A copy has the renamed bounds of its original. -/
theorem mem_upper_copy (hi : IsInst s lvl gen ρ) {α : Nat} (hα : α ∈ gen) {u : SType}
    (hu : u ∈ (s.bounds α).upper) : u.rename ρ ∈ ((s.instantiate gen ρ).bounds (ρ α)).upper := by
  rw [bounds_instantiate_copy hi hα]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨u, hu, rfl⟩)

theorem mem_lower_copy (hi : IsInst s lvl gen ρ) {α : Nat} (hα : α ∈ gen) {l : SType}
    (hl : l ∈ (s.bounds α).lower) : l.rename ρ ∈ ((s.instantiate gen ρ).bounds (ρ α)).lower := by
  rw [bounds_instantiate_copy hi hα]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩)

theorem Grows.instantiate : Grows s (s.instantiate gen ρ) := by
  refine ⟨fun w x h => ?_, fun w x h => ?_, fun _ h => List.mem_append_right _ h, fun _ h => h,
    rfl, rfl⟩
  · simp only [State.instantiate]; split
    · exact List.mem_append_right _ h
    · exact h
  · simp only [State.instantiate]; split
    · exact List.mem_append_right _ h
    · exact h

/-- A renamed accepted constraint is accepted after the instantiation. -/
theorem Logged.instantiate {a b : SType} (h : Logged s a b) :
    Logged (s.instantiate gen ρ) (a.rename ρ) (b.rename ρ) := by
  rcases h with rfl | h
  · exact .inl rfl
  · exact .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, b), h, rfl⟩))

/-! ## Invariants -/

theorem BoundsInLog.instantiate (h : BoundsInLog s) : BoundsInLog (s.instantiate gen ρ) := by
  refine ⟨fun w x hx => ?_, fun w x hx => ?_⟩
  · rcases mem_upper_instantiate hx with ⟨α, _, rfl, u, hu, rfl⟩ | hx
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨(.var α, u), h.1 α u hu, rfl⟩)
    · exact List.mem_append_right _ (h.1 w x hx)
  · rcases mem_lower_instantiate hx with ⟨α, _, rfl, l, hl, rfl⟩ | hx
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨(l, .var α), h.2 α l hl, rfl⟩)
    · exact List.mem_append_right _ (h.2 w x hx)

/-- A renamed type in scope is in scope after the instantiation. -/
theorem in_scope_rename (hi : IsInst s lvl gen ρ) {t : SType} (ht : t.In (· < s.next)) :
    (t.rename ρ).In (· < s.next + gen.length) :=
  SType.in_rename fun w hw => by
    by_cases hg : w ∈ gen
    · exact (hi.fresh w hg).2
    · rw [hi.fix w hg]; exact Nat.lt_of_lt_of_le (ht w hw) (Nat.le_add_right _ _)

theorem Scope.instantiate (hs : Scope s) (hi : IsInst s lvl gen ρ) :
    Scope (s.instantiate gen ρ) := by
  have hn : s.next ≤ s.next + gen.length := Nat.le_add_right _ _
  refine ⟨fun w x hx => ?_, fun e he => Nat.lt_of_lt_of_le (hs.exps e he) hn, hs.expLevel⟩
  rcases hx with hx | hx
  · rcases mem_upper_instantiate hx with ⟨α, hα, rfl, u, hu, rfl⟩ | hx
    · exact ⟨(hi.fresh α hα).2, in_scope_rename hi (hs.bounds α u (.inl hu)).2⟩
    · exact ⟨Nat.lt_of_lt_of_le (hs.bounds w x (.inl hx)).1 hn,
        (hs.bounds w x (.inl hx)).2.scope_mono hn⟩
  · rcases mem_lower_instantiate hx with ⟨α, hα, rfl, l, hl, rfl⟩ | hx
    · exact ⟨(hi.fresh α hα).2, in_scope_rename hi (hs.bounds α l (.inr hl)).2⟩
    · exact ⟨Nat.lt_of_lt_of_le (hs.bounds w x (.inr hx)).1 hn,
        (hs.bounds w x (.inr hx)).2.scope_mono hn⟩

/-- Instantiation keeps the bounds consistent: a copy is fresh, so its
bounds are the renamed bounds of its original, which were consistent. -/
theorem Consistent.instantiate (h : Consistent s) (hs : Scope s) (hi : IsInst s lvl gen ρ) :
    Consistent (s.instantiate gen ρ) := by
  intro w l u hl hu
  rcases mem_lower_instantiate hl with ⟨α, hα, rfl, l₀, hl₀, rfl⟩ | hl
  · rcases mem_upper_instantiate hu with ⟨β, hβ, e, u₀, hu₀, rfl⟩ | hu
    · have := hi.inj β hβ α hα e
      subst this
      rcases h β l₀ u₀ hl₀ hu₀ with hlog | hp
      · exact .inl hlog.instantiate
      · exact nomatch hp
    · exact absurd (hs.bounds _ u (.inl hu)).1 (Nat.not_lt.mpr (hi.fresh α hα).1)
  · rcases mem_upper_instantiate hu with ⟨β, hβ, rfl, u₀, hu₀, rfl⟩ | hu
    · exact absurd (hs.bounds _ l (.inr hl)).1 (Nat.not_lt.mpr (hi.fresh β hβ).1)
    · rcases h w l u hl hu with hlog | hp
      · exact .inl (hlog.mono .instantiate)
      · exact nomatch hp

/-! ## Schemes and closed sets -/

/-- The variables a scheme mentions, other than its generalized ones, are
in `X`: those of its type, and those of the bounds of its generalized
variables. -/
structure SchemeIn (X : Nat → Prop) (s : State) (gen : List Nat) (st : SType) : Prop where
  ty : ∀ w ∈ st.vars, w ∉ gen → X w
  bounds : ∀ α ∈ gen, ∀ b, (b ∈ (s.bounds α).upper ∨ b ∈ (s.bounds α).lower) →
    ∀ w ∈ b.vars, w ∉ gen → X w

variable {X : Nat → Prop}

/-- A renamed type is in `X` when the copies are, and its other variables. -/
theorem in_rename_of (hi : IsInst s lvl gen ρ) (hc : ∀ α ∈ gen, X (ρ α)) {t : SType}
    (ht : ∀ w ∈ t.vars, w ∉ gen → X w) : (t.rename ρ).In X :=
  SType.in_rename fun w hw => by
    by_cases hg : w ∈ gen
    · exact hc w hg
    · rw [hi.fix w hg]; exact ht w hw hg

/-- **Locality of instantiation.** -/
theorem Local.instantiate {st : SType} (hx : XClosed X s) (hi : IsInst s lvl gen ρ)
    (hc : ∀ α ∈ gen, X (ρ α)) (hsch : SchemeIn X s gen st) : Local X s (s.instantiate gen ρ) := by
  refine ⟨fun v hv b hb => ?_, fun v hv => bounds_instantiate_other fun α hα e => hv (e ▸ hc α hα)⟩
  rcases hb with hb | hb
  · rcases mem_upper_instantiate hb with ⟨α, hα, _, u, hu, rfl⟩ | hb
    · exact in_rename_of hi hc (hsch.bounds α hα u (.inl hu))
    · exact hx v hv b (.inl hb)
  · rcases mem_lower_instantiate hb with ⟨α, hα, _, l, hl, rfl⟩ | hb
    · exact in_rename_of hi hc (hsch.bounds α hα l (.inr hl))
    · exact hx v hv b (.inr hb)

/-- Instantiation at `lvl` keeps the levels of bounds, when the scheme
only mentions variables of level at most `lvl`. -/
theorem LevelInv.instantiate {st : SType} (h : LevelInv s) (hi : IsInst s lvl gen ρ)
    (hsch : SchemeIn (fun w => s.level w ≤ lvl) s gen st) : LevelInv (s.instantiate gen ρ) := by
  have hc : ∀ α ∈ gen, s.level (ρ α) ≤ lvl := fun α hα => Nat.le_of_eq (hi.level α hα)
  intro w b hb
  rcases hb with hb | hb
  · rcases mem_upper_instantiate hb with ⟨α, hα, rfl, u, hu, rfl⟩ | hb
    · show (u.rename ρ).level s.level ≤ s.level (ρ α)
      rw [hi.level α hα]
      exact SType.level_le.mpr (in_rename_of hi hc (hsch.bounds α hα u (.inl hu)))
    · exact h w b (.inl hb)
  · rcases mem_lower_instantiate hb with ⟨α, hα, rfl, l, hl, rfl⟩ | hb
    · show (l.rename ρ).level s.level ≤ s.level (ρ α)
      rw [hi.level α hα]
      exact SType.level_le.mpr (in_rename_of hi hc (hsch.bounds α hα l (.inr hl)))
    · exact h w b (.inr hb)

end

end BoltCore.Alg
