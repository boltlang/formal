import BoltCore.PolyLet

/-!
# An example certificate with let-polymorphism

`let id = fun x -> x in id 1`, as inference would certify it: `id`'s
parameter variable `0` is generalized, the use instantiates it with the
copy `1`, and `2` is the type of the application. The accepted
constraints are the use's `1 → 1 ≤ int → 2` and what it decomposes and
propagates into: `int ≤ 1`, `1 ≤ 2` and `int ≤ 2`.

This checks that the conditions of `PTyp.sound_top` can be met by a
certificate with a non-trivial generalization. The proofs are by hand;
the executable checker (roadmap 6b) will decide such conditions.
-/

namespace BoltCore.Alg.Example

open BoltCore.Alg

def int : SType := .prim "int"

def cert : Certificate where
  log := [(.arrow (.var 1) (.var 1), .arrow int (.var 2)), (int, .var 1), (.var 1, .var 2),
    (int, .var 2)]
  vars := [(1, ⟨[int], [.var 2]⟩), (2, ⟨[int], []⟩)]
  kinds := []
  ranks := []

theorem bounds_eq (v : Nat) : cert.bounds v =
    if v = 1 then ⟨[int], [.var 2]⟩ else if v = 2 then ⟨[int], []⟩ else {} := by
  by_cases h1 : v = 1
  · subst h1; rfl
  · by_cases h2 : v = 2
    · subst h2; rfl
    · simp only [Certificate.bounds, cert, List.lookup, h1, h2, ite_false]
      have : (v == 1) = false := by simp [h1]
      have : (v == 2) = false := by simp [h2]
      simp [*]

theorem kind_eq (v : Nat) : cert.kind v = [] := rfl

theorem rank_eq (v : Nat) : cert.rank v = 0 := rfl

theorem mem_log {p : SType × SType} (h : p ∈ cert.log) :
    p = (.arrow (.var 1) (.var 1), .arrow int (.var 2)) ∨ p = (int, .var 1) ∨
      p = (.var 1, .var 2) ∨ p = (int, .var 2) := by
  simpa [cert] using h

theorem logged₁ : Logged cert.state int (.var 1) := .inr (by simp [Certificate.state, cert])
theorem logged₂ : Logged cert.state (.var 1) (.var 2) := .inr (by simp [Certificate.state, cert])
theorem logged₃ : Logged cert.state int (.var 2) := .inr (by simp [Certificate.state, cert])

theorem valid : cert.Valid := by
  have hb : ∀ v, (cert.state.bounds v) = cert.bounds v := fun _ => rfl
  refine ⟨⟨fun p hp => .inr ?_, fun v l u hl hu => ?_⟩, ⟨fun v x hx => ?_, fun v x hx => ?_⟩,
    fun p hp => ?_, fun p hp => ?_, fun v b hvb => ?_⟩
  · -- every accepted constraint is justified
    rcases mem_log hp with rfl | rfl | rfl | rfl
    · exact .arrow logged₁ logged₂
    · exact .varR (by rw [hb, bounds_eq]; simp)
    · exact .varL (by rw [hb, bounds_eq]; simp)
    · exact .varR (by rw [hb, bounds_eq]; simp)
  · -- consistency
    rw [hb, bounds_eq] at hl hu
    by_cases h1 : v = 1
    · subst h1; simp at hl hu; subst hl hu; exact .inl logged₃
    · by_cases h2 : v = 2
      · subst h2; simp at hu
      · simp [h1, h2] at hl
  · -- bounds are accepted constraints
    rw [hb, bounds_eq] at hx
    by_cases h1 : v = 1
    · subst h1; simp at hx; subst hx; simp [Certificate.state, cert]
    · by_cases h2 : v = 2
      · subst h2; simp at hx
      · simp [h1, h2] at hx
  · rw [hb, bounds_eq] at hx
    by_cases h1 : v = 1
    · subst h1; simp at hx; subst hx; simp [Certificate.state, cert]
    · by_cases h2 : v = 2
      · subst h2; simp at hx; subst hx; simp [Certificate.state, cert]
      · simp [h1, h2] at hx
  · -- `Abs` is never a function component
    rcases mem_log hp with rfl | rfl | rfl | rfl <;>
      simp [SType.NAC, int]
  · -- the kind discipline (all kinds are empty)
    have e : ∀ v, KEmpty cert.kind (.var v) := fun _ => KEmpty.var_nil rfl
    have nva : ∀ a b w, (rowView (SType.arrow a b)).2 ≠ .var w := fun _ _ _ h => by
      simp [rowView] at h
    have nvp : ∀ n w, (rowView (SType.prim n)).2 ≠ .var w := fun _ _ h => by simp [rowView] at h
    rcases mem_log hp with rfl | rfl | rfl | rfl
    · exact ⟨⟨trivial, e 1, trivial, e 1⟩, ⟨trivial, .of_nonvar (nvp _), trivial, e 2⟩,
        .of_nonvarL (nva _ _)⟩
    · exact ⟨trivial, trivial, .of_nonvarL (nvp _)⟩
    · exact ⟨trivial, trivial, .of_empty (e 1) (e 2)⟩
    · exact ⟨trivial, trivial, .of_nonvarL (nvp _)⟩
  · -- no structural recursive types
    rw [bounds_eq] at hvb
    simp only [rank_eq]
    by_cases h1 : v = 1
    · subst h1
      simp at hvb
      rcases hvb with rfl | rfl
      · exact ⟨fun _ _ => Nat.le_refl _, fun h => absurd rfl (h 2)⟩
      · exact ⟨fun _ _ => Nat.le_refl _, fun _ w hw => by simp [SType.vars, int] at hw⟩
    · by_cases h2 : v = 2
      · subst h2
        simp at hvb
        subst hvb
        exact ⟨(fun _ h => nomatch h), fun _ w hw => by simp [SType.vars, int] at hw⟩
      · simp [h1, h2] at hvb

/-- The skeleton: `id : ∀0. 0 ≤ ⊤ ⇒ 0 → 0` (`0` is an ordinary type
variable, so its instances are types), used at the copy `1`. -/
def ρ : Nat → Nat := fun v => if v = 0 then 1 else v

def prog : Term :=
  .letIn false "id" (.lam "x" (.var "x")) (.app (.var "id") (.lit 1))

theorem skeleton : PTyp cert [] prog (.var 2) := by
  refine .letIn (gen := [0]) (str := .arrow (.var 0) (.var 0)) (.lam (.var rfl)) ⟨?_, ?_⟩ ?_
  · -- no other variable's bounds mention `0`
    intro v hv b hb w hw
    rw [bounds_eq] at hb
    simp only [List.mem_singleton]
    by_cases h1 : v = 1
    · subst h1; simp at hb
      rcases hb with rfl | rfl <;> simp [SType.vars, int] at hw <;> omega
    · by_cases h2 : v = 2
      · subst h2; simp at hb; subst hb; simp [SType.vars, int] at hw
      · simp [h1, h2] at hb
  · intro p hp; nomatch hp
  · have hinst : PTyp cert [("id", .poly [0] (.arrow (.var 0) (.var 0)))] (.var "id")
        (.arrow (.var 1) (.var 1)) :=
      .inst (gen := [0]) (st := .arrow (.var 0) (.var 0)) (ρ := ρ) rfl ⟨fun v hv => by
          simp only [List.mem_singleton] at hv; simp [ρ, hv],
        fun _ _ => rfl,
        fun α hα u hu => by
          simp only [List.mem_singleton] at hα; subst hα; rw [bounds_eq] at hu
          simp at hu,
        fun α hα l hl => by
          simp only [List.mem_singleton] at hα; subst hα; rw [bounds_eq] at hl
          simp at hl⟩
    exact .app hinst .lit (fun h => nomatch h) (.inr (by simp [cert, int]))

/-- `id 1 : θ(2)`, in the declarative system, with `id` given the scheme
`∀0. 0 ≤ ⊤ ⇒ 0 → 0` by the generalizing `let`. -/
theorem typed : Typ (defsOf cert.state) [] prog (.gvar 2) :=
  PTyp.sound_top valid skeleton

/-! ## A constrained example

`let inc = fun x -> succ x in inc 1`:
`inc : ∀0 3. 0 ≤ int, int ≤ 3, 0 ≤ ⊤, 3 ≤ ⊤ ⇒ 0 → 3`, used at the copies `1`
and `4` of `0` and `3`, which carry the renamed bounds `1 ≤ int` and
`int ≤ 4`; `2` is the result. -/

namespace Constrained

open BoltCore.Alg.Example (int)

def cert : Certificate where
  log := [(.arrow int int, .arrow (.var 0) (.var 3)), (.var 0, int), (int, .var 3),
    (.var 1, int), (int, .var 4),
    (.arrow (.var 1) (.var 4), .arrow int (.var 2)), (int, .var 1), (.var 4, .var 2),
    (int, .var 2)]
  vars := [(0, ⟨[], [int]⟩), (3, ⟨[int], []⟩), (1, ⟨[int], [int]⟩), (4, ⟨[int], [.var 2]⟩),
    (2, ⟨[int], []⟩)]
  kinds := []
  ranks := []

/-- A bound comes from one of the listed entries. -/
theorem mem_bounds {v : Nat} {x : SType} (h : x ∈ (cert.bounds v).upper ∨ x ∈ (cert.bounds v).lower) :
    ∃ b, (v, b) ∈ cert.vars ∧ (x ∈ b.upper ∨ x ∈ b.lower) := by
  simp only [Certificate.bounds] at h
  cases hl : cert.vars.lookup v with
  | none => simp [hl] at h
  | some b =>
    rw [hl] at h
    refine ⟨b, ?_, h⟩
    clear h
    revert hl
    generalize cert.vars = l
    intro hl
    induction l with
    | nil => simp [List.lookup] at hl
    | cons p l ih =>
      obtain ⟨k, b'⟩ := p
      simp only [List.lookup] at hl
      split at hl
      · next he => cases hl; rw [beq_iff_eq.mp he]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hl)

theorem bound_of {v : Nat} {b : Bounds} (h : (v, b) ∈ cert.vars) : cert.bounds v = b := by
  simp [cert] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem logged {a b : SType} (h : (a, b) ∈ cert.log) : Logged cert.state a b := .inr h

theorem valid : cert.Valid := by
  have e : ∀ v, KEmpty cert.kind (.var v) := fun _ => KEmpty.var_nil rfl
  have nva : ∀ a b w, (rowView (SType.arrow a b)).2 ≠ .var w := fun _ _ _ h => by
    simp [rowView] at h
  have nvp : ∀ n w, (rowView (SType.prim n)).2 ≠ .var w := fun _ _ h => by simp [rowView] at h
  have bnd : ∀ v b, (v, b) ∈ cert.vars → cert.state.bounds v = b := fun _ _ h => bound_of h
  refine ⟨⟨fun p hp => .inr ?_, fun v l u hl hu => ?_⟩, ⟨fun v x hx => ?_, fun v x hx => ?_⟩,
    fun p hp => ?_, fun p hp => ?_, fun v b hvb => ?_⟩
  · simp only [Certificate.state, cert, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .arrow (logged (by simp [cert])) (logged (by simp [cert]))
    · exact .varL (by simp [Certificate.state, Certificate.bounds, cert, List.lookup])
    · exact .varR (by simp [Certificate.state, Certificate.bounds, cert, List.lookup])
    · exact .varL (by simp [Certificate.state, Certificate.bounds, cert, List.lookup])
    · exact .varR (by simp [Certificate.state, Certificate.bounds, cert, List.lookup])
    · exact .arrow (logged (by simp [cert])) (logged (by simp [cert]))
    · exact .varR (by simp [Certificate.state, Certificate.bounds, cert, List.lookup])
    · exact .varL (by simp [Certificate.state, Certificate.bounds, cert, List.lookup])
    · exact .varR (by simp [Certificate.state, Certificate.bounds, cert, List.lookup])
  · obtain ⟨b, hb, _⟩ := mem_bounds (.inr hl)
    rw [show cert.state.bounds v = b from bnd v b hb] at hl hu
    simp [cert] at hb
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp at hl hu
    · subst hl hu; exact .inl (.inl rfl)
    · subst hl hu; exact .inl (logged (by simp [cert]))
  · obtain ⟨b, hb, _⟩ := mem_bounds (.inl hx)
    rw [show cert.state.bounds v = b from bnd v b hb] at hx
    simp [cert] at hb
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp at hx <;> subst hx <;> simp [Certificate.state, cert]
  · obtain ⟨b, hb, _⟩ := mem_bounds (.inr hx)
    rw [show cert.state.bounds v = b from bnd v b hb] at hx
    simp [cert] at hb
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp at hx <;> subst hx <;> simp [Certificate.state, cert]
  · simp only [Certificate.state, cert, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SType.NAC, int]
  · simp only [Certificate.state, cert, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨trivial, .of_nonvar (nvp _), trivial, .of_nonvar (nvp _)⟩,
        ⟨trivial, e 0, trivial, e 3⟩, .of_nonvarL (nva _ _)⟩
    · exact ⟨trivial, trivial, .of_nonvarR (nvp _)⟩
    · exact ⟨trivial, trivial, .of_nonvarL (nvp _)⟩
    · exact ⟨trivial, trivial, .of_nonvarR (nvp _)⟩
    · exact ⟨trivial, trivial, .of_nonvarL (nvp _)⟩
    · exact ⟨⟨trivial, e 1, trivial, e 4⟩, ⟨trivial, .of_nonvar (nvp _), trivial, e 2⟩,
        .of_nonvarL (nva _ _)⟩
    · exact ⟨trivial, trivial, .of_nonvarL (nvp _)⟩
    · exact ⟨trivial, trivial, .of_empty (e 4) (e 2)⟩
    · exact ⟨trivial, trivial, .of_nonvarL (nvp _)⟩
  · obtain ⟨b', hb, hx⟩ := mem_bounds hvb
    have hr : ∀ w, cert.rank w = 0 := fun _ => rfl
    simp only [hr]
    simp [cert] at hb
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp at hx <;> rcases hx with rfl | rfl <;>
      first
      | exact ⟨fun _ _ => Nat.le_refl _, fun h => absurd rfl (h 2)⟩
      | exact ⟨(fun _ h => nomatch h), fun _ w hw => by simp [SType.vars, int] at hw⟩

def ρ : Nat → Nat := fun v => if v = 0 then 1 else if v = 3 then 4 else v

def prog : Term :=
  .letIn false "inc" (.lam "x" (.app (.var "succ") (.var "x"))) (.app (.var "inc") (.lit 1))

def Γ : PCtx := [("succ", .mono (.arrow int int))]

theorem skeleton : PTyp cert Γ prog (.var 2) := by
  refine .letIn (gen := [0, 3]) (str := .arrow (.var 0) (.var 3))
    (.lam (.app (.var rfl) (.var rfl) (fun h => nomatch h) (.inr (by simp [cert]))))
    ⟨?_, ?_⟩ ?_
  · -- no other variable's bounds mention `0` or `3`
    intro v hv b hb w hw
    obtain ⟨b', hb', hx⟩ := mem_bounds hb
    simp [cert] at hb'
    rcases hb' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp at hv hx <;> (try rcases hx with rfl | rfl) <;> simp [SType.vars, int] at hw ⊢ <;>
      omega
  · -- nor does the context
    intro p hp
    simp [Γ] at hp
    subst hp
    intro w hw
    simp [SType.vars, int] at hw
  · have hinst : PTyp cert (("inc", .poly [0, 3] (.arrow (.var 0) (.var 3))) :: Γ) (.var "inc")
        (.arrow (.var 1) (.var 4)) :=
      .inst (gen := [0, 3]) (st := .arrow (.var 0) (.var 3)) (ρ := ρ) rfl ⟨fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
          simp [ρ, hv.1, hv.2],
        fun _ _ => rfl,
        fun α hα u hu => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
          rcases hα with rfl | rfl
          · rw [bound_of (by simp [cert] : ((0 : Nat), (⟨[], [int]⟩ : Bounds)) ∈ cert.vars)] at hu
            simp at hu; subst hu
            exact .inr (by simp [cert, ρ, int, SType.rename])
          · rw [bound_of (by simp [cert] : ((3 : Nat), (⟨[int], []⟩ : Bounds)) ∈ cert.vars)] at hu
            simp at hu,
        fun α hα l hl => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
          rcases hα with rfl | rfl
          · rw [bound_of (by simp [cert] : ((0 : Nat), (⟨[], [int]⟩ : Bounds)) ∈ cert.vars)] at hl
            simp at hl
          · rw [bound_of (by simp [cert] : ((3 : Nat), (⟨[int], []⟩ : Bounds)) ∈ cert.vars)] at hl
            simp at hl; subst hl
            exact .inr (by simp [cert, ρ, int, SType.rename])⟩
    exact .app hinst .lit (fun h => nomatch h) (.inr (by simp [cert, int]))

/-- `inc 1 : θ(2)`, with `inc` given the constrained scheme
`∀0 3. 0 ≤ int, int ≤ 3, 0 ≤ ⊤, 3 ≤ ⊤ ⇒ 0 → 3` by the generalizing `let`. -/
theorem typed : Typ (defsOf cert.state) (Γ.toCtx cert.bounds cert.kind .gvar) prog (.gvar 2) :=
  PTyp.sound_top valid skeleton

end Constrained

end BoltCore.Alg.Example
