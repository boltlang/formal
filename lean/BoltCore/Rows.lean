/-!
# The row algebra

Rows are fieldwise: a row `{l₁: f₁, …, lₙ: fₙ | t}` denotes the total map
sending `lᵢ` to `fᵢ` and every other label to whatever the tail `t` gives
it. Unions and intersections of rows are pointwise. This file models rows
at that level of abstraction, over an arbitrary type `F` of field values,
and proves that the row rewrites performed by the OCaml implementation
preserve the denotation:

* `merge_exact`: merging two rows (`add_row` in `lib/simplify.ml`,
  `merge_rows` in `lib/subsume.ml`) is exact under the "covers" condition
  (every label missing from one row is supplied by that row's `Abs` tail).
* `merge_inexact`: without the condition, merging is wrong in general.
* `combine_sound`: the way `merge_rows` combines two atomic tails is
  pointwise meet/join, given the lattice laws for `Abs` (top) and `⊥`.
* `drop_abs_fields`: dropping `Abs` fields from a row whose tail is `Abs`
  (`mk_row`) preserves the denotation, given distinct labels.
* `flatten`: a row whose tail is another row is that row with the fields
  appended (`mk_row`, `row_view`, `norm_row`).
-/

namespace BoltCore.Rows

variable {F : Type}

/-- The first binding of a label. -/
def find? (l : String) : List (String × F) → Option F
  | [] => none
  | (n, f) :: fs => if n = l then some f else find? l fs

def labels (fs : List (String × F)) : List String := fs.map Prod.fst

/-- A row: explicit fields over a tail. -/
structure Row (F : Type) where
  fields : List (String × F)
  tail : String → F

/-- The field a row gives a label: explicit fields override the tail. -/
def Row.at (r : Row F) (l : String) : F := (find? l r.fields).getD (r.tail l)

/-! ## Lookup lemmas -/

theorem isSome_find_iff (l : String) (fs : List (String × F)) :
    (find? l fs).isSome ↔ l ∈ labels fs := by
  induction fs with
  | nil => simp [find?, labels]
  | cons p fs ih =>
    obtain ⟨n, f⟩ := p
    by_cases h : n = l
    · subst h; simp [find?, labels]
    · have h' : l ≠ n := fun e => h e.symm
      simp only [labels] at ih
      simp [find?, labels, h, h', ih]

theorem find_eq_none (l : String) (fs : List (String × F)) (h : l ∉ labels fs) :
    find? l fs = none := by
  cases e : find? l fs with
  | none => rfl
  | some _ => exact absurd ((isSome_find_iff l fs).mp (by simp [e])) h

theorem mem_labels_of_find (l : String) (fs : List (String × F)) (f : F)
    (h : find? l fs = some f) : l ∈ labels fs :=
  (isSome_find_iff l fs).mp (by simp [h])

theorem find_map (g : String → F) (ns : List String) (l : String) :
    find? l (ns.map fun n => (n, g n)) = if l ∈ ns then some (g l) else none := by
  induction ns with
  | nil => simp [find?]
  | cons n ns ih =>
    by_cases h : n = l
    · subst h; simp [find?]
    · have h' : l ≠ n := fun e => h e.symm
      simp [find?, h, h', ih]

theorem find_append (l : String) (a b : List (String × F)) :
    find? l (a ++ b) = match find? l a with
      | some f => some f
      | none => find? l b := by
  induction a with
  | nil => simp [find?]
  | cons p a ih =>
    obtain ⟨n, f⟩ := p
    by_cases h : n = l
    · simp [find?, h]
    · simp [find?, h, ih]

/-! ## Merging rows -/

/-- Merge two rows field by field with `op` (meet or join), using `absF` for
a label a row does not list. Mirrors `add_row` (`lib/simplify.ml`) and
`merge_rows` (`lib/subsume.ml`); `tail` is the combined tail. -/
def merge (op : F → F → F) (absF : F) (r0 r1 : Row F) (tail : String → F) : Row F where
  fields := (labels r0.fields ++ labels r1.fields).map fun n =>
    (n, op ((find? n r0.fields).getD absF) ((find? n r1.fields).getD absF))
  tail := tail

/-- `r0` knows every label `r1` lists: either `r0`'s tail is `Abs`
everywhere, or `r0` lists the label explicitly. -/
def Covers (absF : F) (r0 r1 : Row F) : Prop :=
  (∀ l, r0.tail l = absF) ∨ (∀ l, l ∈ labels r1.fields → l ∈ labels r0.fields)

/-- **Merging is exact under mutual covering**: the merged row gives every
label exactly `op` of what the two rows give it. No lattice laws are needed
for the fields: a row that does not list a label gives it `Abs` precisely
because its tail is `Abs`. -/
theorem merge_exact (op : F → F → F) (absF : F) (r0 r1 : Row F) (tail : String → F)
    (h01 : Covers absF r0 r1) (h10 : Covers absF r1 r0)
    (ht : ∀ l, tail l = op (r0.tail l) (r1.tail l)) (l : String) :
    (merge op absF r0 r1 tail).at l = op (r0.at l) (r1.at l) := by
  simp only [Row.at, merge, find_map, List.mem_append]
  cases h0 : find? l r0.fields with
  | some f0 =>
    have m0 := mem_labels_of_find l _ f0 h0
    cases h1 : find? l r1.fields with
    | some f1 => simp [m0]
    | none =>
      rcases h10 with t1 | sub
      · simp [m0, t1]
      · have := (isSome_find_iff l _).mpr (sub l m0)
        simp [h1] at this
  | none =>
    cases h1 : find? l r1.fields with
    | some f1 =>
      have m1 := mem_labels_of_find l _ f1 h1
      rcases h01 with t0 | sub
      · simp [m1, t0]
      · have := (isSome_find_iff l _).mpr (sub l m1)
        simp [h0] at this
    | none =>
      have n0 : l ∉ labels r0.fields := fun m => by
        have := (isSome_find_iff l _).mpr m; simp [h0] at this
      have n1 : l ∉ labels r1.fields := fun m => by
        have := (isSome_find_iff l _).mpr m; simp [h1] at this
      simp [n0, n1, ht]

/-- **The covering condition is necessary**: merging `{x: a | ρ₀}` with
`{ | ρ₁}` (where `ρ₁` gives `x` something other than `Abs`) is wrong at
`x`, for any `op` that is not constant in its second argument. This is the
merge that the mutation test (merging rows unconditionally) introduced. -/
theorem merge_inexact (op : F → F → F) (absF a b : F) (ρ₀ : String → F)
    (hop : op a absF ≠ op a b) :
    let r0 : Row F := ⟨[("x", a)], ρ₀⟩
    let r1 : Row F := ⟨[], fun _ => b⟩
    (merge op absF r0 r1 (fun l => op (r0.tail l) (r1.tail l))).at "x"
      ≠ op (r0.at "x") (r1.at "x") := by
  simp [Row.at, merge, labels, find?, hop]

/-! ## Combining atomic tails -/

/-- Atomic row tails, as in `lib/subsume.ml`: the top row `Abs`, the bottom
row, and row variables. -/
inductive Tail where
  | abs
  | bot
  | var (n : Nat)
  deriving DecidableEq

/-- The lattice structure the field values must have. -/
structure Laws (F : Type) where
  meet : F → F → F
  join : F → F → F
  absF : F
  botF : F
  meet_idem : ∀ x, meet x x = x
  join_idem : ∀ x, join x x = x
  meet_abs_l : ∀ x, meet absF x = x
  meet_abs_r : ∀ x, meet x absF = x
  join_abs_l : ∀ x, join absF x = absF
  join_abs_r : ∀ x, join x absF = absF
  meet_bot_l : ∀ x, meet botF x = botF
  meet_bot_r : ∀ x, meet x botF = botF
  join_bot_l : ∀ x, join botF x = x
  join_bot_r : ∀ x, join x botF = x

/-- What a tail gives each label, for a valuation `ρ` of row variables. -/
def Tail.at (L : Laws F) (ρ : Nat → String → F) : Tail → String → F
  | .abs, _ => L.absF
  | .bot, _ => L.botF
  | .var n, l => ρ n l

/-- Combine two tails of a meet (`inter`) or join into one atomic tail, if
possible. Mirrors the `tail` helper of `merge_rows` in `lib/subsume.ml`. -/
def combine (inter : Bool) (t0 t1 : Tail) : Option Tail :=
  if t0 = t1 then some t0
  else if inter then
    match t0, t1 with
    | .abs, t => some t
    | t, .abs => some t
    | .bot, _ => some .bot
    | _, .bot => some .bot
    | _, _ => none
  else
    match t0, t1 with
    | .bot, t => some t
    | t, .bot => some t
    | .abs, _ => some .abs
    | _, .abs => some .abs
    | _, _ => none

/-- **Combining tails is exact**: whenever `combine` succeeds, the result is
the pointwise meet/join of the two tails. -/
theorem combine_sound (L : Laws F) (ρ : Nat → String → F) (inter : Bool)
    (t0 t1 t : Tail) (h : combine inter t0 t1 = some t) (l : String) :
    t.at L ρ l = (if inter then L.meet else L.join) (t0.at L ρ l) (t1.at L ρ l) := by
  unfold combine at h
  by_cases he : t0 = t1
  · subst he
    simp at h
    subst h
    cases inter <;> simp [L.meet_idem, L.join_idem]
  · simp only [he, ite_false] at h
    cases inter <;> cases t0 <;> cases t1 <;>
      simp_all [Tail.at, L.meet_abs_l, L.meet_abs_r, L.join_abs_l, L.join_abs_r,
        L.meet_bot_l, L.meet_bot_r, L.join_bot_l, L.join_bot_r] <;>
      (subst h; rfl)

/-! ## Dropping `Abs` fields and flattening -/

theorem labels_filter (p : String × F → Bool) (fs : List (String × F)) (l : String)
    (h : l ∈ labels (fs.filter p)) : l ∈ labels fs := by
  simp only [labels, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨q, ⟨hq, _⟩, rfl⟩ := h
  exact ⟨q, hq, rfl⟩

/-- **Dropping `Abs` fields is exact when the tail is `Abs`** (`mk_row`).
Labels must be distinct, as they are in the OCaml maps: otherwise a dropped
`Abs` binding could unmask a later binding of the same label. -/
theorem drop_abs_fields (isAbs : F → Bool) (absF : F)
    (hspec : ∀ f, isAbs f = true → f = absF)
    (r : Row F) (htail : ∀ l, r.tail l = absF) (hnd : (labels r.fields).Nodup)
    (l : String) :
    (⟨r.fields.filter (fun p => !isAbs p.2), r.tail⟩ : Row F).at l = r.at l := by
  obtain ⟨fs, t⟩ := r
  simp only [Row.at] at htail ⊢
  rw [htail l]
  clear htail
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, f⟩ := p
    simp only [labels, List.map_cons, List.nodup_cons] at hnd
    have ih := ih hnd.2
    by_cases hn : n = l
    · subst hn
      have hnot : n ∉ labels (fs.filter fun p => !isAbs p.2) :=
        fun m => hnd.1 (by simpa [labels] using labels_filter _ fs n m)
      cases ha : isAbs f
      · simp [ha, find?]
      · have hf := hspec f ha
        subst hf
        simp [ha, find?, find_eq_none n _ hnot]
    · cases ha : isAbs f <;> simp [ha, find?, hn, ih]

/-- **Flattening**: a row whose tail is another row is that row with the
fields appended (outer fields first). Mirrors `mk_row`'s flattening and
`row_view`/`norm_row`. -/
theorem flatten (fs : List (String × F)) (r : Row F) (l : String) :
    (⟨fs, r.at⟩ : Row F).at l = (⟨fs ++ r.fields, r.tail⟩ : Row F).at l := by
  simp only [Row.at, find_append]
  cases find? l fs <;> rfl

end BoltCore.Rows
