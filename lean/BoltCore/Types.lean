/-!
# Types, rows and fields

The user-facing type language, sorted (`docs/design/sorts.md`): types, rows
and fields are one family indexed by a sort, as in Rémy's records and
Marques et al.: `Ty .ty` are types, `Ty .row` rows, `Ty .field` fields.

* The lattice is generic: `top`, `bot`, `union`, `inter` and variables exist
  at every sort. `Abs` is `top` at sort `field` (any value, or no field at
  all) and at sort `row` (the top row). It is never a type.
* Types: primitives, functions, and records `rcd ρ` of a row `ρ`.
* Rows: `cons l θ ρ` adds the field `θ` for `l` in front of `ρ`; `nil` is
  the empty row, `missing` at every label. A record literal's row ends in
  `nil`: its type is closed.
* Fields: `pre τ`, a present field of type `τ`; `missing`, the field that is
  definitely absent; `proj l ρ`, field `l` of an opaque row such as a row
  variable. An optional field is the union `opt τ = pre τ ∪ missing`.
* Signatures (issue #2): the domain of a function with a parameter list is
  the union `Ty.sig` of the closed argument records `Dₖ` it accepts, one
  per number `k` of arguments passed by position. It is a definition, not a
  constructor.

There are no structural recursive types (no `μ`); recursive solutions are
graph variables (`gvar`), whose meaning is given by definitions
(`Sub.lean`).
-/

namespace BoltCore

inductive Srt where
  | ty
  | row
  | field
  deriving DecidableEq, Repr

inductive Ty : Srt → Type where
  | top : Ty s
  | bot : Ty s
  | union : Ty s → Ty s → Ty s
  | inter : Ty s → Ty s → Ty s
  /-- A free (rigid) variable, as quantified by schemes. -/
  | fvar : Nat → Ty s
  /-- A graph variable, defined by its upper bounds (`Defs`). -/
  | gvar : Nat → Ty s
  | prim : String → Ty .ty
  | arrow : Ty .ty → Ty .ty → Ty .ty
  | rcd : Ty .row → Ty .ty
  | cons : String → Ty .field → Ty .row → Ty .row
  | pre : Ty .ty → Ty .field
  /-- Field `l` of an opaque row (a row variable). -/
  | proj : String → Ty .row → Ty .field
  /-- The field that is definitely absent. -/
  | missing : Ty .field
  /-- The empty row: `missing` at every label. -/
  | nil : Ty .row

/-- `Abs`: the top field. -/
abbrev Ty.abs : Ty .field := .top

/-- `Opt τ`: a field that is missing, or present at `τ`. -/
abbrev Ty.opt (τ : Ty .ty) : Ty .field := .union (.pre τ) .missing

/-- The field a row gives a label: an explicit field wins over the rest;
the top row gives `Abs`, the empty row `missing`, the bottom row the bottom
field; unions and
intersections are pointwise; a variable's fields are opaque. At the other
sorts it is `⊤`, so that facts about rows can be stated for derivations at
any sort. (Matching on the sort first keeps the recursion structural.) -/
def Ty.field (l : String) : {s : Srt} → Ty s → Ty .field
  | .row, .cons l' θ ρ => if l' = l then θ else ρ.field l
  | .row, .top => .top
  | .row, .nil => .missing
  | .row, .bot => .bot
  | .row, .union a b => .union (a.field l) (b.field l)
  | .row, .inter a b => .inter (a.field l) (b.field l)
  | .row, .fvar n => .proj l (.fvar n)
  | .row, .gvar n => .proj l (.gvar n)
  | .ty, _ => .top
  | .field, _ => .top

/-- A row with present fields `F` in front of `ρ`. -/
def Ty.ofFields : List (String × Ty .ty) → Ty .row → Ty .row
  | [], ρ => ρ
  | (l, τ) :: F, ρ => .cons l (.pre τ) (Ty.ofFields F ρ)

/-- The same labels as `F`, all `Abs`, in front of `ρ`. -/
def Ty.absFields : List (String × Ty .ty) → Ty .row → Ty .row
  | [], ρ => ρ
  | (l, _) :: F, ρ => .cons l .abs (Ty.absFields F ρ)

/-- The record type of a record literal with fields `F`: closed. -/
def Ty.record (F : List (String × Ty .ty)) : Ty .ty := .rcd (Ty.ofFields F .nil)

theorem Ty.field_ofFields_none {l : String} {ρ : Ty .row} :
    ∀ {F : List (String × Ty .ty)}, (∀ p ∈ F, p.1 ≠ l) → (Ty.ofFields F ρ).field l = ρ.field l
  | [], _ => rfl
  | (l', τ) :: F, h => by
    have hne : l' ≠ l := h (l', τ) (List.mem_cons_self ..)
    simp only [Ty.ofFields, Ty.field, hne, ite_false]
    exact Ty.field_ofFields_none fun p hp => h p (List.mem_cons_of_mem _ hp)

/-! ## Parameter lists

A call passes one closed record: the positional arguments as a list under
the reserved label `*`, which source code cannot write, and one field per
named argument. A list is nested closed records: `[a, b]` is
`{hd = a; tl = {hd = b; tl = {}}}`. -/

/-- How a parameter can be passed: by position only (before a `/`), by
position or by name, or by name only (after a `*`). -/
inductive PKind where
  | posOnly
  | either
  | kwOnly
  deriving DecidableEq, Repr

/-- A parameter of a signature: its name, how it can be passed, whether it
has a default (it can then be left out), and its type. The type is a
parameter, since the algorithm's simple types have signatures too. -/
structure Param (α : Type) where
  name : String
  kind : PKind
  opt : Bool
  ty : α

namespace Param
variable {α β : Type}

def map (f : α → β) (p : Param α) : Param β := ⟨p.name, p.kind, p.opt, f p.ty⟩

/-- `m`: the least number of arguments passed by position, the
positional-only parameters without a default. -/
def minPos (ps : List (Param α)) : Nat := ps.countP fun p => p.kind = .posOnly && !p.opt

/-- `p`: the number of parameters that can be passed by position. -/
def maxPos (ps : List (Param α)) : Nat := ps.countP fun p => p.kind != .kwOnly

/-- The numbers `k` of arguments passed by position: `m ≤ k ≤ p`. -/
def counts (ps : List (Param α)) : List Nat :=
  List.range' (minPos ps) (maxPos ps + 1 - minPos ps)

/-- The types of the first `k` parameters, those passed by position. -/
def pos : Nat → List (Param α) → List α
  | k + 1, p :: ps => if p.kind = .kwOnly then [] else p.ty :: pos k ps
  | _, _ => []

/-- The parameters passed by name when `k` arguments are passed by
position: the either-way parameters after the `k`-th, and the keyword-only
ones. A positional-only parameter is never passed by name. -/
def named : Nat → List (Param α) → List (Param α)
  | _, [] => []
  | k, p :: ps =>
    if p.kind = .kwOnly then p :: ps
    else match k with
      | k + 1 => named k ps
      | 0 => if p.kind = .either then p :: named 0 ps else named 0 ps

theorem minPos_map (f : α → β) (ps : List (Param α)) : minPos (ps.map (map f)) = minPos ps := by
  simp only [minPos, List.countP_map]; rfl

theorem maxPos_map (f : α → β) (ps : List (Param α)) : maxPos (ps.map (map f)) = maxPos ps := by
  simp only [maxPos, List.countP_map]; rfl

theorem counts_map (f : α → β) (ps : List (Param α)) : counts (ps.map (map f)) = counts ps := by
  simp only [counts, minPos_map, maxPos_map]

theorem pos_map (f : α → β) : ∀ (k : Nat) (ps : List (Param α)),
    pos k (ps.map (map f)) = (pos k ps).map f
  | 0, [] | 0, _ :: _ | _ + 1, [] => rfl
  | k + 1, p :: ps => by
    simp only [List.map_cons, pos]
    by_cases h : p.kind = .kwOnly
    · simp [map, h]
    · simp [map, h, pos_map f k ps]

theorem named_map (f : α → β) : ∀ (k : Nat) (ps : List (Param α)),
    named k (ps.map (map f)) = (named k ps).map (map f)
  | _, [] => rfl
  | 0, p :: ps => by
    simp only [List.map_cons, named]
    by_cases h : p.kind = .kwOnly
    · simp [map, h]
    · by_cases h' : p.kind = .either <;> simp [map, h, h', named_map f 0 ps]
  | k + 1, p :: ps => by
    simp only [List.map_cons, named]
    by_cases h : p.kind = .kwOnly
    · simp [map, h]
    · simp [map, h, named_map f k ps]

theorem mem_pos {x : α} : ∀ {k : Nat} {ps : List (Param α)}, x ∈ pos k ps → ∃ p ∈ ps, p.ty = x
  | 0, [], h | 0, _ :: _, h | _ + 1, [], h => nomatch h
  | k + 1, p :: ps, h => by
    simp only [pos] at h
    split at h
    · exact nomatch h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨p, List.mem_cons_self .., rfl⟩
      · obtain ⟨q, hq, e⟩ := mem_pos h
        exact ⟨q, List.mem_cons_of_mem _ hq, e⟩

theorem mem_named {q : Param α} : ∀ {k : Nat} {ps : List (Param α)}, q ∈ named k ps → q ∈ ps
  | _, [], h => nomatch h
  | 0, p :: ps, h => by
    simp only [named] at h
    split at h
    · exact h
    · split at h
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_named h)
      · exact List.mem_cons_of_mem _ (mem_named h)
  | k + 1, p :: ps, h => by
    simp only [named] at h
    split at h
    · exact h
    · exact List.mem_cons_of_mem _ (mem_named h)

end Param

/-- The union of a list of types (`⊥` for none). -/
def Ty.unions : List (Ty s) → Ty s
  | [] => .bot
  | [a] => a
  | a :: b :: l => .union a (Ty.unions (b :: l))

/-- The type of a list: `[τ₁, τ₂]` is `{hd: τ₁, tl: {hd: τ₂, tl: {}}}`. -/
def Ty.list : List (Ty .ty) → Ty .ty
  | [] => .rcd .nil
  | τ :: τs => .rcd (.cons "hd" (.pre τ) (.cons "tl" (.pre (Ty.list τs)) .nil))

/-- The field of a parameter passed by name: optional if it has a default. -/
def Param.field (p : Param (Ty .ty)) : Ty .field := if p.opt then Ty.opt p.ty else .pre p.ty

/-- The closed row with a field for each parameter. -/
def Ty.ofParams : List (Param (Ty .ty)) → Ty .row
  | [] => .nil
  | p :: ps => .cons p.name p.field (Ty.ofParams ps)

/-- The row of `Dₖ`, the argument record for `k` arguments passed by
position: `{*: [τ₁, …, τₖ], Eₖ, Q}`. -/
def Ty.argRow (ps : List (Param (Ty .ty))) (k : Nat) : Ty .row :=
  .cons "*" (.pre (Ty.list (Param.pos k ps))) (Ty.ofParams (Param.named k ps))

/-- The rows of the argument records a parameter list accepts. -/
def Ty.sigRows (ps : List (Param (Ty .ty))) : List (Ty .row) :=
  (Param.counts ps).map (Ty.argRow ps)

/-- The domain of a function with the parameters `ps`: the union of the
argument records `Dₘ ∪ … ∪ Dₚ`. -/
def Ty.sig (ps : List (Param (Ty .ty))) : Ty .ty := Ty.unions ((Ty.sigRows ps).map .rcd)

/-- The graph variables occurring in a type, of any sort. -/
def Ty.gvars : Ty s → List Nat
  | .gvar n => [n]
  | .top | .bot | .fvar _ | .prim _ | .missing | .nil => []
  | .union a b | .inter a b | .arrow a b => a.gvars ++ b.gvars
  | .rcd ρ | .pre ρ | .proj _ ρ => ρ.gvars
  | .cons _ θ ρ => θ.gvars ++ ρ.gvars

end BoltCore
