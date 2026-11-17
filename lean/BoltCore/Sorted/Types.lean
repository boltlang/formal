/-!
# Sorted types (`docs/design/sorts.md`)

Types, rows and fields are one family indexed by a sort, as in Rémy's
records and Marques et al.: `Ty .ty` are types, `Ty .row` rows, `Ty .field`
fields.

* The lattice is generic: `top`, `bot`, `union`, `inter` and variables exist
  at every sort. `Abs` is `top` at sort `field` (any value, or no field at
  all) and at sort `row` (the top row). It is never a type.
* Types: primitives, functions, and records `rcd ρ` of a row `ρ`.
* Rows: `cons l θ ρ` adds the field `θ` for `l` in front of `ρ`; a record
  literal's row ends in `top`.
* Fields: `pre τ`, a present field of type `τ`; `proj l ρ`, field `l` of an
  opaque row such as a row variable.

There are no structural recursive types (no `μ`); recursive solutions are
graph variables (`gvar`), whose meaning is given by definitions
(`Sorted/Sub.lean`).

This file and the others in `Sorted/` are the sorted core, built alongside
the unsorted development until it replaces it (the plan of the design
note).
-/

namespace BoltCore.Sorted

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

/-- `Abs`: the top field. -/
abbrev Ty.abs : Ty .field := .top

/-- The field a row gives a label: an explicit field wins over the rest;
the top row gives `Abs`, the bottom row the bottom field; unions and
intersections are pointwise; a variable's fields are opaque. At the other
sorts it is `⊤`, so that facts about rows can be stated for derivations at
any sort. (Matching on the sort first keeps the recursion structural.) -/
def Ty.field (l : String) : {s : Srt} → Ty s → Ty .field
  | .row, .cons l' θ ρ => if l' = l then θ else ρ.field l
  | .row, .top => .top
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

/-- The record type of a record literal with fields `F`. -/
def Ty.record (F : List (String × Ty .ty)) : Ty .ty := .rcd (Ty.ofFields F .top)

theorem Ty.field_ofFields_none {l : String} {ρ : Ty .row} :
    ∀ {F : List (String × Ty .ty)}, (∀ p ∈ F, p.1 ≠ l) → (Ty.ofFields F ρ).field l = ρ.field l
  | [], _ => rfl
  | (l', τ) :: F, h => by
    have hne : l' ≠ l := h (l', τ) (List.mem_cons_self ..)
    simp only [Ty.ofFields, Ty.field, hne, ite_false]
    exact Ty.field_ofFields_none fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- The graph variables occurring in a type, of any sort. -/
def Ty.gvars : Ty s → List Nat
  | .gvar n => [n]
  | .top | .bot | .fvar _ | .prim _ => []
  | .union a b | .inter a b | .arrow a b => a.gvars ++ b.gvars
  | .rcd ρ | .pre ρ | .proj _ ρ => ρ.gvars
  | .cons _ θ ρ => θ.gvars ++ ρ.gvars

end BoltCore.Sorted
