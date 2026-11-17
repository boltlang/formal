/-!
# Types

The user-facing type language of the OCaml implementation (`Types.typ`),
including rows. Free type and row variables are numbered (`fvar`); graph
variables (`gvar`) are the variables of the algorithm's state, whose
meaning is given by definitions (`Defs` in `Sub.lean`).

There are no structural recursive types (no `μ`): the model rejects a type
variable that reaches itself through a type constructor, as an occurs
check would (see `StructRanked` in `Certificate.lean`). Recursive data is
meant to be nominal (issue #4). Graph-variable definitions may still be
cyclic, as in `α ≤ β ≤ α`, which equates variables without building an
infinite type.

Records and rows share one constructor, as in the OCaml code:
`record fields tail` is a record type, or a row when it is itself a tail.
A field is either `abs` (the top field: no guarantee, not even that the
field is there) or a type (Rémy's `Pre τ`, a present field). So `abs` is
strictly above `top`, the type of any value (`Sub.lean`). The tail is `abs` (the top row), `bot` (the bottom row), a row
variable, or a union/intersection of tails. Fields are a separate mutual
type so that all recursion over types is structural.

`proj l t` is field `l` of the row `t`, for rows whose fields cannot be
computed: row variables. `Ty.field` computes the field of any row,
producing `proj` only for those.
-/

namespace BoltCore

mutual
inductive Ty where
  | top
  | bot
  | union : Ty → Ty → Ty
  | inter : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
  /-- `{l₁: f₁, …, lₙ: fₙ | tail}` -/
  | record : Fields → Ty → Ty
  /-- The absent field, and the top row in tail position. -/
  | abs
  | prim : String → Ty
  /-- A free type or row variable (numbered, so fresh ones are easy to
  pick: larger than every number in sight). -/
  | fvar : Nat → Ty
  /-- Field `l` of an opaque row, such as a row variable: `ρ.l`. -/
  | proj : String → Ty → Ty
  /-- A *graph variable*: a type variable of the algorithm's state, whose
  meaning is given by definitions (`Defs` in `Sub.lean`) rather than being
  rigid like `fvar`. Solutions of constraint systems are expressed with
  these. -/
  | gvar : Nat → Ty

inductive Fields where
  | nil
  | cons : String → Ty → Fields → Fields
end

namespace Fields

/-- The first binding of a label. -/
def lookup (l : String) : Fields → Option Ty
  | nil => none
  | cons n f fs => if n = l then some f else lookup l fs

end Fields

/-! ## Fields of rows -/

/-- The field a row gives the label `l`: an explicit field wins over the
tail; the top row (`Abs`, also `⊤`) gives the absent field, the bottom row
gives `⊥`; unions and intersections of rows are pointwise; a function or
primitive type, viewed as a row, guarantees no field (`Abs`, as width
subtyping would have it); any other row (a row variable) gives the opaque
`proj l t`. This is the `Row.at` of `Rows.lean`, on
syntax. -/
def Ty.field (l : String) : Ty → Ty
  | .record fs t =>
    match fs.lookup l with
    | some f => f
    | none => Ty.field l t
  | .abs => .abs
  | .top => .abs
  | .bot => .bot
  | .union a b => .union (Ty.field l a) (Ty.field l b)
  | .inter a b => .inter (Ty.field l a) (Ty.field l b)
  | .prim _ => .abs
  | .arrow _ _ => .abs
  | t => .proj l t

end BoltCore
