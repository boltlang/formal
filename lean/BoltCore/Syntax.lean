import BoltCore.Types

/-!
# Term syntax

Mirrors `lib/syntax.ml` (paper, Fig. 4). Integer literals are kept so terms
correspond one-to-one with the OCaml implementation.
-/

namespace BoltCore

inductive Term where
  | lit : Int → Term
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term
  | rcd : List (String × Term) → Term
  | sel : Term → String → Term
  /-- `t.l ?? d`: the field `l` of `t` if it is present, else `d`. -/
  | selOr : Term → String → Term → Term
  /-- `t with {l = e; ...}`: extend or update fields. -/
  | ext : Term → List (String × Term) → Term
  | letIn : (isRec : Bool) → String → Term → Term → Term
  /-- `fn (x₁ [= d₁], …, xₙ [= dₙ]) -> t`: a function of a parameter list
  (issue #2). Each parameter has a name, a kind and an optional default,
  which is evaluated at each call, in the scope of the parameters before
  it. It is called with an argument record (`Ty.argRow`). -/
  | fn : List (String × PKind × Option Term) → Term → Term
  deriving Repr, Inhabited

/-- A list literal: `[a, b]` is `{hd = a; tl = {hd = b; tl = {}}}`. -/
def Term.list : List Term → Term
  | [] => .rcd []
  | t :: ts => .rcd [("hd", t), ("tl", Term.list ts)]

/-- A call `f(a₁, …, l₁ = b₁, …)`: an application to the argument record
`{* = [a₁, …]; l₁ = b₁; …}`, as the parser builds it. -/
def Term.call (f : Term) (pos : List Term) (named : List (String × Term)) : Term :=
  .app f (.rcd (("*", Term.list pos) :: named))

/-- The term is a function. Evaluation is eager, so `let rec x = s` must
bind a function: any other `s` would be evaluated before `x` exists. -/
def Term.IsFun : Term → Prop
  | .lam _ _ => True
  | .fn _ _ => True
  | _ => False

end BoltCore
