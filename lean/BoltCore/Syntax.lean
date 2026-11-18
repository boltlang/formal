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
  deriving Repr, Inhabited

/-- The term is a function. Evaluation is eager, so `let rec x = s` must
bind a function: any other `s` would be evaluated before `x` exists. -/
def Term.IsFun : Term → Prop
  | .lam _ _ => True
  | _ => False

end BoltCore
