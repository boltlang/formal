/-!
# Term syntax

Mirrors `lib/syntax.ml` (paper, Fig. 4). Integer literals are kept so terms
correspond one-to-one with the OCaml implementation.
-/

namespace SimpleSub

inductive Term where
  | lit : Int → Term
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term
  | rcd : List (String × Term) → Term
  | sel : Term → String → Term
  /-- `t with {l = e; ...}`: extend or update fields. -/
  | ext : Term → List (String × Term) → Term
  | letIn : (isRec : Bool) → String → Term → Term → Term
  deriving Repr, Inhabited

end SimpleSub
