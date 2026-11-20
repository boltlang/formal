import BoltCore.Syntax

/-!
# Evaluation

A call-by-value operational semantics for the terms of `Syntax.lean`, as a
definitional interpreter with fuel: `eval n ρ t` evaluates `t` in the
environment `ρ` with `n` steps of fuel. It returns `none` when the fuel
runs out, `some .err` when evaluation goes wrong (a *stuck* term: an
unbound name, a number applied, a missing field selected, a wrong argument
list), and `some (.ok v)` for a value. Type safety (`Safety.lean`) says
that a well-typed term never evaluates to `err`.

* Functions are closures. A `let rec` binds its name, in the closure's own
  environment, to the closure itself, each time it is applied.
* Records are lists of bindings; the first binding of a label counts, as
  in the record types (`Ty.field`).
* `t.l ?? d` evaluates `d` only when the field is missing.
* A `fn` is called with an argument record (`Val.args`): the arguments
  passed by position, the list under the label `*`, go to the leading
  parameters that can be passed by position; then each remaining parameter
  takes the argument of its name, or the value of its default, evaluated
  in the scope of the parameters before it (`bind`). It is an error to
  leave out a parameter without a default, and to pass an argument that no
  parameter takes: too many by position, an unknown name, a name twice, or
  a positional-only parameter by name.
* The built-ins are values (`Val.op`). `if` is an ordinary curried function
  of three arguments, as in `lib/typer.ml`, so both branches are evaluated.
-/

namespace BoltCore

/-- The built-in functions. -/
inductive Op where
  | not
  | succ
  | add
  | ite
  deriving DecidableEq, Repr

mutual
inductive Val where
  | int : Int → Val
  | bool : Bool → Val
  | rcd : Binds → Val
  /-- A function (a `fun` or a `fn`) with its environment, and its own
  name if a `let rec` bound it. -/
  | clo : Binds → Option String → Term → Val
  | op : Op → Val
  /-- `if b`. -/
  | ite1 : Bool → Val
  /-- `if b v`. -/
  | ite2 : Bool → Val → Val

/-- Bindings of names to values: the fields of a record, or an environment. -/
inductive Binds where
  | nil
  | cons : String → Val → Binds → Binds
end

namespace Binds

def lookup (l : String) : Binds → Option Val
  | nil => none
  | cons n v bs => if n = l then some v else lookup l bs

def append : Binds → Binds → Binds
  | nil, cs => cs
  | cons n v bs, cs => cons n v (append bs cs)

/-- Without the bindings of `l`. -/
def remove (l : String) : Binds → Binds
  | nil => nil
  | cons n v bs => if n = l then remove l bs else cons n v (remove l bs)

end Binds

mutual
/-- The elements of a list value: `{}` is the empty list, and a record with
a `hd` and a `tl` a cell. -/
def Val.elems : Val → Option (List Val)
  | .rcd .nil => some []
  | .rcd bs =>
    match bs.lookup "hd", bs.tlElems with
    | some h, some (some es) => some (h :: es)
    | _, _ => none
  | _ => none

/-- The elements of the `tl` field, if there is one. -/
def Binds.tlElems : Binds → Option (Option (List Val))
  | .nil => none
  | .cons n v bs => if n = "tl" then some v.elems else bs.tlElems
end

/-- An argument record: the arguments passed by position, and those passed
by name. -/
def Val.args : Val → Option (List Val × Binds)
  | .rcd bs =>
    match bs.lookup "*" with
    | some l => l.elems.map fun vs => (vs, bs.remove "*")
    | none => none
  | _ => none

/-! ## Results -/

/-- The result of an evaluation that ended: a value, or an error. -/
inductive Res (α : Type) where
  | ok : α → Res α
  | err : Res α

/-- The outcome of an evaluation with fuel: `none` if the fuel ran out. -/
abbrev Out (α : Type) := Option (Res α)

def Out.bind {α β : Type} (o : Out α) (f : α → Out β) : Out β :=
  match o with
  | none => none
  | some .err => some .err
  | some (.ok a) => f a

theorem Out.bind_eq_some {α β : Type} {o : Out α} {f : α → Out β} {r : Res β}
    (h : o.bind f = some r) : (o = some .err ∧ r = .err) ∨ ∃ a, o = some (.ok a) ∧ f a = some r := by
  match o, h with
  | some .err, h => simp [Out.bind] at h; exact .inl ⟨rfl, h.symm⟩
  | some (.ok a), h => exact .inr ⟨a, rfl, h⟩

/-! ## The interpreter -/

def Term.isFun : Term → Bool
  | .lam .. | .fn .. => true
  | _ => false

/-- The built-ins applied to an argument. -/
def delta : Op → Val → Res Val
  | .ite, .bool b => .ok (.ite1 b)
  | .not, w =>
    match w.args with
    | some ([.bool b], .nil) => .ok (.bool !b)
    | _ => .err
  | .succ, w =>
    match w.args with
    | some ([.int i], .nil) => .ok (.int (i + 1))
    | _ => .err
  | .add, w =>
    match w.args with
    | some ([.int i, .int j], .nil) => .ok (.int (i + j))
    | _ => .err
  | _, _ => .err

/-- The argument a parameter of kind `k` takes by position, and the
remaining ones. -/
def byPos (k : PKind) (pos : List Val) : Option (Val × List Val) :=
  match k, pos with
  | .kwOnly, _ => none
  | _, [] => none
  | _, v :: pos => some (v, pos)

/-- The argument a parameter `x` of kind `k` takes by name. -/
def byName (k : PKind) (x : String) (named : Binds) : Option Val :=
  match k with
  | .posOnly => none
  | _ => named.lookup x

/-- The environment of a closure's body: a recursive closure is bound to
its own name. -/
def selfEnv (ρ : Binds) (self : Option String) (s : Term) : Binds :=
  match self with
  | some f => .cons f (.clo ρ self s) ρ
  | none => ρ

mutual
def eval : Nat → Binds → Term → Out Val
  | 0, _, _ => none
  | _ + 1, _, .lit i => some (.ok (.int i))
  | _ + 1, ρ, .var x =>
    match ρ.lookup x with
    | some v => some (.ok v)
    | none => some .err
  | _ + 1, ρ, .lam x t => some (.ok (.clo ρ none (.lam x t)))
  | _ + 1, ρ, .fn ps t => some (.ok (.clo ρ none (.fn ps t)))
  | n + 1, ρ, .app f a =>
    (eval n ρ f).bind fun vf => (eval n ρ a).bind fun va => apply n vf va
  | n + 1, ρ, .rcd fs => (evalFields n ρ fs).bind fun vs => some (.ok (.rcd vs))
  | n + 1, ρ, .sel t l =>
    (eval n ρ t).bind fun v =>
      match v with
      | .rcd vs =>
        match vs.lookup l with
        | some w => some (.ok w)
        | none => some .err
      | _ => some .err
  | n + 1, ρ, .selOr t l d =>
    (eval n ρ t).bind fun v =>
      match v with
      | .rcd vs =>
        match vs.lookup l with
        | some w => some (.ok w)
        | none => eval n ρ d
      | _ => some .err
  | n + 1, ρ, .ext t [] => eval n ρ t
  | n + 1, ρ, .ext t (f :: fs) =>
    (eval n ρ t).bind fun v => (evalFields n ρ (f :: fs)).bind fun ws =>
      match v with
      | .rcd vs => some (.ok (.rcd (ws.append vs)))
      | _ => some .err
  | n + 1, ρ, .letIn false x s t => (eval n ρ s).bind fun v => eval n (.cons x v ρ) t
  | n + 1, ρ, .letIn true x s t =>
    if s.isFun then eval n (.cons x (.clo ρ (some x) s) ρ) t else some .err

def evalFields : Nat → Binds → List (String × Term) → Out Binds
  | 0, _, _ => none
  | _ + 1, _, [] => some (.ok .nil)
  | n + 1, ρ, (l, t) :: fs =>
    (eval n ρ t).bind fun v => (evalFields n ρ fs).bind fun vs => some (.ok (.cons l v vs))

/-- A function value applied to an argument. -/
def apply : Nat → Val → Val → Out Val
  | 0, _, _ => none
  | n + 1, .clo ρ self s, w =>
    match s with
    | .lam x t => eval n (.cons x w (selfEnv ρ self s)) t
    | .fn ps t =>
      match w.args with
      | some (pos, named) =>
        (bind n (selfEnv ρ self s) ps pos named).bind fun ρ' => eval n ρ' t
      | none => some .err
    | _ => some .err
  | _ + 1, .op o, w => some (delta o w)
  | _ + 1, .ite1 b, w => some (.ok (.ite2 b w))
  | _ + 1, .ite2 b v, w => some (.ok (if b then v else w))
  | _ + 1, _, _ => some .err

/-- Bind the parameters of a `fn`, in order, to the arguments passed by
position `pos` and by name `named`, evaluating the defaults that are
needed. Every argument has to be taken. -/
def bind : Nat → Binds → List (String × PKind × Option Term) → List Val → Binds → Out Binds
  | 0, _, _, _, _ => none
  | _ + 1, ρ, [], [], .nil => some (.ok ρ)
  | _ + 1, _, [], _, _ => some .err
  | n + 1, ρ, (x, k, d) :: ps, pos, named =>
    match byPos k pos with
    | some (v, pos) => bind n (.cons x v ρ) ps pos named
    | none =>
      match byName k x named with
      | some v => bind n (.cons x v ρ) ps pos (named.remove x)
      | none =>
        match d with
        | some d => (eval n ρ d).bind fun v => bind n (.cons x v ρ) ps pos named
        | none => some .err
end

/-- The built-ins of `Typing.lean`, as values. -/
def builtinEnv : Binds :=
  .cons "true" (.bool true) (.cons "false" (.bool false) (.cons "not" (.op .not)
    (.cons "succ" (.op .succ) (.cons "add" (.op .add) (.cons "if" (.op .ite) .nil)))))

/-! ## Examples

The calls of issue #2, for `f = fn (x, y = 10) -> add(x, y)`. -/

section Examples

def addXY : Term :=
  .fn [("x", .either, none), ("y", .either, some (.lit 10))]
    (.call (.var "add") [.var "x", .var "y"] [])

/-- `f(1)`: `y` gets its default. -/
example : eval 30 builtinEnv (.call addXY [.lit 1] []) = some (.ok (.int 11)) := rfl

/-- `f(1, 2)`, `f(1, y = 2)` and `f(y = 2, x = 1)`. -/
example : eval 30 builtinEnv (.call addXY [.lit 1, .lit 2] []) = some (.ok (.int 3)) := rfl
example : eval 30 builtinEnv (.call addXY [.lit 1] [("y", .lit 2)]) = some (.ok (.int 3)) := rfl
example : eval 30 builtinEnv (.call addXY [] [("y", .lit 2), ("x", .lit 1)]) =
    some (.ok (.int 3)) := rfl

/-- `f(y = 2)`: `x` is missing. -/
example : eval 30 builtinEnv (.call addXY [] [("y", .lit 2)]) = some .err := rfl

/-- `f(1, x = 2)`: `x` is passed twice. -/
example : eval 30 builtinEnv (.call addXY [.lit 1] [("x", .lit 2)]) = some .err := rfl

/-- `f(1, 2, 3)` and `f(1, z = 2)`: an argument no parameter takes. -/
example : eval 30 builtinEnv (.call addXY [.lit 1, .lit 2, .lit 3] []) = some .err := rfl
example : eval 30 builtinEnv (.call addXY [.lit 1] [("z", .lit 2)]) = some .err := rfl

/-- `1(2)` and `{}.x` go wrong; `{}.x ?? 2` does not. -/
example : eval 30 builtinEnv (.app (.lit 1) (.lit 2)) = some .err := rfl
example : eval 30 builtinEnv (.sel (.rcd []) "x") = some .err := rfl
example : eval 30 builtinEnv (.selOr (.rcd []) "x" (.lit 2)) = some (.ok (.int 2)) := rfl

/-- A `let rec` that calls itself forever runs out of fuel. -/
example : eval 30 builtinEnv
    (.letIn true "loop" (.fn [("n", .either, none)] (.call (.var "loop") [.var "n"] []))
      (.call (.var "loop") [.lit 1] [])) = none := rfl

end Examples

end BoltCore
