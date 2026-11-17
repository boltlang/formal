import BoltCore.Check

/-!
# Example certificates with let-polymorphism

`let id = fun x -> x in id 1`, as inference would certify it: `id`'s
parameter variable `0` is generalized, the use instantiates it with the
copy `1`, and `2` is the type of the application. The accepted
constraints are the use's `1 → 1 ≤ int → 2` and what it decomposes and
propagates into: `int ≤ 1`, `1 ≤ 2` and `int ≤ 2`.

The executable checker (`Check.lean`) accepts each certificate and its
annotated term, by `decide` (so in the kernel); its soundness theorems then
give the certificate's validity, the typing skeleton and the declarative
typing.
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

def prog : Term :=
  .letIn false "id" (.lam "x" (.var "x")) (.app (.var "id") (.lit 1))

/-- The annotated term `lib/typer.ml` would print for `prog`. -/
def ann : Ann :=
  .letIn "id" [0] (.lam "x" (.var 0) (.var "x")) (.app (.inst "id" [(0, 1)]) (.lit 1) (.var 2))

/-- The checker accepts the certificate and the annotated term. -/
theorem checked : cert.check = true ∧ infer cert [] ann = some (.var 2) := by decide

theorem valid : cert.Valid := Certificate.check_valid checked.1

/-- The skeleton: `id : ∀0. 0 → 0`, used at the copy `1`. -/
theorem skeleton : PTyp cert [] prog (.var 2) := infer_sound checked.2

/-- `id 1 : θ(2)`, in the declarative system, with `id` given the scheme
`∀0. 0 → 0` by the generalizing `let`. -/
theorem typed : Typ (defsOf cert.state) [] prog (.gvar 2) := check_sound checked.1 checked.2

/-! ## A constrained example

`let inc = fun x -> succ x in inc 1`:
`inc : ∀0 3. 0 ≤ int, int ≤ 3 ⇒ 0 → 3`, used at the copies `1`
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

def prog : Term :=
  .letIn false "inc" (.lam "x" (.app (.var "succ") (.var "x"))) (.app (.var "inc") (.lit 1))

def Γ : PCtx := [("succ", .mono (.arrow int int))]

def ann : Ann :=
  .letIn "inc" [0, 3] (.lam "x" (.var 0) (.app (.var "succ") (.var "x") (.var 3)))
    (.app (.inst "inc" [(0, 1), (3, 4)]) (.lit 1) (.var 2))

theorem checked : cert.check = true ∧ infer cert Γ ann = some (.var 2) := by decide

theorem valid : cert.Valid := Certificate.check_valid checked.1

theorem skeleton : PTyp cert Γ prog (.var 2) := infer_sound checked.2

/-- `inc 1 : θ(2)`, with `inc` given the constrained scheme
`∀0 3. 0 ≤ int, int ≤ 3 ⇒ 0 → 3` by the generalizing `let`. -/
theorem typed : Typ (defsOf cert.state) (Γ.toCtx cert.bounds .gv) prog (.gvar 2) :=
  check_sound checked.1 checked.2

end Constrained

end BoltCore.Alg.Example
