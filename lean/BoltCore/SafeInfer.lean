import BoltCore.Safety
import BoltCore.Check

/-!
# Inferred programs do not go wrong

Type safety (`Safety.lean`) for the types that inference gives: a term the
algorithm model types (`theorem1`), and a term whose certificate the
executable checker accepts (`check_sound`), never evaluates to an error.
The second is the statement about runs of the OCaml type checker: the
program it certified does not go wrong, in the semantics of `Eval.lean`.
-/

namespace BoltCore.Alg

open State

/-- The built-in values of the model, which has no `if`. -/
def builtinEnvMono : Binds :=
  .cons "true" (.bool true) (.cons "false" (.bool false) (.cons "not" (.op .not)
    (.cons "succ" (.op .succ) (.cons "add" (.op .add) .nil))))

theorem builtinsMono_typed {E : Defs} : ETyp E builtinEnvMono builtins.toCtx :=
  .mono (.bool Sub.refl) <| .mono (.bool Sub.refl) <| .mono (.not Sub.refl) <|
    .mono (.succ Sub.refl) <| .mono (.add Sub.refl) .nil

/-- **Inference is safe**: a term the algorithm types does not go wrong. -/
theorem infer_safe {K : Nat → List String} {t : Term} {st : SType} {s' : State}
    (h : TypeTerm builtins (State.initK K) t st s') (n : Nat) :
    eval n builtinEnvMono t ≠ some .err :=
  (theorem1 h).safe builtinsMono_typed n

/-- The built-in values have the types the checker gives the built-ins. -/
theorem pbuiltins_typed (c : Certificate) (k : Nat) :
    ETyp (defsOf c.state) builtinEnv ((pbuiltins k).toCtx c.bounds .gv) :=
  .mono (.bool Sub.refl) <| .mono (.bool Sub.refl) <| .mono (.not Sub.refl) <|
    .mono (.succ Sub.refl) <| .mono (.add Sub.refl) <|
    .cons (fun _ ⟨_, _, _, e⟩ => by subst e; exact .ite Sub.refl) .nil

/-- **Certified programs are safe**: if the certificate checks and the
annotated term checks against it, the term does not go wrong. -/
theorem check_safe {c : Certificate} {k : Nat} {a : Ann} {st : SType} (hc : c.check = true)
    (h : infer c (pbuiltins k) a = some st) (n : Nat) :
    eval n builtinEnv a.erase ≠ some .err :=
  (check_sound hc h).safe (pbuiltins_typed c k) n

end BoltCore.Alg
