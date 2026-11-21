import BoltCore.Safety
import BoltCore.Check
import BoltCore.Adequacy

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

/-- The built-in values have the types the checker gives the built-ins. -/
theorem pbuiltins_typed (c : Certificate) :
    ETyp (defsOf c.state) builtinEnv (pbuiltins.toCtx c.bounds .gv) :=
  .mono (.bool Sub.refl) <| .mono (.bool Sub.refl) <| .mono (.not Sub.refl) <|
    .mono (.succ Sub.refl) <| .mono (.add Sub.refl) .nil

/-- **Inference is safe**: a term the algorithm types, in a run without
structural recursive types, does not go wrong. -/
theorem infer_safe {K : Nat → List String} {L : Nat → Nat} {t : Term} {st : SType} {s' : State}
    (h : Infers K L t st s') (n : Nat) : eval n builtinEnv t ≠ some .err := by
  obtain ⟨h, r, hr⟩ := h
  have hc := h.certificate hr
  exact (PTyp.sound_top hc.1 hc.2).safe (pbuiltins_typed _) n

/-- **Certified programs are safe**: if the certificate checks and the
annotated term checks against it, the term does not go wrong. -/
theorem check_safe {c : Certificate} {a : Ann} {st : SType} (hc : c.check = true)
    (h : infer c pbuiltins a = some st) (n : Nat) :
    eval n builtinEnv a.erase ≠ some .err :=
  (check_sound hc h).safe (pbuiltins_typed c) n

end BoltCore.Alg
