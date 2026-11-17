# When Subtyping Constraints Liberate (SuperF)

Lionel Parreaux, Aleksander Boruch-Gruszecki, Andong Fan and Chun Yin Chau.
*When Subtyping Constraints Liberate: A Novel Type Inference Approach for
First-Class Polymorphism.* POPL 2024, PACMPL 8, article 48.
[doi:10.1145/3632890](https://doi.org/10.1145/3632890). Local copies: the
paper, [`papers/when-subtyping-constraints-liberate.pdf`](../../papers/when-subtyping-constraints-liberate.pdf),
and the technical report with the appendices (more examples, box erasure,
the acyclicity check, the translation to F<sub>cc</sub>, proofs),
[`papers/superf-tech-report.pdf`](../../papers/superf-tech-report.pdf).

**Status: under discussion (issue #6). Not implemented.**

## What the paper does

SuperF infers first-class (impredicative) polymorphic types. For
`foo f = (f 123, f True)` it infers
`∀a b. ((Int → a) ∧ (Bool → b)) → (a, b)`, where MLsub would infer the
imprecise `(Int ∨ Bool, Int ∨ Bool)`.

- **Multi-bounded polymorphism.** Polymorphic types carry any number of
  lower and upper bounds on their variables, `∀c {c ≤ Int → a, c ≤ Bool →
  b}. c → (a, b)`. Unions in positive and intersections in negative
  positions are sugar for such bounds. These types are internal: user
  annotations are plain System F types.
- **Declarative system F{≤}**, defined by translation to Cretin and Rémy's
  F<sub>cc</sub>. Its subtyping generalizes F<sub>η</sub> and is likely
  undecidable.
- **Inference** never guesses polymorphic types for parameters, only
  generalizes lambdas, and solves constraints down to variable bounds with
  *extrusion*, which the paper formalizes without explicit levels.
- **Termination by a heuristic.** An acyclicity check rejects
  recursive-looking constraints, so inference terminates but is
  incomplete; it is also not always principal.

## How it relates to this repository

- The bound graph that inference builds here is the multi-bounded
  polymorphism of SuperF, restricted to `let`: our constrained schemes
  `∀ᾱ. D ⇒ σ` (`lean/BoltCore/Typing.lean`) are SuperF's polymorphic types
  that can only be bound by `let`.
- Extrusion is the same mechanism. Our certificate checker, like SuperF's
  formal system, does not need levels: levels are how the inferencer keeps
  generalization correct, and the checker only verifies the result.
- If polymorphic subtyping is undecidable, a checker cannot search for
  derivations, but it can check a certificate that records the
  instantiations the inferencer chose. That is an argument for the
  certificate approach (roadmap step 6).

## Differences

- **First-class polymorphism.** We only have let-polymorphism. Moving to
  SuperF would make schemes ordinary types: `Ty` would need quantifiers,
  `Sub` instantiation and generalization rules, and cut elimination,
  the solution theorem, kinds and `SolutionGen.lean` would all need
  revisiting.
- **MLsub's function merging is unsound with first-class polymorphism.**
  The paper notes that `id : ∀α. α → α` is below `(Int → Int) ∧ (Str →
  Str)`, which MLsub equates with `(Int ∨ Str) → (Int ∧ Str)`, not a valid
  type for `id`. Our simplifier and subsumption checker use that equation,
  so they would have to change.
- **Generalization.** SuperF only generalizes lambda abstractions; we
  generalize every `let` right-hand side (there is no value restriction,
  since there is no mutable state).
- **Recursive types.** We reject structural recursive types with an
  occurs-check analogue (#5); SuperF has its own acyclicity heuristic. How
  the two interact is open.
