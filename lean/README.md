# SimpleSub (Lean)

Mechanized metatheory for the OCaml Simple-sub implementation in `../lib`.
See the "Mechanized metatheory" section of `../README.md` for what is
proved.

```sh
lake build
```

| File | Contents |
|---|---|
| `SimpleSub/Syntax.lean` | term syntax (mirrors `lib/syntax.ml`) |
| `SimpleSub/Types.lean` | types with rows; no structural recursive types |
| `SimpleSub/Lattice.lean` | the MLsub lattice equations: what the minimal rules cannot derive, and the sequent-style plan |
| `SimpleSub/Typing.lean` | declarative typing (constrained schemes `∀ᾱ. D ⇒ σ` for built-ins and let-polymorphism, record extension) with examples |
| `SimpleSub/Algorithm.lean` | model of `lib/typer.ml` (no levels): state, `Constrain`/`TypeTerm` as big-step relations; ranked bounds (`StructRanked`) rule out structural recursive types |
| `SimpleSub/Soundness.lean` | soundness of constraining on the bound graph: justification and consistency invariants, preserved by `constrain` and `typeTerm` |
| `SimpleSub/Solution.lean` | the solution of the inferred constraints (unifying coalescing via graph variables) and its invariants |
| `SimpleSub/Sorts.lean` | `Abs` is never a function parameter or result (`NAC`), preserved by `constrain` and `typeTerm` |
| `SimpleSub/SolutionRows.lean` | the solution theorem, rows and extrusion-shaped justifications included (assuming acyclic row-variable tails) |
| `SimpleSub/Theorem1.lean` | soundness of type inference (`soundness`), assuming acyclic row-variable tails; generalized over renamings of type variables (`soundR`), for instantiation |
| `SimpleSub/Kinds.lean` | kinds for row variables: the algorithm keeps rows well-kinded, so tails are acyclic; **Theorem 1** with no assumptions (`theorem1`) |
| `SimpleSub/Certificate.lean` | certificates (accepted constraints, bounds, kinds, ranks) and typing skeletons: a valid certificate gives a declarative typing over a solution without recursive types (`CTyp.sound`, `Valid.nonrec`), and every accepted run yields one (`TypeTerm.certificate`) |
| `SimpleSub/Sub.lean` | guarded coinductive subtyping, rows compared as label maps; reflexivity, transitivity (cut elimination, for any relation), coinduction up to transitivity, ranked (non-recursive) definitions, the paper's §5.1.3 example with graph variables, row examples |
| `SimpleSub/Rows.lean` | row algebra; exactness of the row rewrites in `lib/simplify.ml` and `lib/subsume.ml` |

Lean binds unknown lowercase names in signatures as implicit variables,
*unless a constant with that name exists*, in which case the constant is
used silently. Keep example definitions (`τ`, `A`, `M`, …) in their own
namespace or `private`.
