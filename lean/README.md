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
| `SimpleSub/Types.lean` | types with rows, locally nameless μ, closedness, contractiveness, unguarded size |
| `SimpleSub/Lattice.lean` | the MLsub lattice equations: what the minimal rules cannot derive, and the sequent-style plan |
| `SimpleSub/Typing.lean` | declarative typing (monomorphic `let`, schemes for built-ins, record extension) with examples |
| `SimpleSub/Algorithm.lean` | model of `lib/typer.ml`/`lib/coalesce.ml` (no levels): state, `Constrain`/`TypeTerm` as big-step relations, contractive coalescing |
| `SimpleSub/Soundness.lean` | soundness of constraining on the bound graph: justification and consistency invariants, preserved by `constrain` and `typeTerm` |
| `SimpleSub/Solution.lean` | a solution of the inferred constraints (unifying coalescing via graph variables); record-free fragment |
| `SimpleSub/Sub.lean` | guarded coinductive subtyping, rows compared as label maps; reflexivity, transitivity (cut elimination), S-Rec, the paper's §5.1.3 example, row examples, non-contractive counterexample |
| `SimpleSub/Rows.lean` | row algebra; exactness of the row rewrites in `lib/simplify.ml` and `lib/subsume.ml` |

Lean binds unknown lowercase names in signatures as implicit variables,
*unless a constant with that name exists*, in which case the constant is
used silently. Keep example definitions (`τ`, `A`, `M`, …) in their own
namespace or `private`.
