# Bolt's Core (Lean)

Mechanized metatheory for the OCaml Simple-sub implementation in `../lib`.
See the "Mechanized metatheory" section of `../README.md` for what is
proved.

```sh
lake build
lake exe boltcore-check CERT.json   # check a certificate from `boltcore --cert`
```

| File | Contents |
|---|---|
| `BoltCore/Syntax.lean` | term syntax (mirrors `lib/syntax.ml`) |
| `BoltCore/Types.lean` | types with rows; no structural recursive types |
| `BoltCore/Lattice.lean` | the MLsub lattice equations: what the minimal rules cannot derive, and the sequent-style plan |
| `BoltCore/Typing.lean` | declarative typing (constrained schemes `∀ᾱ. D ⇒ σ` for built-ins and let-polymorphism, record extension, selection of present fields only) with examples; selecting a missing field is untypable (`not_typ_sel_missing`) |
| `BoltCore/Algorithm.lean` | model of `lib/typer.ml` (no levels): state, `Constrain`/`TypeTerm` as big-step relations; ranked bounds (`StructRanked`) rule out structural recursive types |
| `BoltCore/Soundness.lean` | soundness of constraining on the bound graph: justification and consistency invariants, preserved by `constrain` and `typeTerm` |
| `BoltCore/Solution.lean` | the solution of the inferred constraints (unifying coalescing via graph variables) and its invariants |
| `BoltCore/Sorts.lean` | `Abs` is never a function parameter or result (`NAC`), preserved by `constrain` and `typeTerm` |
| `BoltCore/SolutionRows.lean` | the solution theorem, rows and extrusion-shaped justifications included (assuming acyclic row-variable tails) |
| `BoltCore/Theorem1.lean` | soundness of type inference (`soundness`), assuming acyclic row-variable tails; generalized over renamings of type variables (`soundR`), for instantiation |
| `BoltCore/Kinds.lean` | kinds for row variables: the algorithm keeps rows well-kinded, so tails are acyclic; **Theorem 1** with no assumptions (`theorem1`) |
| `BoltCore/Certificate.lean` | certificates (accepted constraints, bounds, kinds, ranks) and typing skeletons: a valid certificate gives a declarative typing over a solution without recursive types (`CTyp.sound`, `Valid.nonrec`), and every accepted run yields one (`TypeTerm.certificate`) |
| `BoltCore/SolutionGen.lean` | the solution under a generalization: accepted constraints hold when generalized variables are read as an instance of their bounds (`solution_gen`) |
| `BoltCore/PolyLet.lean` | certificates with let-polymorphism: schemes from generalized variables and their bounds (`mkScheme`), checked generalization (`GenOK`) and instantiation (`InstOK`), soundness (`PTyp.sound_top`; uses classical logic) |
| `BoltCore/Check.lean` | the executable checker: Boolean checks of validity (`Certificate.check`) and of polymorphic skeletons over annotated terms (`infer`), with `check_sound`: an accepted certificate types the term |
| `BoltCore/Examples.lean` | example certificates with let-polymorphism, unconstrained and constrained, checked by hand and by the executable checker (`decide`) |
| `Main.lean` | `boltcore-check`: reads a JSON certificate, computes ranks, runs the checks, explains rejections (parsing and diagnostics are not verified) |
| `BoltCore/Sub.lean` | guarded coinductive subtyping, rows compared as label maps, `Abs` strictly above `⊤`; reflexivity, transitivity (cut elimination, for any relation), coinduction up to transitivity, ranked (non-recursive) definitions, the paper's §5.1.3 example with graph variables, row examples |
| `BoltCore/Rows.lean` | row algebra; exactness of the row rewrites in `lib/simplify.ml` and `lib/subsume.ml` |

Lean binds unknown lowercase names in signatures as implicit variables,
*unless a constant with that name exists*, in which case the constant is
used silently. Keep example definitions (`τ`, `A`, `M`, …) in their own
namespace or `private`.
