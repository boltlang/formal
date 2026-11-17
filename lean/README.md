# Bolt's Core (Lean)

Mechanized metatheory for the OCaml type checker in `../lib`: a Lake
project on Lean v4.35.0, with no Mathlib. Everything is proved; there are no
`sorry`s. These are proofs about a model of the code, not about the OCaml
itself; certificates ([`../docs/certificates.md`](../docs/certificates.md))
connect the two.

```sh
lake build
lake exe boltcore-check CERT.json   # check a certificate from `boltcore --cert`
```

## Main results

- **Theorem 1** (`theorem1`, `Kinds.lean`): if the algorithm model types `t`
  with `st` from the built-ins, then `t : θ(st)` in the declarative system,
  where `θ` is the solution of the final state. Rows, row expansion and
  kinds are included; there are no assumptions.
- **Certificates** (`PTyp.sound_top`): a valid certificate with a typing
  skeleton with let-polymorphism gives a declarative typing with
  constrained schemes, over a solution without recursive types
  (`Valid.nonrec`). Every accepted run of the model yields one
  (`TypeTerm.certificate`, `Adequacy.lean`).
- **The executable checker** (`check_sound`, `Check.lean`): Boolean checks
  that imply validity and the skeleton, run by `boltcore-check`.
- **Rows** (`Rows.lean`): the row rewrites of the simplifier and of
  subsumption preserve the meaning of rows.

Types, rows and fields are separate *sorts* (`Types.lean`,
[`../docs/design/sorts.md`](../docs/design/sorts.md)): `Abs` is the top
field and the top row, never a type, so a present field `pre τ` is below
`Abs` and nothing derives the converse. The algorithm and certificates use
one unsorted syntax of simple types, translated into the sorts by position.

## Files

| File | Contents |
|---|---|
| `BoltCore/Syntax.lean` | term syntax (mirrors `lib/syntax.ml`) |
| `BoltCore/Types.lean` | types, rows and fields as one family indexed by a sort; `Abs` is `⊤` at the field and row sorts; no structural recursive types |
| `BoltCore/Sub.lean` | guarded coinductive subtyping, rows compared field by field (`Step.fields`), `Abs ≰ pre τ` (`not_abs_le_pre`); reflexivity, transitivity (cut elimination by sort, for any relation), coinduction up to transitivity, ranked (non-recursive) definitions, the paper's §5.1.3 example with graph variables, row examples |
| `BoltCore/Rows.lean` | row algebra; exactness of the row rewrites in `lib/simplify.ml` and `lib/subsume.ml` |
| `BoltCore/Lattice.lean` | the MLsub lattice equations: what the minimal rules cannot derive (`not_fun_merge`, `not_pre_union`), and the sequent-style plan |
| `BoltCore/Typing.lean` | declarative typing (constrained schemes `∀ᾱ. D ⇒ σ`, with constraints at any sort, for built-ins and let-polymorphism; record extension; selection of present fields `pre τ` only) with examples; selecting a missing field is untypable (`not_typ_sel_missing`) |
| `BoltCore/Algorithm.lean` | model of `lib/typer.ml` (no levels): state, `Constrain`/`TypeTerm` as big-step relations; ranked bounds (`StructRanked`) rule out structural recursive types |
| `BoltCore/Soundness.lean` | soundness of constraining on the bound graph: justification and consistency invariants, preserved by `constrain` and `typeTerm` |
| `BoltCore/Solution.lean` | the solution of the inferred constraints (unifying coalescing via graph variables), simple types translated by position (`toTy`, `toRow`, `toField`), and its invariants |
| `BoltCore/Sorts.lean` | `Abs` is never a function parameter or result (`NAC`), preserved by `constrain` and `typeTerm` |
| `BoltCore/SolutionRows.lean` | the solution theorem at the type and row sorts, rows and extrusion-shaped justifications included (assuming acyclic row-variable tails), proved under a generalization (`solution_gen`: generalized variables read, at the type and row sorts, as an instance of their bounds); the plain theorem (`solution_ty`, `solution_row`) is the case where nothing is generalized |
| `BoltCore/Theorem1.lean` | soundness of type inference (`soundness`), assuming acyclic row-variable tails; generalized over renamings of type variables (`soundR`), for instantiation |
| `BoltCore/Kinds.lean` | kinds for row variables: the algorithm keeps rows well-kinded, so tails are acyclic; **Theorem 1** with no assumptions (`theorem1`) |
| `BoltCore/Certificate.lean` | certificates (accepted constraints, bounds, kinds, ranks) and their validity; every accepted run yields a valid one (`TypeTerm.certificateValid`) |
| `BoltCore/PolyLet.lean` | typing skeletons with let-polymorphism: schemes from generalized variables and their bounds (`mkScheme`), checked generalization (`GenOK`) and instantiation (`InstOK`), soundness (`PTyp.sound_top`; uses classical logic), no recursive types (`Valid.nonrec`) |
| `BoltCore/Adequacy.lean` | every accepted run of the model yields a valid certificate and a skeleton (`TypeTerm.certificate`); Theorem 1 through certificates (`theorem1_cert`) |
| `BoltCore/Check.lean` | the executable checker: Boolean checks of validity (`Certificate.check`) and of polymorphic skeletons over annotated terms (`infer`), with `check_sound`: an accepted certificate types the term |
| `BoltCore/Examples.lean` | example certificates with let-polymorphism, unconstrained and constrained, accepted by the executable checker (`decide`), which gives their validity, skeletons and typings |
| `Main.lean` | `boltcore-check`: reads a JSON certificate, computes ranks, runs the checks, explains rejections (parsing and diagnostics are not verified) |

## Subtyping (`Sub.lean`, `Rows.lean`, `Lattice.lean`)

`Step E R` is one layer of subtyping. It is inductive and uses the
coinductive hypothesis `R` only under a function type or a record field,
which is the paper's `▷`/`◁` discipline. `E` gives *graph variables*
(`gvar`) their meaning as intersections of sets of upper bounds: named,
possibly mutually recursive definitions without binders, used to express
solutions. `Sub` is the greatest fixed point (Knaster–Tarski), with a
coinduction principle `Sub.coind`.

- `Sub.refl`, and `Sub.trans` by cut elimination on single layers (`cut`,
  for any relation in the guarded premises): induction on the two finite
  derivations, with the composed relation as the coinductive hypothesis.
  `Sub.coind_trans` is coinduction up to transitivity.
- `paper_example`: the paper's §5.1.3 example, `A = τ → τ → A ≤ B = τ → B`,
  with `A` and `B` graph variables defined by their unfoldings.
- `field_in_compound_tail`, `bottom_tail`: row facts that need tails to be
  looked into, one of them the shape the simplifier produces for `count`;
  `not_empty_le_field` checks the other direction.

Records compare their rows under the hypothesis, and rows are compared
label by label, in one layer: they are total maps from labels to fields.
`Ty.field` looks a label up in the explicit fields, then in the rest of the
row. A row variable's fields are opaque atoms `proj l ρ`. Every comparison
of rows, by any rule, holds field by field (`Step.fields`), so cut
elimination for rows goes field by field; for types and fields it is an
induction on the two derivations, through a *pending cut* (`Pend`).

`Abs` is `⊤` at the field sort: it promises nothing about a field, not even
that it is there. A present field `pre τ` is below it, and nothing derives
`Abs ≤ pre τ` (`not_abs_le_pre`), so `{} ≤ {x : ⊤}` fails. This matches
`lib/typer.ml`, where an absent field never satisfies a present one.

`Rows.lean` models rows by what they denote, a total map from labels to
fields with explicit fields overriding the tail, and shows each row
rewrite in the OCaml code preserves it:

- `merge_exact`: merging two rows is exact under the covers condition
  (`add_row` in the simplifier, `merge_rows` in subsumption);
  `merge_inexact`: without the condition it is wrong, which is the bug a
  mutation test introduced;
- `combine_sound`: combining two atomic tails is the pointwise meet or
  join, given the lattice laws for `Abs` (top) and `⊥`;
- `drop_abs_fields`: dropping `Abs` fields when the tail is `Abs`
  (`mk_row`) is exact, provided labels are distinct;
- `flatten`: nested rows flatten to appended fields (`mk_row`, `row_view`,
  `norm_row`).

Not covered yet: the MLsub lattice equations. The OCaml code uses five
that aren't derivable: merging intersections and unions of functions,
merging intersections and unions of records, and distributing a row over a
union of tails; with sorts, merging the fields of two rows also needs
`pre (τ₁ ∨ τ₂) ≤ pre τ₁ ∨ pre τ₂`. `Lattice.lean` proves that function
merging and this one aren't derivable from the minimal rules
(`not_fun_merge`, `not_pre_union`), and its header records the
sequent-style plan for adding the equations while keeping transitivity.

## Typing (`Typing.lean`)

Declarative typing over the minimal subtyping rules, with constrained
schemes `∀ᾱ. D ⇒ σ` as in HM(X): an instance substitutes for `ᾱ`, at each
sort, such that the constraints `D` hold; a constraint is subtyping at its
own sort. `let` gives `x` a scheme when `s` has every
instance of it, and it has one. The constraints are read through their
instances, as HM(X) defines entailment, instead of typing `s` under them as
hypotheses: subtyping under both lower and upper bounds is not transitive
in general ("bad bounds"). A monomorphic `let` is the scheme with no
variables. There is no value restriction (no mutable state).

Selection `t.l : τ` requires a present field, `t : {l : pre τ}`, by the
shape of the rule.
Selecting a label that a record literal lacks has no type
(`not_typ_sel_missing`: `{}.x`, `{a = 1}.b`), a first step towards type
safety. There is no operational semantics yet, so progress and
preservation are not proved. Examples: `typ_twice`, `typ_if`, `typ_ext`
(the extension example of Marques et al.), `typ_letPoly`,
`typ_letConstrained`.

## The algorithm and its soundness

- `Algorithm.lean` models `lib/typer.ml` without levels. Bounds live in an
  explicit `State`. `Constrain`, row expansion included, and `TypeTerm` are
  big-step relations, "succeeds from state `s` with state `s'`", and a type
  error is the absence of a derivation. Rules only apply where the OCaml
  `match` would reach them, so the relations are as deterministic as the
  code. Like the OCaml code, an accepted run ends in a state whose bounds
  are ranked (`StructRanked`: a variable's non-variable bounds mention only
  lower-ranked variables, its variable bounds none of higher rank), so
  there are no structural recursive types; cycles of variable bounds are
  allowed. The state has a ghost `log` of every accepted constraint.
  Sanity checks: `fun x -> x`; `1 2` is rejected; in `(fun x -> x) 42`
  propagation gives the result variable the lower bound `int`.
- `Soundness.lean`, the graph level of the paper's Lemma 2. Two invariants
  hold of every state the algorithm reaches. *Justified*: every logged
  constraint is justified by one decomposition step (`GStep`), so the log
  is a self-justifying set of constraints and cache hits are uses of the
  coinductive hypothesis. *Consistent*: every lower bound of a variable is
  logged below each of its upper bounds. The proofs track *pending* pairs,
  since consistency is broken while a new bound propagates.
  `ConstrainTop.sound`: a successful `constrain` call preserves the
  invariant and accepts its constraint; `TypeTerm.inv_init`: the invariant
  holds after typing any term.
- `Solution.lean`, the paper's unifying coalescing. A simple type is
  translated by the position it occurs in: as a type (`toTy`), a row
  (`toRow`) or a field (`toField`, with `Abs` as `⊤` and any other type as
  `pre τ`). Each variable `v` becomes a graph variable defined, at every
  sort, as the intersection of the non-variable upper bounds reachable from
  `v` through variable bounds (`Clo`, an inductive predicate, so cycles need
  no special treatment), translated at that sort. Variables need no sort.
- `SolutionRows.lean`: every accepted constraint `a ≤ b` holds of the
  solution at the row sort, and at the type sort when `a` is not `Abs`
  (`solution_ty`, `solution_row`). Proving a row pair follows the
  algorithm's record case: common fields, labels supplied by row expansion,
  extra fields flowing into the right tail. The coinduction is up to
  transitivity, because a constraint justified through an extruded bound
  only holds through a chain of accepted constraints.
- `Theorem1.lean`: soundness of inference, assuming chains of row-variable
  tails are acyclic (`TailRanked`), and for any renaming of the variables
  (`TypeTerm.soundR`).
- `Kinds.lean` discharges that assumption. The state carries each
  variable's kind (the labels it lacks), fixed for a run; every OCaml run
  is a model run for the kinds it ended up allocating. Every accepted
  constraint is well-kinded and relates rows lacking the same labels, which
  is what `check_kind` checks at run time. So an upper bound `{fs | ρ}` of
  `v` has `kind ρ = kind v ⊎ fs`, strictly larger, and the number of logged
  labels outside a variable's kind ranks the tails.
- `Sorts.lean`: `Abs` never occurs as a parameter or result of a function
  type in accepted constraints or inferred types, so the components of a
  function type translate to types. Constraints with `Abs` on the left are
  row constraints, related at the row sort only.

## Roadmap

Inference is proved against the minimal subtyping rules; the MLsub
equations are deferred to the simplifier's correctness proof, where they
are needed ("option C").

1. Declarative typing: done, including let-polymorphism.
2. A model of the algorithm: done (`Algorithm.lean`).
3. Soundness of constraining (Lemma 2) and of inference (Theorem 1), with
   rows: done. 3a, the graph level (`Soundness.lean`); 3b, from the
   invariant to `Sub` (`Solution.lean`, `SolutionRows.lean`); 3c, Theorem 1
   (`Theorem1.lean`, `Kinds.lean`).
4. Let-polymorphism.
   - 4a, declarative: done (`Typing.lean`).
   - 4b, renamings and interpretations: done. Soundness holds for any
     renaming of graph variables (`TypeTerm.soundR`), and skeleton
     soundness under any interpretation that is an instance of the
     generalized variables (`PTyp.sound`).
   - 4c, generalization: done (`SolutionRows.lean`, `PolyLet.lean`).
     `solution_gen`: if an interpretation reads a `let`'s generalized
     variables, at the type and row sorts, as satisfying their bounds, and
     every other variable as its graph variable, every accepted constraint
     still holds; it needs the bounds of other variables not to mention the
     generalized ones. `PTyp` is the typing skeleton with let-polymorphism:
     contexts hold schemes (`mkScheme`: the generalized variables as fresh
     free variables, constrained by their bounds at the type and row
     sorts), and `let` and `let rec` generalize a list of variables the
     checker vets (`GenOK`). Nested generalizations are proved under an
     instance of the enclosing ones; scheme variables are numbered above
     every free variable in sight, so substitution captures nothing.
   - 4d, instantiation and extrusion, as certificates. Levels and
     extrusion are how the inferencer keeps generalization correct; the
     checker does not need them. Extrusion: done. Justification accepts
     variables as lower bounds; `v ≤ b` through an upper bound `b'` of `v`
     with `b' ≤ b` accepted (`viaL`), and dually through a lower bound
     (`viaR`), both between non-variables so they stay guarded; and row
     expansion through an installed upper bound whose fields are below the
     expanded ones. Instantiation: done. A use of a let-bound name carries
     a renaming, and the checker verifies that it fixes every
     non-generalized variable and that the copies' renamed bounds are
     accepted (`InstOK`). Examples (`Examples.lean`):
     `let id = fun x -> x in id 1` (`∀0. 0 → 0`) and
     `let inc = fun x -> succ x in inc 1` (`∀0 3. 0 ≤ int, int ≤ 3 ⇒ 0 → 3`).
   - Adequacy for skeletons: done for the model without levels
     (`TypeTerm.certificate`, `Adequacy.lean`); with levels and
     instantiation it is tested on the examples instead.
   - Presentation: closed `∀`-types, as MLsub prints them, are equivalent
     to the constrained schemes by coalescing. This needs the MLsub
     equations, so it comes with step 5.
5. The MLsub equations and the simplifier, sequent-style (`Lattice.lean`).
6. A certificate checker ([`../docs/certificates.md`](../docs/certificates.md)).
   - 6a, proofs: done (`Certificate.lean`, `PolyLet.lean`,
     `Adequacy.lean`). Validity is the invariants over the certificate's
     finite lists, including ranks that exclude structural recursive types;
     a skeleton's selection checks that the selected field's type is not
     `Abs`.
   - 6b, programs: done (`Check.lean`, `Main.lean`, `lib/cert.ml`,
     `scripts/check-certs.sh`).
7. Sorts ([`../docs/design/sorts.md`](../docs/design/sorts.md)): done.
   Types, rows and fields are separate sorts, which removed the patches that
   kept `Abs` from acting as a type. Next on this line: optional fields
   (#2) on the field lattice.

## A Lean pitfall

Lean binds unknown lowercase names in signatures as implicit variables,
*unless a constant with that name exists*, in which case the constant is
used silently. Keep example definitions (`τ`, `A`, `M`, …) in their own
namespace or `private`.
