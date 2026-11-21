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

- **Theorem 1** (`theorem1`, `Adequacy.lean`): if the algorithm model types
  `t` with `st` from the built-ins, in a run without structural recursive
  types, then `t : θ(st)` in the declarative system with constrained
  schemes, where `θ` is the solution of the final state. The model has
  levels: `let` generalizes, a use instantiates, and constraining extrudes.
  Rows, row expansion and kinds are included; there are no assumptions.
  The proof goes through the certificate of the run and uses classical
  logic.
- **Certificates** (`PTyp.sound_top`): a valid certificate with a typing
  skeleton with let-polymorphism gives a declarative typing with
  constrained schemes, over a solution without recursive types
  (`Valid.nonrec`). Every accepted run of the model yields one
  (`TypeTerm.certificate`, `Adequacy.lean`), so the checker never rejects
  a correct run of the model.
- **The executable checker** (`check_sound`, `Check.lean`): Boolean checks
  that imply validity and the skeleton, run by `boltcore-check`.
- **Type safety** (`type_safety`, `Safety.lean`): a term that is well-typed
  in the declarative system never evaluates to an error, in a call-by-value
  semantics given as an interpreter with fuel (`Eval.lean`), and a value it
  evaluates to has its type. With the results above: a term the model
  types, and a term whose certificate the checker accepts, do not go wrong
  (`infer_safe`, `check_safe`, `SafeInfer.lean`). Termination is not
  claimed.
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
| `BoltCore/Types.lean` | types, rows and fields as one family indexed by a sort; `Abs` is `⊤` at the field and row sorts; the field `missing` and the empty row `nil`, with `opt τ = pre τ ∪ missing`; parameter lists, whose domain `Ty.sig` is the union of the argument records they accept; no structural recursive types |
| `BoltCore/Sub.lean` | guarded coinductive subtyping, rows compared field by field (`Step.fields`), `Abs ≰ pre τ` (`not_abs_le_pre`); reflexivity, transitivity (cut elimination by sort, for any relation), coinduction up to transitivity, ranked (non-recursive) definitions, the paper's §5.1.3 example with graph variables, row examples |
| `BoltCore/Rows.lean` | row algebra; exactness of the row rewrites in `lib/simplify.ml` and `lib/subsume.ml` |
| `BoltCore/Lattice.lean` | the MLsub lattice equations: what the minimal rules cannot derive (`not_fun_merge`, `not_pre_union`), and the sequent-style plan |
| `BoltCore/Typing.lean` | declarative typing (constrained schemes `∀ᾱ. D ⇒ σ`, with constraints at any sort, for built-ins and let-polymorphism; record extension; selection of present fields `pre τ` only; selection with a default of optional fields; closed record literals; conditionals; functions of a parameter list, `fn`) with examples; selecting a missing field is untypable (`not_typ_sel_missing`), and so is passing an argument twice (`not_twice_le_sig`) |
| `BoltCore/Eval.lean` | operational semantics: values, closures and a call-by-value interpreter with fuel; the binding of arguments to the parameters of a `fn`; the built-ins as values; the calls of issue #2 as examples |
| `BoltCore/Safety.lean` | type safety: typing of values (`VTyp`), canonical forms by inverting one layer of subtyping, argument records against parameter lists (`ArgsOK`), and safety by induction on the fuel (`safe`, `type_safety`) |
| `BoltCore/Algorithm.lean` | model of `lib/typer.ml`: state, levels, extrusion (`Extrude`), `Constrain`, instantiation (`State.instantiate`) and `TypeTerm` as big-step relations; `let` generalizes the variables above its level; signatures `sig P` with their two constraint rules, and `fn`; ranked bounds (`StructRanked`) rule out structural recursive types |
| `BoltCore/Extrusion.lean` | what extrusion leaves alone: it only allocates and adds bounds, its result has level at most the target, it keeps the type constructor, and it does not touch variables of low level |
| `BoltCore/Locality.lean` | locality: a set of variables that is closed under bounds and contains what a run allocates stays closed, and bounds outside it are untouched (`Extrude.local`, `Constrain.local`); scope as an instance (`Scope`: a fresh variable has no bounds) |
| `BoltCore/Justify.lean` | the ghost log as a relation (`Logged`), one step of justification (`GStep`), growth of a state, the two invariants with pending pairs |
| `BoltCore/Rename.lean` | renamings of type variables: what they commute with, and `GStep.rename` (a renaming of a justified constraint is justified) |
| `BoltCore/Levels.lean` | a bound of a variable has at most its level (`LevelInv`), kept by extrusion and constraining |
| `BoltCore/ExtrusionSound.lean` | every pair an extrusion logs is justified (`Extrude.just`); consistency; bounds in the log |
| `BoltCore/Instantiate.lean` | what instantiating a scheme does to a state: growth, scope, consistency, levels, closed sets |
| `BoltCore/Soundness.lean` | soundness of constraining on the bound graph: justification and consistency, preserved by `constrain` with extrusion (`ConstrainTop.sound`, for a state and types in scope) |
| `BoltCore/TypeWf.lean` | typing with levels: locality (`TypeTerm.local`), frames (a run leaves the variables above its level alone, `TypeTerm.frame`), the allocation invariants of every state a run reaches (`TypeTerm.wf`: scope, levels of bounds, consistency) |
| `BoltCore/Solution.lean` | the solution of the inferred constraints (unifying coalescing via graph variables), simple types translated by position (`toTy`, `toRow`, `toField`), and its invariants |
| `BoltCore/Sorts.lean` | `Abs` is never a function parameter or result, and the parameters of a signature are types (`NAC`), preserved by `constrain` and `typeTerm` |
| `BoltCore/SolutionRows.lean` | the solution theorem at the type and row sorts, rows and extrusion-shaped justifications included (assuming acyclic row-variable tails), proved under a generalization (`solution_gen`: generalized variables read, at the type and row sorts, as an instance of their bounds); the plain theorem (`solution_ty`, `solution_row`) is the case where nothing is generalized |
| `BoltCore/Final.lean` | what the solution theorem needs of the final state (`Final`); the fields of inferred records |
| `BoltCore/Kinds.lean` | kinds for row variables: the algorithm keeps rows well-kinded, so tails are acyclic (`kinds_tailRanked`); a copy has the kind of its original |
| `BoltCore/Certificate.lean` | certificates (accepted constraints, bounds, kinds, ranks) and their validity; the certificate of a state that satisfies the invariants is valid (`State.certificate_valid`) |
| `BoltCore/PolyLet.lean` | typing skeletons with let-polymorphism: schemes from generalized variables and their bounds (`mkScheme`), checked generalization (`GenOK`) and instantiation (`InstOK`), soundness (`PTyp.sound_top`; uses classical logic), no recursive types (`Valid.nonrec`) |
| `BoltCore/Adequacy.lean` | every accepted run of the model yields a valid certificate and a skeleton with let-polymorphism (`TypeTerm.certificate`), proved relative to the state the whole run ends in; **Theorem 1** (`theorem1`) |
| `BoltCore/Check.lean` | the executable checker: Boolean checks of validity (`Certificate.check`) and of polymorphic skeletons over annotated terms (`infer`), with `check_sound`: an accepted certificate types the term |
| `BoltCore/SafeInfer.lean` | inferred and certified programs do not go wrong (`infer_safe`, `check_safe`) |
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
`Abs ≤ pre τ` (`not_abs_le_pre`), so `{..} ≤ {x : ⊤, ..}` fails. This
matches `lib/typer.ml`, where an absent field never satisfies a present one.

Optional fields and closed records add one field, `missing` (definitely
absent, an atom related only to itself), and one row, `nil` (`missing` at
every label). An optional field is the union `opt τ = pre τ ∪ missing`, so
its rules are theorems: `pre_le_opt`, `missing_le_opt`, `opt_le_opt`,
`opt_le_abs`. What must not hold does not: `not_missing_le_pre`,
`not_opt_le_pre`, `not_pre_le_missing`, `not_abs_le_missing` and
`not_abs_le_opt` (a forgotten field is not an optional one). For rows:
`nil_le_top` keeps width subtyping, `closed_le_optional` lets an optional
field be left out, and `not_extra_le_closed` and `not_top_le_nil` say that a
closed record has no other fields.

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
shape of the rule. Selection with a default, `t.l ?? d : τ`, requires
`t : {l : opt τ}` and `d : τ`. A record literal's row ends in `nil`.
Selecting a label that a record literal lacks has no type
(`not_typ_sel_missing`: `{}.x`, `{a = 1}.b`); type safety is proved in
`Safety.lean` (below). Examples: `typ_twice`, `typ_if`, `typ_ext`
(the extension example of Marques et al.), `typ_letPoly`,
`typ_letConstrained`.

Parameter lists (issue #2). `fn (x₁ [= d₁], …) -> t` has the type
`Ty.sig P → σ`, where `Ty.sig P` is the union of the closed argument
records `Dₖ`, one per number `k` of arguments passed by position
(`Ty.argRow`); it is a definition, not a constructor. A default is typed
in the scope of the parameters before it (`TypParams`). A call is an
application to an argument record (`Term.call`) and has no rule of its
own; the built-ins take positional-only parameters. The rule asks for a
well-formed parameter list (`Param.WF`): positional-only parameters
without a default, then those with one, then either-way, then
keyword-only parameters, with distinct names. The parser only builds such
lists; type safety needs it, and the checker tests it. Examples: `typ_fn`,
`sig_xy` (the three records of `fn (x, y = 0) -> …`), `typ_call` (`f(1)`),
and `not_twice_le_sig`: the argument record of `f(1, x = 2)` is below none
of the three.

## Type safety (`Eval.lean`, `Safety.lean`, `SafeInfer.lean`)

`eval n ρ t` evaluates `t` in the environment `ρ` with `n` steps of fuel:
`none` if the fuel runs out, `some .err` if evaluation goes wrong (an
unbound name, a number applied, a missing field selected, a wrong argument
list), and `some (.ok v)` for a value. Functions are closures; a `let rec`
binds its name to the closure itself each time it is applied. `t.l ?? d`
evaluates `d` only when the field is missing. A `fn` is called with an
argument record: the arguments passed by position go to the leading
parameters that can take them, each other parameter takes the argument of
its name or the value of its default, evaluated in the scope of the
parameters before it, and every argument has to be taken. So `f(y = 2)`,
`f(1, x = 2)`, `f(1, 2, 3)` and `f(1, z = 2)` are errors of the semantics
for `f = fn (x, y = 10) -> …`, not only of the type checker. The built-in
functions are values. `if c then a else b` is a term (`Term.ite`), not a
function: only the branch that `c` chooses is evaluated, so a recursive
function can stop.

`type_safety`: if `t : τ` from the built-ins, then `eval n builtinEnv t` is
never an error, for any `n`, and a value it gives has type `τ`
(`type_safety_value`). The proof is by induction on the fuel, for
evaluation, application and the binding of arguments together (`Safe`),
following Siek's "three easy lemmas" for definitional interpreters; there
is no substitution, so names being strings is not an issue.

- Values are typed by `VTyp`. A closure has the types of its function in a
  typed environment; a recursive closure the type its function has given
  that its own name has it. An environment gives each name a value that
  has every instance of the name's scheme, which is what the `let` rule
  provides.
- Every rule of `VTyp` ends in a subtyping step, so canonical forms are
  inversions of one layer of `Sub`: a value of a function type is a
  function, a value of a record type is a record whose fields fit the row
  (`VTyp.rcd_inv`), and a value of a union of records is a value of one of
  them (`Sub.unions_inv`), which is how a value of a signature is an
  argument record for some number of positional arguments (`VTyp.args`).
- `ArgsOK.cons` reads the binding of one parameter off the argument record
  `Dₖ`: it takes an argument by position, or by name, or has a default.
  This uses the order of the parameters and their distinct names
  (`Param.WF`).
- The definitions of graph variables are arbitrary: safety does not need
  the solution to be free of recursive types.

Not covered: termination, and a small-step semantics (the interpreter
gives the result of an evaluation, not its steps).

## The algorithm and its soundness

- `Algorithm.lean` models `lib/typer.ml`, levels included. Bounds live in
  an explicit `State`. `Constrain`, row expansion and extrusion included,
  and `TypeTerm` are big-step relations, "succeeds from state `s` with
  state `s'`", and a type error is the absence of a derivation. Rules only apply where the OCaml
  `match` would reach them, so the relations are as deterministic as the
  code. Like the OCaml code, an accepted run ends in a state whose bounds
  are ranked (`StructRanked`: a variable's non-variable bounds mention only
  lower-ranked variables, its variable bounds none of higher rank), so
  there are no structural recursive types; cycles of variable bounds are
  allowed. The state has a ghost `log` of every accepted constraint.
  Sanity checks: `fun x -> x`; `1 2` is rejected; in `(fun x -> x) 42`
  propagation gives the result variable the lower bound `int`; in
  `let id = fun x -> x in id` the parameter is generalized and the use
  instantiates it (`typeTerm_let_id`).
  Simple types have no unions, so the domain of a `fn` is a signature
  `sig P`, with the two rules of `lib/typer.ml`: an argument record below a
  signature is constrained against the argument record `Dₖ` for its number
  of positional arguments (`Constrain.recordSig`), and a signature below a
  record or a signature has every `Dₖ` below it (`Constrain.sigL`).
  Levels (Sec. 3.5): each variable has one, fixed for a run like its kind.
  A bound is installed on a variable only if its level is not above the
  variable's; otherwise it is extruded to that level first (`Extrude`,
  Fig. 7: a variable whose level is too high gets a copy, once per
  polarity, which becomes one of its bounds and gets the copies of its
  bounds on the other side). `let` types its right-hand side one level up
  and generalizes the variables above its level that this allocated
  (`genVars`); a use of the name allocates a copy of each, with the
  renamed bounds (`State.instantiate`).
- `Soundness.lean`, the graph level of the paper's Lemma 2. Two invariants
  hold of every state the algorithm reaches. *Justified*: every logged
  constraint is justified by one decomposition step (`GStep`), so the log
  is a self-justifying set of constraints and cache hits are uses of the
  coinductive hypothesis. *Consistent*: every lower bound of a variable is
  logged below each of its upper bounds. The proofs track *pending* pairs,
  since consistency is broken while a new bound propagates.
  `ConstrainTop.sound`: a successful `constrain` call preserves the
  invariant and accepts its constraint. With extrusion, `v ≤ b` holds
  through the copy `b'` of `b` (`v ≤ b'` as a bound, `b' ≤ b` accepted),
  and every pair an extrusion logs is justified (`ExtrusionSound.lean`).
  Consistency needs a fresh copy to have no bounds, so it is proved for a
  state in scope, on types in scope (`Locality.lean`).
- `TypeWf.lean`, why generalizing is sound. A bound of a variable has at
  most its level (`Levels.lean`), so a variable of level at most `lvl` only
  reaches such variables. A run at level `lvl` is *local* to the variables
  of level at most `lvl` and those it allocates (`TypeTerm.frame`): it
  leaves the others alone. So the variables a `let` generalizes are
  finished once its right-hand side is typed: they keep their bounds, and
  no other variable ever mentions them.
- `Solution.lean`, the paper's unifying coalescing. A simple type is
  translated by the position it occurs in: as a type (`toTy`), a row
  (`toRow`, with the empty row as `nil`) or a field (`toField`, with `Abs`
  as `⊤`, `Missing` as `missing`, `Opt τ` as `opt τ` and any other type as
  `pre τ`). Each variable `v` becomes a graph variable defined, at every
  sort, as the intersection of the non-variable upper bounds reachable from
  `v` through variable bounds (`Clo`, an inductive predicate, so cycles need
  no special treatment), translated at that sort. Variables need no sort.
  A signature is translated to `Ty.sig` of its translated parameters: as a
  type the union of its argument records, as a row the union of their rows.
- `SolutionRows.lean`: every accepted constraint `a ≤ b` holds of the
  solution at the row sort, and at the type sort when `a` is not `Abs`
  (`solution_ty`, `solution_row`). Proving a row pair follows the
  algorithm's record case: common fields, labels supplied by row expansion,
  extra fields flowing into the right tail. A row below the empty row is
  proved separately (`fieldToNil`), by induction on the left row, since the
  right side does not shrink. A record below a signature is below one of
  its argument records, which is closed, so that step needs no induction
  on the right side (`stepFieldClosedG`); a signature on the left is the
  same statement for each of its argument records. The coinduction is up to
  transitivity, because a constraint justified through an extruded bound
  only holds through a chain of accepted constraints.
- `Kinds.lean`: chains of row-variable tails are acyclic (`TailRanked`),
  which the solution theorem assumes. The state carries each
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
- `Adequacy.lean`: a run yields a valid certificate and a skeleton
  (`TypeTerm.certificate`), hence Theorem 1 (`theorem1`). What a `let`
  generalizes and what a use instantiates are checked against the
  certificate, the state the *whole* run ends in, while a derivation only
  knows its own part of the run. So the proof is relative to that final
  state `F`: each part of a run is told that after it nothing touches a
  variable above its level (`Fin`, from the frame of the part after it);
  each `let`-bound name in scope that its generalized variables are
  finished (`Frozen`, which is `GenOK` and what `InstOK` needs); and
  justification is stated over the bounds of `F` and the constraints
  logged so far (`JustLoc`), since the renamed constraints of an
  instantiation are only justified once nothing else mentions the
  generalized variables.

## Roadmap

Inference is proved against the minimal subtyping rules; the MLsub
equations are deferred to the simplifier's correctness proof, where they
are needed ("option C").

1. Declarative typing: done, including let-polymorphism.
2. A model of the algorithm: done (`Algorithm.lean`).
3. Soundness of constraining (Lemma 2) and of inference (Theorem 1), with
   rows: done. 3a, the graph level (`Soundness.lean`); 3b, from the
   invariant to `Sub` (`Solution.lean`, `SolutionRows.lean`); 3c, Theorem 1
   (`Adequacy.lean`, with `Kinds.lean`). Theorem 1 was first proved
   directly on a run of a model without levels; it now goes through the
   certificate of the run.
4. Let-polymorphism.
   - 4a, declarative: done (`Typing.lean`).
   - 4b, interpretations: done. Skeleton soundness holds under any
     interpretation that is an instance of the generalized variables
     (`PTyp.sound`).
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
   - 4d, instantiation and extrusion, in certificates. Levels and
     extrusion are how the inferencer keeps generalization correct; the
     checker does not need them. Extrusion: done. Justification accepts
     variables as lower bounds; `v ≤ b` through an upper bound `b'` of `v`
     with `b' ≤ b` accepted (`viaL`), and dually through a lower bound
     (`viaR`), both between non-variables so they stay guarded; between
     variables, through a variable that is an upper bound of one and a
     lower bound of the other (`viaVar`, needed from three levels on); and row
     expansion through an installed upper bound whose fields are below the
     expanded ones. Instantiation: done. A use of a let-bound name carries
     a renaming, and the checker verifies that it fixes every
     non-generalized variable and that the copies' renamed bounds are
     accepted (`InstOK`). Examples (`Examples.lean`):
     `let id = fun x -> x in id 1` (`∀0. 0 → 0`) and
     `let inc = fun x -> succ x in inc 1` (`∀0 3. 0 ≤ int, int ≤ 3 ⇒ 0 → 3`).
   - 4e, levels in the model, and adequacy: done
     ([`../docs/design/levels.md`](../docs/design/levels.md)). The model
     generalizes, instantiates and extrudes as `lib/typer.ml` does, and
     every accepted run yields a valid certificate and a skeleton
     (`TypeTerm.certificate`, `Adequacy.lean`). Two programs the checker
     used to reject were found on the way; `GStep` has a rule and a weaker
     premise since (`viaVar`, and the first field of each label in a record
     step).
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
