# Certificates

The type checker's results can be checked by a small verified program
instead of trusting the type checker (roadmap step 6). The inferencer,
`lib/typer.ml` now and Bolt's compiler later, prints a *certificate* of its
work; a checker written in Lean decides whether it is valid, and a valid
certificate proves that the program has its type in the declarative
system.

```sh
dune exec -- boltcore --cert cert.json program.sub
(cd lean && lake exe boltcore-check ../cert.json)
scripts/check-certs.sh -v        # every example and test program
```

## What a certificate is

- the **accepted constraints**: a log of subtyping constraints, each of
  which must be justified by one decomposition step from the others and
  from the bounds;
- the **bounds** of each variable, which must be consistent (every lower
  bound accepted below every upper bound);
- the **kinds** of the row variables;
- the program as an **annotated term** (`Ann` in Lean): the term with the
  types a checker cannot compute bottom-up, i.e. parameter and result
  types, the rows of extensions, the generalized variables of each `let`,
  and the renaming at each use of a let-bound name.

The JSON format is documented in `lean/Main.lean`. A program becomes one
term: each item is a `let` around the rest, and items with type errors are
left out.

Parameter lists need nothing new in the format beyond the signature type
and the `fn` term, which carries the type of each parameter. What
`constrain` goes through for a signature is in the log already: the
argument record chosen for a call, and each argument record of a signature
compared with another type. An extruded signature is never constrained
against its original, so `Typer.note_sig` records what a step of the
checker needs for the pair: each argument record of the lower signature
below the upper signature and below its record for the same number of
positional arguments, and their lists of positional arguments.

## What is proved

In `lean/BoltCore/Check.lean`:

- `Certificate.check c = true → c.Valid`: the Boolean checks imply the
  invariants of the soundness proofs (justification, consistency, bounds
  in the log, `Abs` never a function component, the kind discipline, and a
  ranking that excludes structural recursive types);
- `infer c Γ a = some st → PTyp c Γ a.erase st`: the annotated term has a
  polymorphic typing skeleton;
- `check_sound`: together, `a.erase` has type `st` in the
  declarative system with constrained schemes (types, rows and fields are
  separate sorts, see [design/sorts.md](design/sorts.md)), over the
  certificate's solution.

With type safety (`lean/BoltCore/Safety.lean`), `check_safe`
(`SafeInfer.lean`): a program whose certificate is accepted does not go
wrong, in the operational semantics of `lean/BoltCore/Eval.lean`. The
checker also tests that each parameter list is well-formed (in order, with
distinct names), which the OCaml parser guarantees and type safety needs.

Only this direction is proved: a rejection proves nothing. Not verified:
the JSON parser, the ranks (computed by `boltcore-check` and checked by
`rankedB`), the diagnostics, and that the annotated term is the program as
written.

The other direction, *adequacy*, is proved for the Lean model of the
algorithm (`TypeTerm.certificate`, `Adequacy.lean`): an accepted run yields
a valid certificate and a skeleton the checker's rules accept. The model
has levels, extrusion, generalization and instantiation, as `lib/typer.ml`
does ([design/levels.md](design/levels.md)). It is a model: that the OCaml
code runs as the model does is not proved, and the script below tests it.

## How the typer produces one

`lib/cert.ml`, with recording hooks in `lib/typer.ml`. The log is what
`constrain` accepts, plus what inference relies on without constraining:

- the relation of each extruded type to its original (`extrude` records
  it);
- at each use of a let-bound name, a renamed copy of the scheme's
  constraints. Every generalized variable needs a copy, so the variables
  `freshen_above` does not reach get one too (`complete_copies`);
- each bound as a constraint, and each lower bound below each upper bound.

Each `let` generalizes all the variables above its level that its
right-hand side created, not only those reachable from its type. Otherwise
an unreachable variable (the bounds of an unused parameter, say) mentions
generalized ones, and generalization fails (`GenOK`).

## Results

`scripts/check-certs.sh` certifies `examples/*.sub`, the `-e` programs of
`test/*.t` and `test/certs.txt`, which stresses extrusion under nested
`let`s. Every program is accepted, some without their ill-typed items;
`--rectypes` programs are not certified, since the Lean development has no
recursive types.

- **A real mismatch was found.** In `{a = 0} with {a = 1; a = true}`, OCaml
  kept the last binding of the repeated label, while the Lean rule takes the
  first. A label repeated in a `with` is now a parse error.
- **Extrusion needs one rule of its own.** Between variables, `v ≤ w`
  through a variable `m` that is an upper bound of `v` and a lower bound of
  `w` (`GStep.viaVar`). It takes three levels to need it: a variable that is
  a lower bound of another, both inside an inner `let`, extruded past an
  outer one. The first programs did not have that, and the rule was added
  when one was found that the checker rejected
  (`fn (a) -> let f(x) = let g(y) = a(if true then x else y) in g in f`).
- **A step compares the first field of each label.** A record literal may
  repeat a label, and a step used to compare every field of the right side
  with the first of that label on the left, as `constrain` does. An
  extruded copy of such a record is not below the original in that sense,
  so the checker rejected `fn (a) -> let f(x) = a({l = x; l = 1}) in f`.
  A shadowed field has no meaning (`Ty.field` takes the first), and a step
  now ignores it.
- **What the log needs.** Dropping the extruded pairs or the instantiated
  constraints makes the checker reject programs. The lower bounds below
  upper ones are what consistency asks for in the three-level program
  above. That bounds are constraints was never needed on these programs;
  it is kept because it is cheap and can only produce certificates the
  checker rejects.
- **The checker is not vacuous.** Dropping a constraint, claiming a wrong
  result type, or generalizing too little each make it reject.
