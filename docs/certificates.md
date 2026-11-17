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

## What is proved

In `lean/BoltCore/Check.lean`:

- `Certificate.check c = true → c.Valid`: the Boolean checks imply the
  invariants of the soundness proofs (justification, consistency, bounds
  in the log, `Abs` never a function component, the kind discipline, and a
  ranking that excludes structural recursive types);
- `infer c Γ a = some st → PTyp c Γ a.erase st`: the annotated term has a
  polymorphic typing skeleton;
- `check_sound`: together, `a.erase` has type `st` in the declarative
  system with constrained schemes, over the certificate's solution.

Only this direction is proved: a rejection proves nothing. Not verified:
the JSON parser, the ranks (computed by `boltcore-check` and checked by
`rankedB`), the diagnostics, and that the annotated term is the program as
written.

The other direction, *adequacy*, is proved for the Lean model of the
algorithm without levels (`TypeTerm.certificate`, `Certificate.lean`): an
accepted run yields a valid certificate. For the real typer, with levels
and let-polymorphism, it is tested.

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
- **Extrusion needs no new rule.** The rule expected for it, `w ≤ n`
  through a variable that is an upper bound of `w` and a lower bound of
  `n`, was never needed.
- **What the log needs.** Dropping the extruded pairs or the instantiated
  constraints makes the checker reject programs. The other completions
  (bounds as constraints, lower bounds below upper ones) were never needed
  on these programs; they are kept because they are cheap and can only
  produce certificates the checker rejects.
- **The checker is not vacuous.** Dropping a constraint, claiming a wrong
  result type, or generalizing too little each make it reject.
