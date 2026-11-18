# Bolt's Core

A research testbed for the type system of the Bolt compiler: type
inference with subtyping, after Parreaux's **Simple-sub** (ICFP 2020),
extended with extensible records, implemented in OCaml and verified in
Lean. [`docs/papers/`](docs/papers/README.md) describes each paper the
project builds on and how we differ from it.

```sh
dune build
dune exec -- boltcore -e 'fun f -> fun x -> f (f x)'
dune exec -- boltcore program.sub                     # or read from stdin
dune exec -- boltcore --raw -e '...'                  # coalesced, not simplified
dune exec -- boltcore --rectypes -e '...'             # allow recursive types
dune exec -- boltcore -e '...' --expect "'a -> 'a"    # check modulo equivalence
dune exec -- boltcore --self-check program.sub        # simplified ≡ raw, per item
dune exec -- boltcore --compare "⊤ -> int" "'a -> int" # relate two type schemes
dune exec -- boltcore --cert cert.json program.sub    # print a certificate
dune test                                             # cram snapshots in test/*.t
scripts/check-certs.sh                                # certify every example
```

## Layout

| Path | Contents |
|---|---|
| `lib/` | the type checker: syntax and parser, inference (`typer.ml`), coalescing, simplification, subsumption, certificates |
| `bin/main.ml` | the `boltcore` command |
| `examples/` | commented programs: basics, records, rows, optional fields, unions, polymorphism, recursion, errors |
| `test/` | cram tests: core inference (`core.t`), the examples (`examples.t`), subsumption (`subsume.t`); extra programs for certificates (`certs.txt`) |
| `lean/` | the mechanized metatheory ([`lean/README.md`](lean/README.md)) |
| `scripts/check-certs.sh` | certifies every example and test program with the Lean checker |
| `docs/` | [certificates](docs/certificates.md), [papers](docs/papers/README.md) |
| `papers/` | PDFs of the papers the implementation follows |

## The language

```
program ::= { 'let' ['rec'] x { x } '=' e | e }
e       ::= n | x | fun x { x } -> e | e e | let ['rec'] x { x } = e in e
          | if e then e else e | {l = e; …} | e.l | e.l ?? e | e with {l = e; …}
```

Built-ins: `true`, `false`, `not`, `succ`, `add`, and
`if : ∀α. bool → α → α → α`. Types are MLsub's: primitives, functions,
records, `⊤`, `⊥`, unions in positive and intersections in negative
positions, type variables, and let-polymorphism.

Design decisions that differ from the papers:

- **Extensible records.** `r with {l = e}` adds field `l`, or overwrites
  it, possibly changing its type: `fun r -> r with {y = 1}` has type
  `{y: Abs | 'a} -> {y: int | 'a}`. Records are rows of fields over a tail.
  `Abs` is the *top* field, "no guarantee", and the top row. Row variables
  have kinds, the labels they do not represent. A label may be set only
  once in a `with`. See
  [extensible-records.md](docs/papers/extensible-records.md).
- **Closed records and optional fields** (the first part of #2). A record
  literal has exactly its fields: `{x = 1} : {x: int}`, whose tail is the
  empty row. `{x: int, ..}` is open (tail `Abs`), which is what selection
  asks for: `fun r -> r.x : {x: 'a, ..} -> 'a`. Width subtyping is
  unchanged, since the empty row is below `Abs`. Fields form a lattice:
  `Missing` (definitely absent) and a present field are below the optional
  field `x?: τ`, which is below `Abs`. `r.x ?? d` reads an optional field,
  with `d` when it is missing: `fun r -> r.x ?? 0 : {x?: 'a, ..} -> 'a ∨ int`.
  A field given in one branch only is optional:
  `if b then {y = 1} else {} : {y?: int}`.
- **No structural recursive types** by default: as with an occurs check, a
  type variable may not reach itself through a type constructor (variable
  cycles such as `α ≤ β ≤ α` are fine). Recursive data is meant to be
  nominal, as in Bolt (#4). `--rectypes` restores the paper's
  equi-recursive types.
- **`let rec` only binds functions**, since evaluation is eager.

The full list of deviations from Simple-sub is in
[simple-sub.md](docs/papers/simple-sub.md).

## Checking the checker

**Snapshots.** `dune test` runs the cram tests, so any change in an
inferred type shows up as a diff.

**Subsumption.** `Subsume.subsumes s1 s2` decides `s1 ≤∀ s2`: `s1` is at
least as general as `s2`. The variables of `s1` are flexible, with
Simple-sub-style bounds; those of `s2` are rigid. Recursive types become
cyclic graphs, with coinductive assumptions guarded as in the paper's
Fig. 10 (`▷`/`◁`), and on top of Fig. 10 it uses the MLsub lattice
equations that simplification assumes, e.g. `(a -> b) ∧ (c -> d) ≡ a ∨ c
-> b ∧ d`, and `⋀X ≤ ⋁Y` iff some atom of `X` is below some atom of `Y`.
Both types must be polar (unions only positive, intersections only
negative), so every choice point involves only the rigid side and the check
never backtracks over bound updates. It isn't proven complete for MLsub's
full algebra, but it agrees with every case in `test/subsume.t`.

`--self-check` uses it to verify that simplification preserves meaning; a
deliberately broken simplifier was caught on every affected example,
including one that merges rows unconditionally. For rows it follows the
type checker's expansion rule, with flexible row variables expanded and
memoized per label set, and:

- rows distribute over non-empty unions and intersections of tails;
- rows that can't be merged, on the left against a closed row on the
  right, are compared field by field, and the right tail receives the
  *meet* of their remainders (committing to one left row could bind a
  flexible tail too tightly);
- otherwise each pair of left and right rows is tried, and bounds recorded
  by a failed attempt are rolled back through an undo trail;
- an *unguarded* recursive occurrence, such as `('g ∧ int as 'g)`, is read
  as the neutral element of its context: `⊤` in an intersection, `⊥` in a
  union, as the simplifier reads it.

Inside braces `|` starts the tail, so unions in field types use `∨`:
`{x: int | 'r}`, `{| 'r}`, `{x: int, ..}`, optional fields `x?: int`, and
`Abs` and `Missing` fields.

**Certificates.** `boltcore --cert FILE` prints a certificate of a
program's typing, and `boltcore-check` (Lean) verifies it, with a proof
that an accepted certificate types the program in the declarative system.
Every example and test program is accepted. See
[docs/certificates.md](docs/certificates.md).

## Mechanized metatheory

[`lean/`](lean/README.md) proves, without `sorry`s, against a model of the
type checker:

- **soundness of inference** (the paper's Theorem 1, `theorem1`), with
  rows, row expansion and kinds;
- **soundness of certificates**, with let-polymorphism as constrained
  schemes, and of the executable checker (`check_sound`);
- the **exactness of the row rewrites** in the simplifier and subsumption;
- that selecting a missing field has no type (`not_typ_sel_missing`), and
  the field lattice of optional fields and closed records.

**Roadmap.** Done: declarative typing with let-polymorphism, the
algorithm model, Theorem 1, certificates with generalization,
instantiation and extrusion, and the executable checker. Next: adequacy of
certificates for let-polymorphism (levels in the model), the MLsub lattice
equations and the simplifier's correctness, and the presentation of
inferred types as closed `∀`-types. Details in
[`lean/README.md`](lean/README.md#roadmap).

## Not yet implemented

- Type safety: there is no operational semantics, so no progress or
  preservation.
- Boolean-algebra types (negation, as in
  [MLstruct](docs/papers/mlstruct.md)), and rejecting uninhabited types
  such as `int ∧ bool`.
- Effects, after [Effekt](docs/papers/effekt.md).
- Open issues: named and optional arguments (#2; its optional fields and
  closed records are done), bidirectional checking (#3),
  nominal enums and structs (#4), a polarity-aware check for recursive
  types (#5), first-class polymorphism with
  [SuperF](docs/papers/superf.md) (#6).
