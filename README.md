# simplesub

An OCaml port of the core of **Simple-sub**, from Lionel Parreaux,
*The Simple Essence of Algebraic Subtyping* (ICFP 2020), in `papers/`.
It's a research testbed for the type system of the Bolt compiler.

```sh
dune build
dune exec -- simplesub -e 'fun f -> fun x -> f (f x)'
dune exec -- simplesub program.sub      # or read from stdin
dune exec -- simplesub --raw -e '...'   # skip simplification (Sec. 3.3 output)
dune exec -- simplesub -e '...' --expect "'a -> 'a"   # check modulo equivalence
dune exec -- simplesub --self-check program.sub      # simplified ≡ raw, per item
dune exec -- simplesub --compare "⊤ -> int" "'a -> int" # relate two type schemes
dune test                                # cram snapshots in test/*.t
```

`examples/` has commented sample programs: basics, records, unions,
polymorphism, recursion and errors. Their output is snapshotted in
`test/examples.t`, so a change in inferred types shows up as a test diff.

## Map to the paper

| Paper | Code |
|---|---|
| Fig. 4: `Term` | `lib/syntax.ml` |
| Fig. 6: `SimpleType`, `VariableState`, `PolymorphicType` | `lib/types.ml` (`simple_type`, `var_state`, `type_scheme`) |
| Fig. 5: user-facing `Type` | `lib/types.ml` (`typ`, `show_typ`) |
| Fig. 8: `typeTerm` | `lib/typer.ml` (`type_term`, `type_let_rhs`) |
| Fig. 9: `constrain` | `lib/typer.ml` (`constrain`) |
| Fig. 7: `extrude` | `lib/typer.ml` (`extrude`) |
| §3.5.1: `freshenAbove` / `instantiate` | `lib/typer.ml` |
| §3.3.3: `coalesceType` | `lib/coalesce.ml` |
| §4.4: `CompactType`, `compactType` | `lib/simplify.ml` (`compact`, `compact_type`) |
| §4.3.1: co-occurrence analysis, `simplifyType` | `lib/simplify.ml` (`simplify`) |
| §4.3.2: hash consing, `coalesceCompactType` | `lib/simplify.ml` (`coalesce_compact`) |
| subsumption `≤∀` (outside the paper's scope) | `lib/subsume.ml` (`subsumes`, `relate`) |
| type syntax | `lib/parser.ml` (`parse_type`) |

## Subsumption

`Subsume.subsumes s1 s2` decides `s1 ≤∀ s2`: `s1` is at least as general as
`s2`. The variables of `s1` are instantiable (flexible, with Simple-sub-style
bounds); those of `s2` are rigid. Recursive types become cyclic graphs, and
the coinductive assumptions are guarded as in the paper's Fig. 10 (`▷`/`◁`).
On top of Fig. 10 it uses the MLsub lattice equations that simplification
assumes. For example, `(a -> b) ∧ (c -> d) ≡ a ∨ c -> b ∧ d`, and
`⋀X ≤ ⋁Y` holds iff some atom of `X` is below some atom of `Y`.

Both types must be polar: unions only in positive positions, intersections
only in negative ones. That guarantees every choice point (a union on the
right, an intersection on the left) involves only the rigid side, so the
check never backtracks over bound updates. The check isn't proven complete
for MLsub's full algebra, but it agrees with every case in
`test/subsume.t`.

`--self-check` uses it to verify that simplification preserves meaning. A
deliberately broken simplifier was caught on every affected example.

## Deviations from the paper

- **Reflexive constraints are skipped.** `constrain` returns immediately
  when `lhs` and `rhs` are equal, and the paper's Fig. 9 doesn't. Without
  the check, `α <: α` records α as its own bound. That's sound, but it
  coalesces to junk like `('a ∧ 'b as 'b)`.
- **`level` is recomputed** on every call instead of being cached in a
  `lazy val`.
- **The constraint cache** is a hash table keyed on structural equality
  where variables compare by identity (`Types.equal` / `Types.hash`). This
  mirrors Scala's case-class equality.
- **Built-ins** follow the reference implementation: `true`, `false`, `not`,
  `succ`, `add`, and `if : ∀α. bool → α → α → α`.
- **§4 is re-implemented from the paper's description.** The paper doesn't
  show the code, and there's no `canonicalizeType` pass. Variable
  unification is greedy and its rewrites don't commute: one merge can block
  another, so different orders give different (but equivalent) types. The
  order is fixed canonically. Variables are visited by first appearance in
  the inferred type, never by internal id, and all negative merges run
  before positive ones. That reproduces the paper's
  `twice : ('a ∨ 'b -> 'a) -> 'b -> 'a`.
- **Simplification relies on MLsub's lattice assumptions** (§4.1). For
  example, `(a -> b) ∧ (c -> d)` is merged into `a ∨ c -> b ∧ d`, and a
  union of records keeps only the common fields. Those merges would be
  unsound for overloading or flow typing.

## Not yet implemented

- Boolean-algebra types (negation, MLstruct), and rejecting uninhabited
  types such as `int ∧ bool`.
