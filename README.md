# simplesub

An OCaml port of the core of **Simple-sub**, from Lionel Parreaux,
*The Simple Essence of Algebraic Subtyping* (ICFP 2020), in `papers/`.
It's a research testbed for the type system of the Bolt compiler.

```sh
dune build
dune exec -- simplesub -e 'fun f -> fun x -> f (f x)'
dune exec -- simplesub program.sub      # or read from stdin
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

## Not yet implemented

- §4 type simplification: co-occurrence analysis, polar-variable removal,
  sandwich flattening, hash consing, and the `CompactType` IR. Printed types
  are therefore coalesced but unsimplified.
- A subsumption check (`≤∀`), which would let tests compare against
  expected types modulo equivalence instead of using textual snapshots.
