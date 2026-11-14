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

`examples/` has commented sample programs: basics, records, rows (record
extension and update), unions, polymorphism, recursion and errors. Their output is snapshotted in
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

## Extensible records

`r with {l = e}` adds field `l`, or overwrites it if present, possibly
changing its type. This follows Marques, Florido & Vasconcelos, *Towards
Algebraic Subtyping for Extensible Records* (2024), in `papers/`:

- A row is `Record (fields, tail)`. Each field is `Abs` or a type `τ`
  (Rémy's `Pre τ`), and the tail is `Abs` or a row variable. `Abs` is the
  *top* field (`Pre τ ≤ Abs`): it means "no guarantee", not "known
  absent". Plain records `{x: τ}` are rows with tail `Abs`, so width
  subtyping is unchanged.
- `r with {l = e}` constrains `r ≤ {l: Abs | ρ}` and has type
  `{l: τ | ρ}`. Overwrite semantics means no "lacks" constraint is needed.
- **Deviation from the paper:** the paper expands a row variable by
  substituting into it. We expand through constraints instead. For
  `{fs₀ | ρ} ≤ {fs₁ | t₁}`, where `fs₁` has labels `L` that `fs₀`
  doesn't, we add `ρ ≤ {L-fields | ρ'}` and `{fs₀ ∖ fs₁ | ρ'} ≤ t₁`.
  `ρ'` is memoized per `(ρ, L)`, so recursive types terminate.
- **Simplification of rows:** compact types keep a list of rows. Two rows
  are merged only when every label missing from one of them is known there
  (its tail is `Abs`). Otherwise the field types live inside a row variable,
  and merging would change the type.
- **Covered by the safety net:** subsumption supports rows, so
  `--self-check` checks every rows example, and `--expect`/`--compare`
  accept row syntax: `{x: int | 'r}`, `{| 'r}`, and `Abs` fields. Inside
  braces `|` starts the tail, so unions in field types use `∨`.

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
deliberately broken simplifier was caught on every affected example. That
includes, for rows, a simplifier that merges rows unconditionally.

Rows follow the type checker's expansion rule, with flexible row variables
expanded and memoized per label set. A few more rules apply:

- Rows distribute over non-empty unions and intersections of tails.
- When rows that can't be merged meet on the left against a closed row on
  the right, they're compared field by field.
- Otherwise, the check tries each pair of left and right rows. Bounds
  recorded by a failed attempt are rolled back through an undo trail, so a
  failed attempt can't cause spurious failures later.
- An *unguarded* recursive occurrence, such as `('g ∧ int as 'g)`, which
  raw coalescing produces for variable cycles, is read as the neutral
  element of its context: `⊤` in an intersection, `⊥` in a union. This is
  the reading the simplifier uses when it drops such cycles.
- Row kinds aren't checked, so ill-kinded types such as
  `{| 'a} -> {y: int | 'a}` get conservative answers.

## Deviations from the paper

- **Raw coalescing only produces contractive types.** Every recursive
  occurrence is under a function or record field. A variable cycle with no
  constructor in between, like `α ≤ β ≤ α`, gives the neutral element of
  its context (`⊥` in a union, `⊤` in an intersection). The paper's
  §3.3.3 would give an unguarded `μα. … ∧ α` here instead. Under the
  paper's own Fig. 10, `X ≤ μα. X ∧ α` isn't derivable: it needs a
  hypothesis that's never unlocked. So such a type is strictly below `X`,
  but the simplifier (the paper's and ours) drops these cycles, which would
  be unsound. Emitting only contractive types removes the conflict. The
  Lean development (`lean/SimpleSub/Types.lean`) is restricted to
  contractive types too.
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

## Mechanized metatheory (Lean)

`lean/` is a Lake project on Lean v4.35.0, with no Mathlib. Run `lake build`
in `lean/`. Everything below is proved; there are no `sorry`s.

- `SimpleSub/Syntax.lean`: terms, mirroring `lib/syntax.ml`.
- `SimpleSub/Types.lean`: types with rows, μ-binders as de Bruijn
  indices (locally nameless), local closedness, contractiveness, and the
  *unguarded size* `ug`. That's the size of the part not under a function
  type or record field. Unfolding a contractive μ strictly decreases it
  (`ug_open`).
- `SimpleSub/Sub.lean`: declarative subtyping with equi-recursive types.
  `Step E R` is one layer of subtyping. It's inductive and uses the
  coinductive hypothesis `R` only under a function type or record field,
  which is the paper's ▷/◁ discipline. `E` gives *graph variables*
  (`gvar`) their meaning as intersections of sets of upper bounds: named,
  possibly mutually recursive definitions without binders, used to express
  solutions. `Sub` is the greatest fixed point
  (Knaster–Tarski), with a coinduction principle `Sub.coind`. Proved so far:
  - `Sub.refl`: every closed contractive type is a subtype of itself.
  - `Sub.trans`: transitivity, with no side conditions (not even
    contractiveness). The proof is cut elimination on single layers
    (`cut`): induction on the two finite derivations, with the composed
    relation as the coinductive hypothesis.
  - `Sub.unfold`/`Sub.fold` (S-Rec): `μα. a ≡ a[μα. a/α]`.
  - `paper_example`: the paper's §5.1.3 example,
    `μα₀. τ → τ → α₀ ≤ μα₁. τ → α₁`.
  - `M_le_int` and `not_int_le_M`: the non-contractive `μα. int ∧ α` is
    strictly below `int`. This is why raw coalescing only emits contractive
    types.
  - `field_in_compound_tail`, `bottom_tail`, `nested_tail`: row facts
    that need tails to be looked into. One is the shape the simplifier
    produces for `count`. `not_empty_le_field` checks the other direction.

  Records are compared as rows, i.e. total maps from labels to fields:
  `{fs | t} ≤ {gs | u}` when every label's field is related. `Ty.field`
  looks a label up in the explicit fields, then in the tail. A row
  variable's fields are opaque atoms `proj l ρ`. Not covered yet: recursive
  rows in tail position (kept opaque), kinds, and the MLsub lattice
  equations. The OCaml code uses five such equations that aren't derivable
  yet: merging intersections and unions of functions, merging intersections
  and unions of records, and distributing a row over a union of tails.
  Adding them while keeping transitivity is the next milestone.
- `SimpleSub/Rows.lean`: the row algebra. Rows are modeled by what they
  denote: a total map from labels to fields, with explicit fields
  overriding the tail. Each theorem shows a row rewrite in the OCaml code
  preserves that denotation:
  - `merge_exact`: merging two rows is exact under the covers condition
    (`add_row` in the simplifier, `merge_rows` in subsumption).
  - `merge_inexact`: without the condition, merging is wrong. This is
    the bug the mutation test introduced.
  - `combine_sound`: combining two atomic tails is the pointwise meet or
    join, given the lattice laws for `Abs` (top) and `⊥`.
  - `drop_abs_fields`: dropping `Abs` fields when the tail is `Abs`
    (`mk_row`) is exact, provided labels are distinct.
  - `flatten`: nested rows flatten to appended fields (`mk_row`,
    `row_view`, `norm_row`).

- `SimpleSub/Lattice.lean`: the MLsub lattice equations. `not_fun_merge`
  proves that function merging isn't derivable from the minimal rules. The
  file header records the sequent-style plan for adding the equations.
- `SimpleSub/Typing.lean`: declarative typing over the minimal subtyping
  rules. `let` is monomorphic for now, but contexts hold schemes, so
  built-ins like `if` instantiate. It includes record extension, and the
  examples `typ_twice`, `typ_if` and `typ_ext` (the extension example of
  Marques et al.).
- `SimpleSub/Algorithm.lean`: a model of `lib/typer.ml` and
  `lib/coalesce.ml`, without levels. Bounds live in an explicit `State`.
  `Constrain`, including row expansion, and `TypeTerm` are big-step
  relations: "succeeds from state `s` with state `s'`". A type error is the
  absence of a derivation. Rules only apply where the OCaml `match` would
  reach them, so the relations are as deterministic as the code.
  Coalescing is a function, contractive like `lib/coalesce.ml`. Sanity
  checks: `fun x -> x`, `1 2` is rejected, and in `(fun x -> x) 42`
  propagation gives the result variable the lower bound `int`. The state
  has a ghost `log` of every accepted constraint, which exists only for
  the proofs.
- `SimpleSub/Soundness.lean`: soundness of constraining at the level of the
  bound graph (the first half of the paper's Lemma 2). Two invariants hold
  of every state the algorithm reaches:
  - **Justified:** every logged constraint is justified by one
    decomposition step (`GStep`), so the log is a self-justifying set of
    constraints, and cache hits are uses of the coinductive hypothesis.
  - **Consistent:** every lower bound of a variable is logged below each of
    its upper bounds.

  The proofs track *pending* pairs, since consistency is temporarily broken
  while a new bound propagates. `ConstrainTop.sound`: a successful
  `constrain` call preserves the invariant and accepts its constraint.
  `TypeTerm.inv_init`: the invariant holds after typing any term.
- `SimpleSub/Solution.lean`: from the invariant to `Sub` (the paper's
  unifying coalescing), proved for the record-free fragment. Each type
  variable `v` becomes a *graph variable* `gvar v`, defined as the
  intersection of the non-variable upper bounds reachable from `v` through
  variable-to-variable bounds (`Clo`, an inductive predicate, so cycles
  need no special treatment). `clo_logged` closes chains of variable
  bounds. `solution`: every accepted constraint `a ≤ b` gives
  `θ(a) ≤ θ(b)`.
- `SimpleSub/SolutionRows.lean`: the same for all simple types, rows
  included (`solution_rows`). The coinductive relation also holds the
  *field projections* of accepted constraints. Proving a field pair follows
  the algorithm's record case: common fields, labels supplied by row
  expansion, extra fields flowing into the right tail. It assumes chains of
  row-variable tails through upper bounds are acyclic (`TailRanked`), which
  kinds would guarantee (issue #1).
- `SimpleSub/Sorts.lean`: `Abs` never occurs as a parameter or result of a
  function type in accepted constraints or inferred types. `Abs` is the top
  of `Sub`, so `Abs ≤ {…}` must stay false at the level of types. Row
  constraints with `Abs` on the left are only ever compared field by
  field.

These are proofs about a model of the code, not the OCaml itself.

**Roadmap ("option C").** Inference is proved against the minimal subtyping
rules. The MLsub equations are deferred to the simplifier's correctness
proof, where they are needed.
1. Declarative typing. Done for monomorphic `let`.
2. A model of the algorithm. Done: `Algorithm.lean`.
3. Soundness of constraining (the paper's Lemma 2), then of inference
   (Theorem 1), including row expansion.
   - 3a, the graph level: done (`Soundness.lean`).
   - 3b, from the invariant to `Sub`: done (`Solution.lean`,
     `SolutionRows.lean`). It assumes acyclic row-variable tails
     (`TailRanked`); kinds should discharge that.
   - 3c: Theorem 1, assembling the typing derivation from `TypeTerm`.
4. Let-polymorphism (levels and extrusion).
5. The MLsub equations and the simplifier, sequent-style (see
   `Lattice.lean`).

## Not yet implemented

- **Kinds for row variables** (Rémy): the set of labels a row variable is
  guaranteed not to contain. Without them, ill-kinded types such as
  `{| 'a} -> {y: int | 'a}`, where `'a` is used both with and without `y`,
  are accepted. Both the subsumption checker and the Lean subtyping relation
  then answer conservatively. Kinds are needed in inference, in
  `lib/subsume.ml`, and in `lean/SimpleSub/Sub.lean`.
- Boolean-algebra types (negation, MLstruct), and rejecting uninhabited
  types such as `int ∧ bool`.
