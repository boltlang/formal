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
- **Kinds** (Rémy). A row variable's kind is the set of labels it does
  *not* represent, because the record it is the tail of lists them; a label
  in the kind projects to `Abs` from the variable. `r with {L = …}` creates
  a row variable of kind `L` (`r with {}` is just `r`). Expansion never
  expands labels in the tail's kind, and gives `ρ'` the strictly larger
  kind `kind ρ ∪ L`. `constrain` checks, whenever it installs a bound, that
  both sides have the same kind; a failure would be a type-checker bug.
  The simplifier only merges variables of equal kind. Subsumption infers
  the kinds of variables in user-written types from their use as tails, so
  `{| 'a} -> {y: int | 'a}` (where `'a` lacks `y`) is equivalent to
  `{y: Abs | 'a} -> {y: int | 'a}`.
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
- When rows that can't be merged meet on the left, they're compared field
  by field against the right row, and its tail receives the *meet* of the
  rows' remainders. Committing to a single left row could bind a flexible
  tail too tightly and make a later, valid comparison fail.

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
- `SimpleSub/Solution.lean`: the solution (the paper's unifying
  coalescing). Each type variable `v` becomes a *graph variable* `gvar v`,
  defined as the intersection of the non-variable upper bounds reachable
  from `v` through variable-to-variable bounds (`Clo`, an inductive
  predicate, so cycles need no special treatment).
- `SimpleSub/SolutionRows.lean`: every accepted constraint `a ≤ b` gives
  `θ(a) ≤ θ(b)` (`solution_rows`). The coinductive relation also holds the
  *field projections* of accepted constraints. Proving a field pair follows
  the algorithm's record case: common fields, labels supplied by row
  expansion, extra fields flowing into the right tail. The coinduction is
  up to transitivity (`Sub.coind_trans`), because a constraint justified
  through an extruded bound only holds through a chain of accepted
  constraints. Variables may be lower bounds. It assumes chains of
  row-variable tails are acyclic (`TailRanked`), which kinds guarantee
  (`Kinds.lean`).
- `SimpleSub/Theorem1.lean`: **soundness of type inference** (the paper's
  Theorem 1, for our model). If the algorithm types `t` with `st` from the
  built-in context, then `t : θ(st)` in the declarative system, where `θ`
  is the solution of the final state (`soundness`). Every constraint the
  algorithm solved becomes a subsumption step. It assumes that
  row-variable tails are acyclic (`TailRanked`).
- `SimpleSub/Kinds.lean`: **kinds** discharge that assumption, giving
  Theorem 1 with no assumptions (`theorem1`). The model's state carries
  each variable's kind (the labels it lacks), and expansion leaves labels
  in the tail's kind absent, as in `lib/typer.ml`. The kind map is fixed
  for a run, and the rules that allocate a variable require it to have
  the right kind: every OCaml run is a model run for the kinds it ended up
  allocating. The invariant: every accepted constraint is well-kinded (a
  record over a row variable lists at least one label, all lacked by the
  variable) and relates rows lacking the same labels, which is what
  `check_kind` checks at run time. So an upper bound `{fs | ρ}` of `v`
  has `kind ρ = kind v ⊎ fs`, strictly larger, and the number of logged
  labels outside a variable's kind ranks the tails.
- `SimpleSub/Sorts.lean`: `Abs` never occurs as a parameter or result of a
  function type in accepted constraints or inferred types. `Abs` is the top
  of `Sub`, so `Abs ≤ {…}` must stay false at the level of types. Row
  constraints with `Abs` on the left are only ever compared field by
  field.

These are proofs about a model of the code, not the OCaml itself.

**Roadmap ("option C").** Inference is proved against the minimal subtyping
rules. The MLsub equations are deferred to the simplifier's correctness
proof, where they are needed.
1. Declarative typing. Done, including let-polymorphism (4a).
2. A model of the algorithm. Done: `Algorithm.lean`.
3. Soundness of constraining (the paper's Lemma 2), then of inference
   (Theorem 1), including row expansion.
   - 3a, the graph level: done (`Soundness.lean`).
   - 3b, from the invariant to `Sub`: done (`Solution.lean`,
     `SolutionRows.lean`), assuming acyclic row-variable tails
     (`TailRanked`).
   - 3c, Theorem 1: done (`Theorem1.lean`, and `Kinds.lean`, where kinds
     discharge `TailRanked`).
4. Let-polymorphism.
   - 4a, declarative: done (`Typing.lean`). Constrained schemes
     `∀ᾱ. D ⇒ σ`, as in HM(X): an instance substitutes types for `ᾱ` such
     that the constraints `D` hold. `let` gives `x` a scheme when `s` has
     every instance of it, and it has one. The constraints are read
     through their instances, as HM(X) defines entailment, instead of
     typing `s` under them as hypotheses: subtyping under both lower and
     upper bounds is not transitive in general ("bad bounds"). A
     monomorphic `let` is the scheme with no variables. No value
     restriction (no mutable state).
   - 4b, renaming and interpretations: done. The soundness proof holds
     for any renaming of graph variables (`TypeTerm.soundR`), and
     certificate soundness for any interpretation of the variables
     under which the constraints hold (`CTyp.soundI`).
   - 4c, generalization: to do. The certificate lists the generalized
     variables `A` of each `let`. The scheme is the inferred type with
     `A` read as free variables, constrained by their bounds. For each
     instance `φ` satisfying those bounds, the accepted constraints hold
     under the interpretation that reads `α ∈ A` as `φ(α)` and every
     other variable as its graph variable. This generalizes the solution
     theorem: variables of `A` are related through the bounds `φ`
     satisfies instead of through definitions. It needs the bounds of
     variables outside `A` not to mention `A`, which the checker
     verifies. `CTyp.soundI` then types the right-hand side at each
     instance. No recursive types or coalescing are needed.
   - 4d, instantiation and extrusion, as certificates. Levels and
     extrusion are how the inferencer keeps generalization correct; the
     checker does not need them as an algorithm.
     - Extrusion: done. Justification accepts what extrusion produces:
       variables as lower bounds; `v ≤ b` through an upper bound `b'` of
       `v` with `b' ≤ b` accepted (`viaL`), and dually `a ≤ v` through a
       lower bound `a'` with `a ≤ a'` accepted (`viaR`), both between
       non-variables so they stay guarded; and row expansion through an
       installed upper bound whose fields are below the expanded ones.
       The solution theorem holds for all of these (coinduction up to
       transitivity), so certificates no longer need "no variable lower
       bounds".
     - Instantiation: to do. A certificate records each instantiation's
       renaming `ρ`, and the checker verifies the copies carry the
       renamed bounds. Then `α ↦ θ(ρα)` satisfies the scheme's
       constraints by the solution theorem, so the type the use needs,
       `θ(ρ st)`, is an instance.
   - Presentation: closed `∀`-types (MLsub's, as printed) are equivalent
     to the constrained schemes by coalescing. This needs the MLsub
     equations, so it comes with step 5.
5. The MLsub equations and the simplifier, sequent-style (see
   `Lattice.lean`).
6. A certificate checker. The inferencer (`lib/typer.ml` now, Bolt's
   compiler later) emits its result: the type of each node, and the final
   bounds and accepted constraints. A Lean checker decides the invariants
   the soundness proofs rely on (justification, consistency, kinds, `Abs`
   only in rows), so Theorem 1 applies to every accepted certificate.
   - 6a, proofs: done (`Certificate.lean`). A certificate lists the
     accepted constraints, the bounds and the kinds; validity is the
     invariants over those finite lists. Soundness (`CTyp.sound`): a
     valid certificate with a typing skeleton for a term gives its
     declarative typing. Adequacy (`TypeTerm.certificate`): every run of
     the model yields a valid certificate and skeleton, so a correct
     inferencer is never rejected.
   - 6b, programs: to do. Boolean checks with proofs that they decide
     validity and skeletons, and certificate output from `lib/typer.ml`.

## Not yet implemented

- Boolean-algebra types (negation, MLstruct), and rejecting uninhabited
  types such as `int ∧ bool`.
