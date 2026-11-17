# The Simple Essence of Algebraic Subtyping

Lionel Parreaux. *The Simple Essence of Algebraic Subtyping: Principal Type
Inference with Subtyping Made Easy (Functional Pearl).* ICFP 2020, PACMPL 4,
article 124. [doi:10.1145/3409006](https://doi.org/10.1145/3409006).
Local copy: [`papers/simple-essence-algebraic-subtyping.pdf`](../../papers/simple-essence-algebraic-subtyping.pdf).

**Status: the basis of the implementation and of the Lean development.**

## What the paper does

MLsub (Dolan and Mycroft, POPL 2017) extends Hindley–Milner with subtyping
and still infers compact principal types, but it is specified through
biunification and polar types. Simple-sub gets the same results with a
plainer algorithm:

- type variables carry mutable lists of lower and upper bounds, and
  `constrain` decomposes constraints and propagates bounds, using a cache
  for recursive types (§3.2);
- levels keep let-polymorphism sound, and *extrusion* copies a type to a
  lower level when a variable of that level is constrained against it
  (§3.5);
- *coalescing* turns bounds into user-facing union and intersection types,
  with `μ` for recursive ones (§3.3);
- simplification by co-occurrence analysis and hash consing (§4);
- §5 gives minimal declarative subtyping rules (Fig. 10) and sketches
  soundness and completeness for the version without let-polymorphism. The
  full proofs are left out of the paper.

## How it is used

`lib/` is an OCaml port of the algorithm. The parts map as follows.

| Paper | Code |
|---|---|
| Fig. 4: `Term` | `lib/syntax.ml` |
| Fig. 6: `SimpleType`, `VariableState`, `PolymorphicType` | `lib/types.ml` (`simple_type`, `var_state`, `type_scheme`) |
| Fig. 5: user-facing `Type` | `lib/types.ml` (`typ`, `show_typ`) |
| Fig. 8: `typeTerm` | `lib/typer.ml` (`type_term`, `type_let_rhs`) |
| Fig. 9: `constrain` | `lib/typer.ml` (`constrain`) |
| Fig. 7: `extrude` | `lib/typer.ml` (`extrude`) |
| §3.5.1: `freshenAbove`, `instantiate` | `lib/typer.ml` |
| §3.3.3: `coalesceType` | `lib/coalesce.ml` |
| §4.4: `CompactType`, `compactType` | `lib/simplify.ml` (`compact`, `compact_type`) |
| §4.3.1: co-occurrence analysis, `simplifyType` | `lib/simplify.ml` (`simplify`) |
| §4.3.2: hash consing, `coalesceCompactType` | `lib/simplify.ml` (`coalesce_compact`) |
| Fig. 10, as a checker of `≤∀` (beyond the paper) | `lib/subsume.ml` |

The Lean development (`lean/`) follows the plan of §5. Like §5.2, it makes
the bounds an explicit state and the algorithm a relation, and it proves
Theorem 1 (soundness) through Lemma 2 (soundness of constraining).

## Differences in the implementation

- **Records are rows.** The paper's `Record(fields)` becomes
  `Record(fields, tail)`, with `Abs` fields and row variables, for record
  extension (see [extensible-records.md](extensible-records.md)).
- **`let rec` only binds functions.** Evaluation is eager, so the
  right-hand side of `let rec x = s` is evaluated before `x` exists; only a
  function, whose body runs later, can refer to `x` safely. `let rec x =
  succ x` and the cyclic record `let rec ones = {head = 1; tail = ones}`
  are rejected (`type_let_rhs`; `Term.IsFun` in Lean). Cyclic data built
  through constructors could come later, with a guardedness check (#4).
- **No structural recursive types by default.** Like an occurs check,
  inference rejects a type variable that reaches itself through a type
  constructor, following both upper and lower bounds (`check_acyclic`).
  Variable-only cycles such as `α ≤ β ≤ α` are fine. Recursive data is
  meant to be nominal, as in Bolt (#4). `--rectypes` restores the paper's
  equi-recursive types, and the paper's recursive examples in the tests use
  it. Following both directions is conservative:
  `fun x -> if true then x else {a = x}` is rejected, as HM rejects it,
  although its type `'a -> 'a ∨ {a: 'a}` is not recursive (#5).
- **Raw coalescing only produces contractive types.** Every recursive
  occurrence is under a function or a record field. A variable cycle with
  no constructor in between gives the neutral element of its context (`⊥`
  in a union, `⊤` in an intersection), where §3.3.3 would give an
  unguarded `μα. … ∧ α`. Under the paper's own Fig. 10, `X ≤ μα. X ∧ α`
  isn't derivable (it needs a hypothesis that is never unlocked), so such a
  type is strictly below `X`, yet the simplifier, the paper's and ours,
  drops these cycles. Emitting only contractive types removes the
  conflict.
- **Reflexive constraints are skipped.** `constrain` returns at once when
  both sides are equal; Fig. 9 doesn't. Without the check, `α <: α` records
  `α` as its own bound, which is sound but coalesces to junk such as
  `('a ∧ 'b as 'b)`.
- **§4 is re-implemented from its description.** The paper doesn't show the
  code, and there is no `canonicalizeType` pass. Variable unification is
  greedy and its rewrites don't commute: one merge can block another, so
  different orders give different (but equivalent) types. The order is
  fixed canonically: variables are visited by first appearance in the
  inferred type, never by internal id, and all negative merges run before
  positive ones. That reproduces the paper's
  `twice : ('a ∨ 'b -> 'a) -> 'b -> 'a`.
- **Small things.** `level` is recomputed on every call instead of cached
  in a `lazy val`. The constraint cache is a hash table on structural
  equality, with variables compared by identity, as Scala's case-class
  equality does. The built-ins are the reference implementation's: `true`,
  `false`, `not`, `succ`, `add` and `if : ∀α. bool → α → α → α`.

As in §4.1, simplification relies on MLsub's lattice equations: for
example, `(a -> b) ∧ (c -> d)` becomes `a ∨ c -> b ∧ d`, and a union of
records keeps only their common fields. Those merges would be unsound for
overloading, flow typing or first-class polymorphism (see
[superf.md](superf.md)).

## Differences in the formalization

| Paper (§5) | Lean (`lean/`) |
|---|---|
| Syntactic subtyping (Fig. 10) with hypotheses `Σ`, guarded by `▷`/`◁`, and `S-Rec` to unfold `μ` | Subtyping as a greatest fixed point (`Sub`) of a guarded one-layer relation (`Step`). There is no `μ`: recursive solutions are *graph variables*, named definitions without binders (`Sub.lean`). The §5.1.3 example is `paper_example`. |
| Soundness through unifying coalescing (Fig. 12) into recursive types | The solution `θ` reads each variable as the intersection of the non-variable upper bounds reachable through variable bounds (`Solution.lean`) |
| Lemma 2 with a stronger hypothesis relating `Σ` to the cache, and consistency loosened during propagation | A ghost log of accepted constraints with two invariants, justification and consistency, and *pending* pairs while a bound propagates (`Soundness.lean`) |
| Theorem 1: `⊢ t : τ` with `τ ≤∀ E⁺⟦st⟧` | `t : θ(st)` in the declarative system, over the solution (`theorem1`). Relating it to coalesced closed types needs the MLsub equations (roadmap step 5). |
| Let-polymorphism left out, justified by let-duplication (footnote 15) | Constrained schemes `∀ᾱ. D ⇒ σ` as in HM(X), proved sound for certificates of polymorphic programs (`PolyLet.lean`) |
| Completeness (Theorem 2, Lemmas 3–5) sketched | Not proved. Certificate adequacy (`TypeTerm.certificate`) is proved for the model without levels and tested on the examples for the real typer. |
| Minimal rules, MLsub equations optional | The same choice. `Lattice.lean` proves that function merging is not derivable from the minimal rules. |

The Lean development also covers what the paper does not have: rows and
row expansion, kinds for row variables, separate sorts for types, rows
and fields (`Abs` is the top field and never a type, so a present field
`pre τ` is strictly below it), and the absence of structural recursive
types (`Valid.nonrec`).
