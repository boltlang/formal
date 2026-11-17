# Towards Algebraic Subtyping for Extensible Records

Rodrigo Marques, Mário Florido and Pedro Vasconcelos. *Towards Algebraic
Subtyping for Extensible Records.* Extended abstract, 2024.
[arXiv:2407.06747](https://arxiv.org/abs/2407.06747).
Local copy: [`papers/towards-algebraic-subtyping-for-extensible-records.pdf`](../../papers/towards-algebraic-subtyping-for-extensible-records.pdf).

**Status: the basis of record extension (`with`) and of rows.**

## What the paper does

It extends Simple-sub ([simple-sub.md](simple-sub.md)) with record
extension `t with {l = t}`, after Rémy and Pottier:

- record types become rows `{l : θ, …; ρ}` whose tail `ρ` is `Abs` or a row
  variable, and whose fields `θ` are `Pre τ`, `Abs` or a type variable;
- `Pre τ ≤ Abs` (S-Ignore) and `Pre τ₁ ≤ Pre τ₂` when `τ₁ ≤ τ₂` (S-Pre);
  rows are equal up to field order and to unfolding `Abs` (`{…; Abs} ≡ {…,
  l : Abs; Abs}`);
- `t₁ with {l = t₂}` has type `{l : Pre τ; ρ}` when `t₁ : {l : α; ρ}`, and
  `t.l : τ` needs `t : {l : Pre τ; ρ}`;
- constraint solving *expands* a row variable when a label is missing:
  `{x : τ, ρ} ≤ {ρ'}` creates `ρ' ⟶ x : α, ρ''` with `τ ≤ α` and `ρ ≤ ρ''`.

It is work in progress: there are no proofs, and no treatment of
simplification. A prototype is at
[RodrigoMarques16/simple-sub-records](https://github.com/RodrigoMarques16/simple-sub-records);
we did not use its code.

## How it is used

`lib/typer.ml` represents rows as `Record (fields, tail)`, with fields `Abs`
or a type (`Pre τ` is just `τ`), as in the paper. `r with {l = e}`
constrains `r ≤ {l: Abs | ρ}` and has type `{l: τ | ρ}`. The paper's
example `(λr. r with {y = 2}) {x = 1}` is in `test/core.t`, `--expect`
checks its type in `test/subsume.t`, and the Lean declarative system types
it (`typ_ext`).

## Differences

- **`Abs` means "no guarantee", not "absent".** The paper reads `Abs` as "the
  field is not present" and a closed row as "all other fields are absent",
  but S-Ignore (`Pre τ ≤ Abs`) makes `Abs` the *top* field, and we follow
  the rule: a record with an `Abs` field may have the field or not. Plain
  records `{x: τ}` are rows with tail `Abs`, so width subtyping is
  unchanged. In Lean, types, rows and fields are separate sorts, as in the
  paper's grammar: `Abs` is the top field and never a type, a present field
  `pre τ` is below it and nothing derives the converse, so `{} ≤ {x : ⊤}`
  fails (`not_abs_le_pre`). There is no "known
  absent" field yet; issue #2 proposes one.
- **No field variables.** The paper's `with` rule takes `t₁ : {l : α; ρ}`
  for a fresh field variable `α`. Since `Abs` is the top field, we constrain
  against `{l: Abs | ρ}` directly and fields are never variables.
- **Expansion through constraints, not substitution.** For `{fs₀ | ρ} ≤
  {fs₁ | t₁}` where `fs₁` has labels `L` that `fs₀` lacks, we constrain `ρ
  ≤ {L-fields | ρ'}`, then `{fs₀ ∖ fs₁ | ρ'} ≤ t₁`. The expansion variable
  `ρ'` is memoized per `(ρ, L)`, so recursive types still give finitely
  many constraints. The paper rewrites `ρ'` itself (`ρ' ⟶ x : α, ρ''`).
- **Kinds** (after Rémy). A row variable's kind is the set of labels it does
  not represent, because the record it is the tail of lists them. A label
  in the kind projects to `Abs`, so it is never expanded, and the expansion
  variable gets the strictly larger kind `kind ρ ∪ L`. `r with {L = …}`
  creates a row variable of kind `L`. `constrain` checks that both sides of
  every installed bound have the same kind. The paper has no kinds. In
  Lean, kinds are what makes chains of row tails acyclic, which the
  soundness proof needs (`Kinds.lean`).
- **Simplification of rows.** Compact types keep a list of rows, and two
  rows merge only when every label missing from one is known there (its
  tail is `Abs`). Otherwise the field types live inside a row variable and
  merging would change the type. The Lean proof is `merge_exact`, and
  `merge_inexact` shows the condition is needed.
- **Subsumption on rows.** `lib/subsume.ml` decides `≤∀` for row types, so
  `--self-check`, `--expect` and `--compare` cover them. It infers the kinds
  of variables in written types from their use as tails, so
  `{| 'a} -> {y: int | 'a}` (where `'a` lacks `y`) is equivalent to
  `{y: Abs | 'a} -> {y: int | 'a}`. For the paper's extension example we
  infer `{y: Abs | 'a} -> {y: int | 'a}`, its `{y : β, ρ} → {y : int, ρ}`
  with the field variable `β`, which only occurs negatively, read as the
  top field `Abs`.
- **Proofs.** The paper conjectures soundness and completeness. We prove
  soundness of inference with rows, row expansion and kinds included
  (`theorem1`), and the exactness of the row rewrites in the simplifier and
  in subsumption (`Rows.lean`). Completeness is not proved.
- **Repeated labels.** A label set twice in one `with` is a parse error.
- **No structural recursive types** by default, where the paper keeps
  Simple-sub's `μ` (see [simple-sub.md](simple-sub.md)).
