# Design note: sorted types (types, rows, fields)

Status: done (steps 1–3 and 3b); the Lean development is sorted throughout. Next: #2, optional fields.

## The problem

The Lean development has one syntax of types, `Ty`, in which `Abs` (the top
field, and the top row in tail position) is a type like any other, and
fields are types. Much of the development exists only to keep `Abs` from
behaving like a type:

| Patch | Where |
|---|---|
| `Abs` strictly above `⊤`: `Step.top` needs `Ty.IsType`; `not_abs_le_top` | `Sub.lean` |
| `Abs` never a function parameter or result (`NAC`), preserved by the algorithm | `Sorts.lean` |
| `≠ .abs` premises in the skeleton rules; `FieldR`'s side conditions | `Certificate.lean`, `PolyLet.lean`, `Soundness.lean` |
| Selection needs `τ ≤ ⊤`; `SType.Present` | `Typing.lean`, `Certificate.lean` |
| Variables that stand for types are below `⊤` (`TyVar`, the `⊤` definition in `defsOf`) | `Solution.lean` |
| Schemes add `α ≤ ⊤` per type variable; `HoldsUnder.top`, `GenHyp.top` | `PolyLet.lean`, `SolutionGen.lean`, `Certificate.lean` |
| Constraints hold "as types" only when the left side is not `Abs`, and field by field always (`Holds`, `SatAfter`, `Cstr.typeLevel`) | `Typing.lean`, `SolutionGen.lean` |
| A primitive or function type, viewed as a row, has `Abs` fields | `Ty.field`, `Types.lean` |

It also admits junk: `Step.abs` puts every type below `Abs`, so `⊢ 1 : Abs`
and `fun x -> x : Abs → Abs` are derivable. That is harmless (nothing can
use a value of type `Abs`) but should not typecheck.

`../extrecords`, a Lean model of Marques et al., avoids all of this by
*sorting* the syntax, as Rémy and the paper do: types, rows and fields are
separate, `Abs` is a field or a row and never a type, and the only field
rules are `Pre τ ≤ Abs` and `Pre τ₁ ≤ Pre τ₂`. Its subtyping relation is not
one we can reuse (it is inductive with `refl` and `trans` as rules, and has
no recursion or graph variables), but its sorting is.

## The proposal

### Syntax: one family indexed by sort

```lean
inductive Srt | ty | row | field

inductive T : Srt → Type where
  -- the lattice, at every sort
  | top   : T s          -- ⊤ at ty; Abs at field; the top row at row
  | bot   : T s
  | union : T s → T s → T s
  | inter : T s → T s → T s
  | fvar  : Nat → T s   -- free (rigid) variables, sorted
  | gvar  : Nat → T s   -- graph variables, sorted
  -- types
  | prim  : String → T .ty
  | arrow : T .ty → T .ty → T .ty
  | rcd   : T .row → T .ty
  -- rows
  | cons  : String → T .field → T .row → T .row
  -- fields
  | pre   : T .ty → T .field
  | proj  : String → T .row → T .field   -- field l of an opaque row
```

`Abs` is `top` at sort `field` (and at sort `row`). Then `Pre τ ≤ Abs` is
just the `top` rule, and `Abs ≤ Pre τ` fails because no rule derives it, so
`Pre ⊤ < Abs` holds by the shape of the syntax. That is the
"`Abs` strictly above `⊤`" decision, with nothing left to state.

The lattice operations are generic, so there is no special case for the
union or intersection of rows or fields. The field of a row is computed as
now, per sort:

```
field l (cons l' θ ρ) = if l = l' then θ else field l ρ
field l top = top        field l bot = bot
field l (ρ₁ ∪ ρ₂) = field l ρ₁ ∪ field l ρ₂    (and ∩)
field l ρ = proj l ρ     for a variable ρ
```

There is no case for primitive or function types: `rcd` only takes rows.

### Subtyping

`Step E R : T s → T s → Prop`, with `R` a relation at every sort:

- generic rules at every sort: `top`, `bot`, `union`/`inter` on both sides,
  `fvar`, `gvar`, and `defL`/`defR` for graph variables;
- types: `prim`; `arrow` with `R` on the components (guarded, `◁`);
  `rcd ρ₁ ≤ rcd ρ₂` when `R ρ₁ ρ₂` (guarded);
- rows: `ρ₁ ≤ ρ₂` when `Step (field l ρ₁) (field l ρ₂)` for every label
  (one layer, unguarded);
- fields: `pre τ₁ ≤ pre τ₂` when `Step τ₁ τ₂`; `proj l t ≤ proj l t`, and
  `projDefL`/`projDefR` for fields of graph row variables, as now.

The guards stay where they are now: under a function type and under a
record. Comparing rows becomes an ordinary judgment at sort `row`, which
removes the field-by-field obligations: a scheme constraint between rows
is just `Sub` at sort `row`, so `Holds`, `SatAfter`'s second component and
`Cstr.typeLevel` disappear.

Cut elimination (`Sub.trans`) keeps its structure: induction on the two
finite derivations, now with the `pre` and row cases.

### Typing

- `t.l : τ` when `t : rcd (cons l (pre τ) top)`; there is no `τ ≤ ⊤`
  premise.
- `t with {fs} : rcd (fs ++ ρ)` when `t : rcd (fs ↦ Abs ++ ρ)`, as now.
- Scheme variables are sorted, and instances substitute by sort, so a type
  variable is never instantiated with `Abs`: `mkScheme`'s `α ≤ ⊤`
  constraints go.
- No field variables. extrecords' T-Ext quantifies over the old field
  `θ`; with subsumption, `θ = Abs` is equivalent (its own `f_type_lossy`
  does this), and the OCaml typer already works that way.

### The algorithm and certificates stay unsorted

The algorithm model's `SType` and the OCaml `simple_type` keep one syntax,
with `Record (fields, tail)` for both records and rows. What changes:

- **The solution translates by position** (as built in step 2): `sTy`,
  `sRow` and `sField` map a simple type to a type, a row and a field
  (`sField abs = ⊤`, `sField τ = pre (sTy τ)`, `sRow (var v) = gvar v`, …).
  They are total; `Abs` in a type position gives junk, which `NAC` rules
  out where it matters. Every graph variable is defined at every sort, from
  its upper bounds translated at that sort, so variables need no sort and
  `TyVar` and the `⊤` definition go. (This note first proposed a sort per
  variable and a well-sortedness invariant replacing `NAC`; neither turned
  out to be needed.)

Keeping `SType` unsorted avoids dependent pairs in logs, caches and
certificates, and keeps the model close to the OCaml code. A fully indexed
`SType` is possible but not needed: sorts matter for what the solution
means, not for how the algorithm runs.

## What it removes and what it costs

Removed: everything in the first table, and the junk typings. Issue #2
becomes a field lattice: `Missing ≤ Opt τ ≤ Abs`, `Pre τ ≤ Opt τ`, with
`missing` as a field constructor and `nil` as a closed-row tail, instead of
more special cases in `Ty` (done: `Types.lean`, `Sub.lean`).

Costs:

- **Proofs.** It touches nearly everything: `Sub` and cut elimination,
  `Rows.lean`, `Typing.lean`, the solution theorem, kinds, certificates,
  generalization and the checker. Most proofs keep their structure, with
  more cases. My estimate: several sessions.
- **Lean mechanics.** Matching on an indexed family needs care (the sort is
  a dependent index), and `DecidableEq` must be derived for it for the
  checker.
- **`Pre` and the lattice.** `pre τ₁ ∪ pre τ₂ ≡ pre (τ₁ ∪ τ₂)` and its dual
  are lattice equations, not minimal rules. They belong with the MLsub
  equations (roadmap step 5), which the simplifier's row merges need anyway.

## Plan

Each step ends with `lake build`, `dune test` and `scripts/check-certs.sh`
passing. Steps 1–3 were built in `lean/BoltCore/Sorted/`, alongside the
unsorted files; step 3b moved them into place, so the file names below are
those of the time:

1. **Sorted declarative core.** Done, in `lean/BoltCore/Sorted/`, alongside
   the unsorted files: `Types`, `Sub` (with cut elimination), `Lattice` and
   `Typing`, with the typing examples and `not_typ_sel_missing`. `Rows.lean`
   is abstract over field values and needs no change. Lean notes: `field`
   is defined at every sort (`⊤` outside rows) and matches on the sort
   first, which keeps its recursion structural, so it reduces by `rfl`.
   Cut elimination goes through a *pending cut* predicate (`Pend`), so that
   one induction on the right derivation covers every shape without casts
   between sorts; rows are cut field by field.
2. **Sorted solution.** Done (`Sorted/Solution.lean`, `Sorted/Theorem1.lean`):
   the sorted solution theorem (`ssolution_ty`, `ssolution_row`) and
   Theorem 1 over sorted typing with no assumption left (`stheorem1`). Two
   findings change the plan:
   - **Variables need no sort.** A simple type is translated by the
     position it occurs in (`sTy`, `sRow`, `sField`), and every graph
     variable is defined at every sort from its upper bounds. The
     unsorted proof's type-level pairs and field pairs become pairs at the
     type and row sorts; `TyVar` and the `⊤` definition are gone.
   - **`NAC` stays as it is.** It is the fragment of well-sortedness the
     proof needs (no `Abs` in function types, so their translations at the
     type sort mean something), and `Sorts.lean` is reused unchanged, as
     are the algorithm model, justification, consistency and kinds.
3. **Certificates.** Done: `Sorted/SolutionGen.lean`, `Sorted/PolyLet.lean`
   and `Sorted/Certificate.lean`, and the executable checker
   (`Check.lean`) now proves sorted typings (`check_sound` through
   `SPTyp.sound_top`). An interpretation gives each variable a type and a
   row; generalization asks for the bounds at both sorts, which replaces
   the field-by-field obligations, and there is no `α ≤ ⊤` constraint and no
   kind condition on instantiation. The checker asks that a selected field
   and a record literal's fields are not `Abs`, instead of `Present`.
   Adequacy goes straight to the polymorphic skeleton
   (`TypeTerm.scertificate`): a monomorphic `let` generalizes no variables.
   Still unsorted: the hand-written skeletons in `Examples.lean` (their
   `decide` checks already go through the sorted checker).
3b. **Retire the unsorted declarative development.** Done: the sorted files
   replaced `Types`, `Sub`, `Lattice` and `Typing`; the files that mixed
   algorithm-level lemmas with the unsorted solution (`Solution`,
   `SolutionRows`, `Theorem1`, `Kinds`, `Certificate`, `SolutionGen`,
   `PolyLet`) keep the former and hold the sorted proofs; adequacy is
   `Adequacy.lean`; the `Sorted` prefix is gone. The monomorphic skeleton
   `CTyp` is gone too: its role is played by `PTyp` with lets that
   generalize no variables.
4. **OCaml.** Probably unnecessary: since variables need no sort (step 2),
   neither the typer nor certificates need to record one.
5. **Then #2**, optional fields, on the sorted field lattice.

## Open questions

- Should the bottom field be the generic `bot`, or `pre bot`? The generic
  `bot` is the only choice below `missing`.
- Should the row rule compare fields with `Step` (one layer, as proposed) or
  with `R`? `Step` keeps the guard at the record, as now.
- Can certificates stay free of sorts by inferring them from kinds and from
  occurrence as tails, instead of listing them?
