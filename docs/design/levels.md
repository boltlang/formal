# Levels in the Lean model

Status: done. The model has levels, extrusion, generalization and
instantiation, and `TypeTerm.certificate` and `theorem1` are proved for it
(`lean/BoltCore/Adequacy.lean`). This note is the plan as it was carried
out; "Order of work" says what each step became.

## Goal

The Lean model of the typer (`lean/BoltCore/Algorithm.lean`) has no levels:
its `let` is monomorphic. The real typer generalizes with levels, extrudes
and instantiates, and its runs are only checked one by one, through
certificates. The goal is to prove once, for a model with levels:

> every accepted run yields a valid certificate and a typing skeleton with
> let-polymorphism (`TypeTerm.certificate`),

so that Theorem 1 with let-polymorphism follows from `PTyp.sound_top`.
Today that statement is proved for the model without levels and tested for
the real typer.

## What the checker had to learn first (done)

Two programs the typer accepts were rejected by the checker, so adequacy
could not hold. Both are fixed in `GStep`, proved sound in
`SolutionRows.lean` and decided in `Check.lean`.

- `GStep.viaVar`: `v ≤ w` between variables, through a variable `m` that
  is an upper bound of `v` and a lower bound of `w`. Extruding a variable
  `u` with a variable lower bound `v` of a level that is also too high
  copies both: `m` is the copy of `v`, `w` the copy of `u`, and consistency
  at `u` asks for `v ≤ w`. It takes three levels.
- `GStep.record` compares the first field of each label on both sides. An
  extruded copy of a record with a repeated label is related to the
  original position by position, which is not what `constrain` checks
  (every field of the right side against the first of the left).

## The model

One model, not two: levels are added to the existing relations, and the
model without levels is the case where every level is 0 (no rule for
extrusion ever applies).

- `State.level : Nat → Nat`, fixed for a run like `State.kind`: the rules
  that allocate a variable require it to have the right level.
- `Extrude s c pol lvl t t' s' c'`, with `ExtrudeFields`, `ExtrudeParams`
  and `ExtrudeEach` (the bounds of a copied variable). `c` is the table of
  copies, per polarity. A type of level at most `lvl` is returned as it is.
  A variable gets a fresh copy at level `lvl` of the same kind: for a
  positive occurrence the copy becomes an upper bound of the original and
  gets the extruded lower bounds, and dually. There is no rule for a bare
  `Opt`: `constrain` never reaches one (it is only a field).
- Ghost log of an extrusion: the pair of each extruded type and its
  original (`note` in `lib/typer.ml`); for a signature what `note_sig`
  records; each new bound as a constraint; and for a copy `w` of `v`, each
  lower bound of `v` below `w` (dually, `w` below each upper bound). The
  last two are what `lib/cert.ml` completes the log with.
- `Constrain`: `varL` and `varR` get the guards of the OCaml code
  (`level rhs ≤ level lv`, `level lhs ≤ level rv`); two new rules extrude
  the other side and constrain against the copy. A constraint between two
  variables never reaches them: one of the guards holds.
- `Expand.fresh`: the expansion variable has the level of the row variable.
- Contexts hold schemes: `mono st` or `poly lim gen st`, where `gen` is
  ghost (the generalized variables, as `created_above` computes them).
- `TypeTerm Γ lvl s t st s'`. `let` types its right-hand side at `lvl + 1`
  and binds `poly lvl gen st`, with `gen` the variables allocated in
  between whose level is above `lvl`.
- A use of a `poly` name allocates a copy of every variable of `gen`, with
  the renamed bounds (as `complete_copies` does while recording; without
  recording the typer copies only the reachable ones, and the rest are
  unreachable). Ghost log: every logged constraint, renamed.

## Invariants, in the order they are needed

1. **Scope**: every variable in a bound, the context, the expansion table
   and the types in play is below `s.next`, and variables from `s.next` on
   have no bounds. Consistency already needs it: a fresh copy has no upper
   bounds.
2. **Levels**: a bound of `v` has level at most `level v`; an expansion
   variable has the level of its row variable; at level `lvl` the context
   and the inferred type have level at most `lvl` (for `poly lim gen st`:
   `lim ≤ lvl`, and the variables of the scheme outside `gen` have level at
   most `lim`).
3. **Locality**, for any set of variables `P` that contains every variable
   from `s.next` on, the variables of the context, and is closed under
   bounds (`PClosed P s`): a run keeps `P` closed, infers a type in `P`,
   logs only constraints in `P` and leaves the bounds of variables outside
   `P` as they are. No levels are involved; they only provide instances:
   `P = {v ≥ s.next} ∪ {level v ≤ lvl}` is closed by 1 and 2.
4. The invariants of the proofs so far, extended to the new rules:
   `CacheInLog`, `Justified`, `Consistent`, `BoundsInLog`, `LogNAC`,
   `KInv`. `LbNonVar` goes: with levels a variable can be a lower bound (it
   was not used outside `Solution.lean`). `Constrain.installs` becomes: the
   bound installed is the constraint's right side or its extrusion.

## The skeleton

`GenOK` and `InstOK` speak of the final certificate `c`, but a derivation
only knows its own run. As `TypeTerm.skeleton` already takes "what this run
logs is in `c`", it takes one more hypothesis about the rest of the run:

    Rest P s' := PClosed P c ∧ ∀ v, ¬ P v → c.bounds v = s'.bounds v

for `P = {v ≥ s'.next} ∪ {level v ≤ lvl}`: after this run nothing touches a
variable above the current level. Locality gives it to each sub-run from
the run after it (same level), and to a right-hand side from the body.

- `GenOK.avoid` (a bound of a variable outside `gen` does not mention
  `gen`): if `v` is in `P`, by `Rest`. Otherwise its bounds are those at
  `s'`; if `v` is older than the right-hand side they are those before it
  (locality), which are in scope there; if `v` is newer than it, locality
  of the body.
- `InstOK`: the bounds of a generalized variable `α` in `c` are those when
  it was generalized (`Rest` and locality of the body), so by monotonicity
  they are those at each use, where the copy got their renaming.
- `Justified` for the renamed constraints of an instantiation is proved
  about `c` as well (`GStep` is stable under a renaming that fixes what the
  bounds of other variables mention): it needs `GenOK.avoid`, which is not
  known of an intermediate state.

`Theorem1.lean` proves Theorem 1 directly on a run, which cannot go through
a generalizing `let`. Its statement becomes `theorem1_cert`: through the
certificate, so with classical logic (`PTyp.sound_top` uses it).

## Order of work

1. Done: the two justification rules.
2. Done: extrusion and `Constrain`.
   - `State.level`, `Extrude` (`Algorithm.lean`); what extrusion leaves
     alone (`Extrusion.lean`); locality and scope (`Locality.lean`:
     `Extrude.local`, `Constrain.local`, `Scope`); every pair an extrusion
     logs is justified, consistency, bounds in the log
     (`ExtrusionSound.lean`); `Extrude.nac` (`Sorts.lean`), `Extrude.kinds`
     (`Kinds.lean`). `Soundness.lean` was split: its definitions are in
     `Justify.lean`.
   - `varL` and `varR` have the level guards (`varR` also takes a variable
     of lower level on the left). Extrusion is two rules per side
     (`extLHit`/`extLNew`, `extRHit`/`extRNew`), not a recursive call:
     after extruding, either the constraint against the copy is cached, or
     the copy is installed and propagated (`go lhs rhs'` can only do that:
     the copy is not a variable, not `Abs`, and low enough by
     `Extrude.level_le`). This avoids a window in which the cached original
     has no installed bound.
   - `CacheInLog` is a structure: a cached `v ≤ b` with `b` not a variable
     has `Installed` a bound (`b` if low enough; for a record over a low
     row variable, a record with the same tail and fields below, which is
     what `ExpandG.var` asks for); a cached `a ≤ v` with `a` low enough has
     installed `a`; expansion variables have the level of their row
     variable (`ExpLevel`).
   - Consistency needs scope (a fresh copy has no bounds), so
     `Constrain.consist`, `ConstrainTop.sound` and `TypeTerm.inv` take a
     state and types in scope; `TypeTerm.inv` also proves scope.
   - `LbNonVar` is gone; `Inv₂` is `BoundsInLog`.
3. Done: `TypeTerm` with levels.
   - `Rename.lean` (`GStep.rename`), `Levels.lean` (`LevelInv`),
     `Instantiate.lean` (`State.instantiate` and its invariants).
   - `TypeTerm Γ lvl s t st s'` with `CEntry.mono`/`.poly gen st` in the
     context, `genVars` for what a `let` generalizes, `IsInst` for the
     renaming of a use.
   - `TypeWf.lean`: `TypeTerm.local` (for any set that contains every
     variable allocated from now on), `Frame`, `TypeTerm.frame`,
     `TypeTerm.wf` (scope, `LevelInv`, consistency). The context invariant
     is `CtxWF L lvl s Γ`: an entry is in scope, and outside what it
     generalizes it only mentions variables of level at most `lvl`.
   - `Adequacy.lean`: `Fin F L lvl s` is the `Rest` above; `Frozen F s gen`
     is what `GenOK` and `InstOK` need of a scheme; `JustLoc F s` is
     justification over the bounds of `F` and the log so far. The log has
     to be the log *so far*: the renaming of a step is a step only if the
     renamed premises are accepted, and an instantiation only renames what
     is logged when it happens.
4. Done: the direct proof in `Theorem1.lean` is gone (the file is
   `Final.lean`), `theorem1` is in `Adequacy.lean`, and it uses classical
   logic. README updated.

What is not covered: the model copies every generalized variable at a use,
as the typer does while recording a certificate; without recording the
typer copies only those reachable from the type. That the two infer the
same types is not proved.

## Found on the way, not part of this

A record literal with a repeated label is typed by its first field
(`{l = 1; l = true}.l : int`) and printed by its last
(`{l = 1; l = true} : {l: bool}`). The `with` form rejects a repeated label
in the parser; a record literal does not.
