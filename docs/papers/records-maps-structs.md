# Typing Records, Maps, and Structs

Giuseppe Castagna. ICFP 2023, PACMPL 7, article 196.
[doi:10.1145/3607838](https://doi.org/10.1145/3607838). Open access.

**Status: the comparison point for optional record fields (issue #2). Not
implemented.**

## What the paper does

A single record type for both *structs* (known labels, different value
types, a missing label is an error) and *maps* (computed keys, one value
type, a missing key gives a default), for dynamically typed languages such
as Elixir and Erlang:

- types are set-theoretic, with union, intersection and negation, and
  subtyping is semantic (Frisch, Castagna and Benzaken's *semantic
  subtyping*);
- a record type is a function from labels to `τ ∨ ⊥`, where `⊥` means "the
  field is undefined": a *mandatory* field `ℓ = t` maps `ℓ` to `t`, an
  *optional* field `ℓ ⇒ t` to `t ∨ ⊥`; the other labels map to `⊥` in a
  *closed* record and to `1 ∨ ⊥` (any value, or undefined) in an *open*
  one; map types give a type to a whole set of keys;
- selection `e.ℓ` requires `e : {ℓ = 1}`, i.e. a defined field; there are
  also concatenation `e₁ + e₂` (the right fields win) and deletion `e\ℓ`;
- subtyping is decided through a decomposition of record atoms; there is
  no type inference (functions are annotated) and no polymorphism.

## How it is used

As a reference for the field lattice. Its readings line up with ours:

| Castagna | This repository |
|---|---|
| `ℓ = t`, mandatory | a present field `t` (`Pre t`); in Lean, a type below `⊤` |
| `1`, any value | `⊤` |
| `1 ∨ ⊥`, any value or undefined | `Abs`, strictly above `⊤` |
| open record `{…}` (other labels `1 ∨ ⊥`) | a record with tail `Abs`, our only kind of record literal |
| `e.ℓ` requires `{ℓ = 1}` | `t.l` requires a present field (`Typ.sel`, `τ ≤ ⊤`) |
| `e₁ + e₂` | `r with {…}`, with a literal on the right |
| `ℓ ⇒ t`, optional | proposed `Opt t` (#2) |
| `⊥`, undefined; closed records | proposed `Absent` field and tail (#2) |

## Differences

- **Inference.** We infer principal types with polymorphism and row
  variables; the paper has neither type inference nor polymorphism, and
  names combining semantic subtyping with row polymorphism as an open
  challenge.
- **Lattice.** Ours is MLsub's, without negation, and our only records are
  open: there are no closed records, optional fields or known-absent
  fields yet (#2).
- **Maps.** There are no map types, computed keys or deletion.
- **Unions of records.** Semantic subtyping keeps unions of records
  precise; our simplifier keeps only the common fields, by MLsub's
  equations (see [mlstruct.md](mlstruct.md) for the same choice in
  MLstruct).
