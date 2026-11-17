# MLstruct: Principal Type Inference in a Boolean Algebra of Structural Types

Lionel Parreaux and Chun Yin Chau. OOPSLA 2022, PACMPL 6, article 141.
[doi:10.1145/3563304](https://doi.org/10.1145/3563304).
Extended version with the proofs: <https://lptk.github.io/mlstruct-paper>.

**Status: a candidate for the next step of the type lattice. Not implemented.**

## What the paper does

MLstruct generalizes MLsub (and so Simple-sub) to first-class unions and
intersections, adds *negation* types so that the types form a Boolean
algebra, and keeps principal type inference:

- classes contribute *nominal tags* (`#Some`), and a class type is its tag
  intersected with a record of its fields, so the system stays structural
  with "a sprinkle of nominality";
- class-instance matching (`case x of Some → …, _ → …`) is typed with
  negations of tags, which gives extensible variants without row
  variables;
- equi-recursive types, restricted to regular trees so that subsumption
  stays decidable;
- the union of records with different fields is identified with `⊤`, to
  keep unions tractable, and `{x : ⊥}` is not below `⊥`, which would be
  unsound in their algebra;
- soundness and completeness of inference are stated, with proofs in the
  extended version.

## How it is used

Not yet. It is the reference for two items listed as not implemented:
negation (Boolean-algebra) types, and rejecting uninhabited types such as
`int ∧ bool`, which MLsub-style systems accept.

## Differences

- **Lattice.** We have the MLsub lattice (no negation). The simplifier
  already relies on MLsub's equations, for example merging intersections of
  functions; MLstruct's algebra extends those equations.
- **Records.** Our records are rows with row variables and `Abs` fields, for
  record extension ([extensible-records.md](extensible-records.md)).
  MLstruct has no row variables: it gets extensibility from classes and
  negation instead. As in MLstruct, a union of records keeps only their
  common fields.
- **Recursion and nominal types.** We reject structural recursive types and
  plan nominal enums and structs with declared or inferred variance (#4);
  MLstruct has equi-recursive structural types and classes whose variance
  arises from their structural decomposition.
- **Pattern matching.** We have none yet. MLstruct's class-instance matching
  is the obvious model if Bolt's `match` on enums is added (#4).
