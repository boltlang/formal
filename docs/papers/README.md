# Papers

One note per paper the project builds on or plans around: what the paper
does, how it is used here, and where we differ. The PDFs are in
[`papers/`](../../papers/).

| Paper | Status | Note |
|---|---|---|
| Parreaux, *The Simple Essence of Algebraic Subtyping* (ICFP 2020) | implemented: inference, coalescing, simplification; the plan of the Lean proofs | [simple-sub.md](simple-sub.md) |
| Marques, Florido, Vasconcelos, *Towards Algebraic Subtyping for Extensible Records* (2024) | implemented: rows and `with` | [extensible-records.md](extensible-records.md) |
| Brachthäuser, Schuster, Ostermann, *Effects as Capabilities* / *Effekt* (OOPSLA 2020) | planned: the design for effects | [effekt.md](effekt.md) |
| Parreaux, Chau, *MLstruct* (OOPSLA 2022) | future: negation and Boolean-algebra types | [mlstruct.md](mlstruct.md) |
| Parreaux, Boruch-Gruszecki, Fan, Chau, *When Subtyping Constraints Liberate* (SuperF, POPL 2024) | discussion: first-class polymorphism (#6) | [superf.md](superf.md) |
| Castagna, *Typing Records, Maps, and Structs* (ICFP 2023) | comparison: optional fields (#2) | [records-maps-structs.md](records-maps-structs.md) |

Also in `papers/`, not used yet: Frisch, Castagna and Benzaken, *Semantic
Subtyping: Dealing Set-Theoretically with Function, Union, Intersection,
and Negation Types* (JACM 2008), the foundation of Castagna's records
paper.

Cited without a local copy:

- Dolan and Mycroft, *Polymorphism, Subtyping, and Type Inference in MLsub*
  (POPL 2017): the type lattice and its equations, which the simplifier
  and subsumption rely on (`lean/BoltCore/Lattice.lean`).
- Odersky, Sulzmann and Wehr, *Type Inference with Constrained Types*
  (HM(X), TAPOS 1999): constrained schemes `∀ᾱ. D ⇒ σ` and their reading
  through instances, used by the declarative system
  (`lean/BoltCore/Typing.lean`).
- Rémy, *Type Inference for Records in a Natural Extension of ML* (1993):
  `Pre`/`Abs` fields and kinds for row variables.
