# Effekt: Lightweight Effect Polymorphism for Handlers

Jonathan Immanuel Brachthäuser, Philipp Schuster and Klaus Ostermann.
*Effects as Capabilities: Effect Handlers and Lightweight Effect
Polymorphism.* OOPSLA 2020, PACMPL 4, article 126,
[doi:10.1145/3428194](https://doi.org/10.1145/3428194). Local copy, the
extended technical report *Effekt: Lightweight Effect Polymorphism for
Handlers*: [`papers/brachthaeuser20effekt.pdf`](../../papers/brachthaeuser20effekt.pdf).

**Status: the intended design for effects. Nothing is implemented yet.**

## What the paper does

- **The contextual reading of effects.** A type `α → β / ε` says that the
  function needs its *calling context* to handle `ε`, not that it has the
  side effects `ε`. An empty `ε` means "contextually pure": the function
  may still have effects, but they are handled where it was defined.
- **Effects as capabilities.** Programs translate to System Ξ in explicit
  capability-passing style: a handler binds a capability, and an effect
  operation calls the capability in scope. Handlers are lexically scoped,
  so an effect can never be handled by the wrong handler by accident, and
  effect parametricity holds.
- **No parametric effect polymorphism.** There are no effect variables;
  polymorphism over effects arises from the calling context. Effect types
  are sets, not rows.
- **Second-class blocks.** Functions that take or use capabilities are
  *blocks*: they can be passed as arguments but not returned or stored, so
  a block cannot escape the handler whose capability it closes over. The
  paper shows how a first-class `leak` block would fail at run time.
- Soundness of System Ξ and of the translation is mechanized; the language
  is implemented and compiles to JavaScript.

## How it is used

Bolt's effects are meant to follow this design rather than Koka-style
effect rows with dynamic handler search: effects are requirements on the
caller, handlers bind capabilities lexically, and there are no effect
variables in types.

## Differences and open problems

- **First-class functions.** Simple-sub, and so this core, has first-class
  functions everywhere, which is exactly what Effekt gives up for blocks.
  Before effects are added, the core needs a way to stop a function that
  closes over a capability from escaping its handler: second-class blocks
  as in Effekt, or capture sets that track which capabilities a value
  holds. This is the main open design question; it should not be left as a
  footnote.
- **Inference.** Effekt infers the return types and effects of functions.
  How effect sets would fit into this core's subtype inference, as a
  component of function types or as capability parameters in the bound
  graph, is open.
- **Rank-2 types.** Capability-passing code often wants arguments that are
  polymorphic in the capability they receive; issue #6 discusses
  first-class polymorphism ([superf.md](superf.md)).
