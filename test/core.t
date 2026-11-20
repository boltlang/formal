Types inferred by Simple-sub, simplified as in Section 4 of the paper.
The final section shows the raw coalesced types (`--raw`) for comparison.

Basics

  $ boltcore -e '42'
  - : int
  $ boltcore -e 'fn (x) -> 42'
  - : (x: ⊤) -> int
  $ boltcore -e 'fn (x) -> x'
  - : (x: 'a) -> 'a
  $ boltcore -e 'fn (x) -> x(42)'
  - : (x: {*: [int]} -> 'a) -> 'a
  $ boltcore -e '(fn (x) -> x)(42)'
  - : int
  $ boltcore -e 'fn (f) -> fn (x) -> f(f(x))'
  - : (f: {*: ['a ∨ 'b]} -> 'a) -> (x: 'b) -> 'a
  $ boltcore -e 'let twice(f) = fn (x) -> f(f(x)) in twice'
  - : (f: {*: ['a ∨ 'b]} -> 'a) -> (x: 'b) -> 'a

Records (width/depth subtyping)

  $ boltcore -e 'fn (x) -> x.f'
  - : (x: {f: 'a, ..}) -> 'a
  $ boltcore -e '{a = 1; b = true}.a'
  - : int
  $ boltcore -e 'fn (x) -> {L = succ(x.v); R = x}'
  - : (x: 'a ∧ {v: int, ..}) -> {L: int, R: 'a}
  $ boltcore -e '(fn (r) -> r.a)({a = 1; b = 2})'
  - : int

if-then-else via the `if` combinator; joins of incompatible types are allowed
when they are never eliminated

  $ boltcore -e 'fn (x) -> if x then 1 else 2'
  - : (x: bool) -> int
  $ boltcore --rectypes -e 'fn (x) -> if true then x else {a = x}'
  - : (x: 'a) -> 'a ∨ {a: 'a}

Let polymorphism (levels, freshenAbove)

  $ boltcore -e 'let id(x) = x in {a = id(1); b = id(true)}'
  - : {a: int, b: bool}
  $ boltcore -e 'fn (y) -> let f(x) = {v = x; w = y} in f'
  - : (y: 'a) -> (x: 'b) -> {v: 'b, w: 'a}

Extrusion: a lambda-bound variable flowing into a let-bound definition

  $ boltcore -e 'fn (x) -> let y(z) = x(z) in y'
  - : (x: {*: ['a]} -> 'b) -> (z: 'a) -> 'b
  $ boltcore -e 'fn (k) -> let f(x) = k(x) in {a = f(1); b = f(true)}'
  - : (k: {*: [bool ∨ int]} -> 'a) -> {a: 'a, b: 'a}

Recursive types are rejected by default, as by an occurs check: no type
variable may reach itself through a type constructor (following upper and
lower bounds). Recursive data is meant to be nominal. Variable-only cycles
are fine. Like HM, this also rejects joining a value with a structure
containing it, although subtyping could type that without recursion.

  $ boltcore -e 'let rec f(x) = f in f'
  - : type error: recursive type: α1 reaches itself through a type constructor (via bound ((x: α2) -> α1))
  [1]
  $ boltcore -e 'fn (x) -> x(x)'
  - : type error: recursive type: α1 reaches itself through a type constructor (via bound ({*: [α1]} -> α2))
  [1]
  $ boltcore -e 'let rec len(l) = if l.isNil then 0 else succ(len(l.tail)) in len'
  - : type error: recursive type: α7 reaches itself through a type constructor (via bound α2)
  [1]
  $ boltcore -e 'fn (x) -> if true then x else {a = x}'
  - : type error: recursive type: α2 reaches itself through a type constructor (via bound {a: α1})
  [1]
  $ boltcore -e 'let rec loop(x) = loop(x) in loop'
  - : (x: ⊤) -> ⊥
  $ boltcore -e 'fn (f) -> fn (x) -> if true then f(x) else x'
  - : (f: {*: ['a]} -> 'b) -> (x: 'a ∧ 'b) -> 'b

`let rec` only binds functions: evaluation is eager, so any other
right-hand side would be evaluated before the name it defines exists.

  $ boltcore -e 'let rec x = succ(x) in x'
  - : type error: let rec x: the right-hand side must be a function
  [1]
  $ boltcore -e 'let rec f(x) = f(succ(x)) in f'
  - : (x: int) -> ⊥
  $ boltcore -e 'let f(x) = let rec g(y) = g(x) in g in f'
  - : (x: ⊤) -> (y: ⊤) -> ⊥

Recursion and recursive types (Sec. 3.4.1, 4.3.2), with `--rectypes`

  $ boltcore --rectypes -e 'let rec f(x) = f in f'
  - : ((x: ⊤) -> 'a as 'a)
  $ boltcore --rectypes -e 'let rec f(x) = {L = x; R = f(x)} in f'
  - : (x: 'a) -> ({L: 'a, R: 'b} as 'b)
  $ boltcore --rectypes -e 'let rec x = let y = x in fn (x) -> y in x'
  - : type error: let rec x: the right-hand side must be a function
  [1]
  $ boltcore --rectypes -e 'let rec produce(arg) = {head = arg; tail = produce(succ(arg))} in produce'
  - : (arg: int) -> ({head: int, tail: 'a} as 'a)
  $ boltcore --rectypes -e 'let rec consume(strm) = add(strm.head, consume(strm.tail)) in consume'
  - : (strm: ({head: int, tail: 'a, ..} as 'a)) -> int

Self-application and the Y combinator

  $ boltcore --rectypes -e 'fn (x) -> x(x)'
  - : (x: 'a ∧ ({*: ['a]} -> 'b)) -> 'b
  $ boltcore --rectypes -e 'let y(f) = (fn (x) -> f(x(x)))(fn (x) -> f(x(x))) in y(fn (f) -> fn (x) -> f)'
  - : ((x: ⊤) -> 'a as 'a)

Top-level declarations are generalized and can be reused. A failing
declaration is reported and skipped. `use` is rightly rejected: there is no
flow typing, so `length` demands a `tail` field even on the `isNil = true` node
(its input type is `μb. {tail: b, isNil: bool}`; only a cyclic record fits,
and `let rec` cannot build one, since it only binds functions).

  $ cat > prog.sub <<'SRC'
  > // a small program
  > let id(x) = x
  > let rec length(l) = if l.isNil then 0 else succ(length(l.tail))
  > let rec nils = {isNil = true; tail = nils}
  > let ok = {a = id(1); b = id({c = true}); n = length(nils)}
  > let use = length({isNil = false; tail = {isNil = true}})
  > SRC
  $ boltcore --rectypes prog.sub
  let id : (x: 'a) -> 'a
  let length : (l: ({isNil: bool, tail: 'a, ..} as 'a)) -> int
  let nils : type error: let rec nils: the right-hand side must be a function
  let ok : type error: identifier not found: nils
  let use : type error: missing field: tail in {isNil: bool}
  [1]

Type errors

  $ boltcore -e '1(2)'
  - : type error: cannot constrain int <: ({*: [int]} -> α1)
  [1]
  $ boltcore -e 'succ(true)'
  - : type error: cannot constrain bool <: int
  [1]
  $ boltcore -e '{a = 1}.b'
  - : type error: missing field: b in {a: int}
  [1]
  $ boltcore -e 'fn (x) -> succ(not(x))'
  - : type error: cannot constrain bool <: int
  [1]
  $ boltcore -e 'unbound'
  - : type error: identifier not found: unbound
  [1]
  $ boltcore -e 'let f(x) = x.a in f({b = 1})'
  - : type error: missing field: a in {b: int}
  [1]
  $ boltcore --rectypes -e 'let rec f(x) = f(x.a) in f({a = {a = 1}})'
  - : type error: cannot constrain int <: {a: α8, ..}
  [1]

Parse errors

  $ boltcore -e 'fn -> 1'
  parse error: 1:4: expected '(' (at '->')
  [2]
  $ boltcore -e 'fn (x, x) -> 1'
  parse error: 1:11: parameter x is given twice (at '->')
  [2]
  $ boltcore -e 'fn (x = 1, y) -> 1'
  parse error: 1:15: parameter y has no default but follows one that has (at '->')
  [2]
  $ boltcore -e 'fn (/, x) -> 1'
  parse error: 1:11: '/' must follow a parameter (at '->')
  [2]
  $ boltcore -e 'fn (x, *, /, y) -> 1'
  parse error: 1:17: '/' must come before '*', and only once (at '->')
  [2]
  $ boltcore -e 'fn (x, *) -> 1'
  parse error: 1:11: '*' must be followed by a parameter (at '->')
  [2]
  $ boltcore -e 'fn (x, /, /) -> 1'
  parse error: 1:14: '/' must come before '*', and only once (at '->')
  [2]
  $ boltcore -e 'succ(x = 1, 2)'
  parse error: 1:15: a positional argument follows a named one (at 'end of input')
  [2]
  $ boltcore -e 'succ(x = 1, x = 2)'
  parse error: 1:19: argument x is given twice (at 'end of input')
  [2]
  $ boltcore -e 'fun x -> x'
  parse error: 1:5: expected 'let' or end of input (a call needs parentheses: f(x)) (at 'x')
  [2]
  $ boltcore -e 'succ 1'
  parse error: 1:6: expected 'let' or end of input (a call needs parentheses: f(x)) (at '1')
  [2]
  $ boltcore -e 'let a = succ x'
  parse error: 1:14: expected 'let' or end of input (a call needs parentheses: f(x)) (at 'x')
  [2]

Keyword-only parameters may have defaults in any order

  $ boltcore -e 'fn (x, *, y = 1, z) -> 1'
  - : (x: ⊤, *, y?: ⊤, z: ⊤) -> int

Raw (coalesced but unsimplified) output, Sec. 3.3, versus simplified output

  $ boltcore --raw -e 'fn (f) -> fn (x) -> f(f(x))'
  - : (f: 'a ∧ ({*: ['b]} -> 'c) ∧ ({*: ['d]} -> 'b)) -> (x: 'd) -> 'c
  $ boltcore -e 'fn (f) -> fn (x) -> f(f(x))'
  - : (f: {*: ['a ∨ 'b]} -> 'a) -> (x: 'b) -> 'a
  $ boltcore --rectypes --raw -e 'let rec f(x) = {L = x; R = f(x)} in f'
  - : 'a ∨ ((x: 'b) -> {L: 'b, R: ('d ∨ {L: 'b, R: 'c} as 'c)})
  $ boltcore --rectypes -e 'let rec f(x) = {L = x; R = f(x)} in f'
  - : (x: 'a) -> ({L: 'a, R: 'b} as 'b)
  $ boltcore --raw -e 'fn (x) -> {L = add(x, 1); R = if true then 0 else x}'
  - : (x: 'a ∧ 'b ∧ int) -> {L: 'c ∨ int, R: 'b ∨ int}
  $ boltcore -e 'fn (x) -> {L = add(x, 1); R = if true then 0 else x}'
  - : (x: int) -> {L: int, R: int}

More cases from the paper (Secs. 2-4)

  $ boltcore --rectypes -e 'fn (x) -> x(x)(x)'
  - : (x: 'a ∧ ({*: ['a]} -> {*: ['a]} -> 'b)) -> 'b
  $ boltcore --rectypes -e '(fn (x) -> x(x))(fn (x) -> x(x))'
  - : ⊥
  $ boltcore --rectypes -e 'fn (x) -> {l = x(x); r = x}'
  - : (x: 'a ∧ ({*: ['a]} -> 'b)) -> {l: 'b, r: 'a}
  $ boltcore --rectypes -e 'fn (f) -> (fn (x) -> f(x(x)))(fn (x) -> f(x(x)))'
  - : (f: {*: ['a]} -> 'a) -> 'a
  $ boltcore --rectypes -e 'let rec f(x) = f(x.u) in f'
  - : (x: ({u: 'a, ..} as 'a)) -> ⊥
  $ boltcore -e 'fn (x) -> fn (y) -> fn (z) -> if x then y else z'
  - : (x: bool) -> (y: 'a) -> (z: 'a) -> 'a
  $ boltcore -e 'if true then {a = 1; b = true} else {b = false; c = 42}'
  - : {a?: int, b: bool, c?: int}

Extensible records (rows, after Marques et al. 2024)

  $ boltcore -e 'fn (r) -> r with {y = 1}'
  - : (r: {y: Abs | 'a}) -> {y: int | 'a}
  $ boltcore -e '(fn (r) -> r with {y = 2})({x = 1}).x'
  - : int
  $ boltcore -e '{x = 1} with {x = true}'
  - : {x: bool}
  $ boltcore -e 'fn (r) -> r with {y = 1}.x'
  - : (r: {x: 'a, ..}) -> 'a
  $ boltcore --self-check -e 'fn (r) -> r with {a = r.a; b = 2}'
  - : (r: {a: 'a, b: Abs | 'b}) -> {a: 'a, b: int | 'b}
  $ boltcore --raw -e 'fn (r) -> r with {a = r.a; b = 2}'
  - : (r: 'a ∧ {a: Abs, b: Abs | 'b} ∧ {a: 'c, ..}) -> {a: 'c, b: int | 'b}
  $ boltcore -e 'let rec f(r) = f(r with {n = succ(r.n)}) in f'
  - : (r: {n: int, ..}) -> ⊥
  $ boltcore -e 'fn (r) -> fn (s) -> if true then r with {y = 1} else s with {z = 2}'
  - : (r: {y: Abs | 'a}) -> (s: {z: Abs | 'b}) -> {z: int | 'b} ∨ {y: int | 'a}
  $ boltcore -e '{x = 1} with {y = 2}.z'
  - : type error: missing field: z in {x: int}
  [1]
  $ boltcore -e 'fn (r) -> r with {y}'
  parse error: 1:20: expected '=' (at '}')
  [2]

Closed records: a record literal has exactly its fields. `{x: int, ..}` is
open (any other fields), which is what selection asks for. A closed record
can be used where an open one is expected.

  $ boltcore -e '{a = 1; b = true}'
  - : {a: int, b: bool}
  $ boltcore -e 'fn (r) -> r.a'
  - : (r: {a: 'a, ..}) -> 'a
  $ boltcore -e '(fn (r) -> r.a)({a = 1; b = true})'
  - : int
  $ boltcore -e 'fn (f) -> f({x = 1})'
  - : (f: {*: [{x: int}]} -> 'a) -> 'a
  $ boltcore -e '{}'
  - : {}

Optional fields: `r.l ?? d` is the field if it is present, and `d` otherwise.
`l?: τ` is a field that is missing, or present at `τ`

  $ boltcore -e 'fn (r) -> r.y ?? 0'
  - : (r: {y?: 'a, ..}) -> 'a ∨ int
  $ boltcore -e '(fn (r) -> r.y ?? 0)({x = 1})'
  - : int
  $ boltcore -e '(fn (r) -> r.y ?? 0)({y = true})'
  - : bool ∨ int
  $ boltcore -e 'fn (r) -> add(r.x ?? 1, r.y ?? r.x ?? 2)'
  - : (r: {x?: int, y?: int, ..}) -> int
  $ boltcore -e 'fn (r) -> (r.a ?? {}).b ?? 0'
  - : (r: {a?: {b?: 'a, ..}, ..}) -> 'a ∨ int
  $ boltcore -e 'fn (x) -> x.a ?? x'
  - : (x: 'a ∧ {a?: 'a, ..}) -> 'a

A field given in one branch only is optional; plain selection then fails

  $ boltcore -e 'fn (b) -> if b then {y = 1} else {}'
  - : (b: bool) -> {y?: int}
  $ boltcore -e 'fn (b) -> (if b then {y = 1} else {}).y ?? 0'
  - : (b: bool) -> int
  $ boltcore -e 'fn (b) -> (if b then {y = 1} else {}).y'
  - : type error: missing field: y in {}
  [1]
  $ boltcore -e 'fn (b) -> if b then {x = 1} else {y = 2}'
  - : (b: bool) -> {x?: int, y?: int}

A field read both ways is required: `Opt τ ∧ Pre σ = Pre (τ ∧ σ)`

  $ boltcore --self-check -e 'fn (r) -> {a = r.y ?? 0; b = r.y}'
  - : (r: {y: 'a, ..}) -> {a: 'a ∨ int, b: 'a}
  $ boltcore --raw -e 'fn (r) -> {a = r.y ?? 0; b = r.y}'
  - : (r: 'a ∧ {y: 'b, ..} ∧ {y?: 'c, ..}) -> {a: 'c ∨ int, b: 'b}

With let-polymorphism, extrusion and rows

  $ boltcore --self-check -e 'let f(r) = r.y ?? 0 in {a = f({}); b = f({y = 3}); c = f({z = true})}'
  - : {a: int, b: int, c: int}
  $ boltcore --self-check -e 'fn (r) -> let f(d) = r.y ?? d in {a = f(1); b = f(true)}'
  - : (r: {y?: 'a, ..}) -> {a: 'a ∨ int, b: 'a ∨ bool}
  $ boltcore --self-check -e 'fn (r) -> r with {y = 1}.y ?? 2'
  - : (r: {..}) -> int
  $ boltcore --self-check -e 'fn (b) -> fn (r) -> if b then r with {x = 1} else {}'
  - : (b: bool) -> (r: {x: Abs | 'a}) -> {} ∨ {x: int | 'a}
  $ boltcore --self-check -e 'let rec f(r) = f(r with {n = r.n ?? 0}) in f'
  - : (r: {n?: ⊤, ..}) -> ⊥

`??` binds weaker than calls and selections, and its left operand is a
selection

  $ boltcore -e 'fn (r) -> succ(r.n) ?? 0'
  parse error: 1:21: the left operand of '??' must be a field selection (at '??')
  [2]
  $ boltcore -e 'fn (r) -> succ(r.n ?? 0)'
  - : (r: {n?: int, ..}) -> int

A label is set at most once in a `with`:

  $ boltcore -e '{a = 0} with {a = 1; a = true}'
  parse error: 1:31: label 'a' set twice in 'with' (at 'end of input')
  [2]

Raw output is contractive: a variable cycle without a constructor in between
becomes the neutral element (here ⊤ in an intersection) instead of an
unguarded recursive type like `('g ∧ 'h as 'g)`

  $ boltcore --raw -e 'let rec count(r) = if r.done then r else count(r with {n = succ(r.n)}) in count'
  - : 'a ∨ ((r: 'b ∧ {n: Abs | 'c ∧ {done: 'd ∧ bool | 'e}} ∧ {n: 'f ∧ int, ..} ∧ 'g ∧ 'h ∧ ⊤ ∧ {done: 'd ∧ bool, ..}) -> 'g ∨ {n: 'i ∨ int | 'c})

Kinds: the row variable of `r with {y = …}` lacks y; `r with {}` is just r

  $ boltcore -e 'fn (r) -> r with {}'
  - : (r: 'a) -> 'a
  $ boltcore --self-check -e 'fn (r) -> r with {a = 1} with {b = 2}'
  - : (r: {a: Abs, b: Abs | 'a}) -> {a: int, b: int | 'a}
  $ boltcore --self-check -e 'fn (r) -> r with {a = 1} with {a = true}'
  - : (r: {a: Abs | 'a}) -> {a: bool | 'a}
  $ boltcore --self-check -e 'fn (r) -> (fn (s) -> s with {z = 3})(r with {x = 1})'
  - : (r: {x: Abs, z: Abs | 'a}) -> {x: int, z: int | 'a}
