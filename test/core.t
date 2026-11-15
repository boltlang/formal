Types inferred by Simple-sub, simplified as in Section 4 of the paper.
The final section shows the raw coalesced types (`--raw`) for comparison.

Basics

  $ simplesub -e '42'
  - : int
  $ simplesub -e 'fun x -> 42'
  - : ⊤ -> int
  $ simplesub -e 'fun x -> x'
  - : 'a -> 'a
  $ simplesub -e 'fun x -> x 42'
  - : (int -> 'a) -> 'a
  $ simplesub -e '(fun x -> x) 42'
  - : int
  $ simplesub -e 'fun f -> fun x -> f (f x)'
  - : ('a ∨ 'b -> 'a) -> 'b -> 'a
  $ simplesub -e 'let twice = fun f -> fun x -> f (f x) in twice'
  - : ('a ∨ 'b -> 'a) -> 'b -> 'a

Records (width/depth subtyping)

  $ simplesub -e 'fun x -> x.f'
  - : {f: 'a} -> 'a
  $ simplesub -e '{a = 1; b = true}.a'
  - : int
  $ simplesub -e 'fun x -> {L = succ x.v; R = x}'
  - : 'a ∧ {v: int} -> {L: int, R: 'a}
  $ simplesub -e '(fun r -> r.a) {a = 1; b = 2}'
  - : int

if-then-else via the `if` combinator; joins of incompatible types are allowed
when they are never eliminated

  $ simplesub -e 'fun x -> if x then 1 else 2'
  - : bool -> int
  $ simplesub --rectypes -e 'fun x -> if true then x else {a = x}'
  - : 'a -> 'a ∨ {a: 'a}

Let polymorphism (levels, freshenAbove)

  $ simplesub -e 'let id = fun x -> x in {a = id 1; b = id true}'
  - : {a: int, b: bool}
  $ simplesub -e 'fun y -> let f = fun x -> {v = x; w = y} in f'
  - : 'a -> 'b -> {v: 'b, w: 'a}

Extrusion: a lambda-bound variable flowing into a let-bound definition

  $ simplesub -e 'fun x -> let y = fun z -> x z in y'
  - : ('a -> 'b) -> 'a -> 'b
  $ simplesub -e 'fun k -> let f = fun x -> k x in {a = f 1; b = f true}'
  - : (bool ∨ int -> 'a) -> {a: 'a, b: 'a}

Recursive types are rejected by default, as by an occurs check: no type
variable may reach itself through a type constructor (following upper and
lower bounds). Recursive data is meant to be nominal. Variable-only cycles
are fine. Like HM, this also rejects joining a value with a structure
containing it, although subtyping could type that without recursion.

  $ simplesub -e 'let rec f = fun x -> f in f'
  - : type error: recursive type: α2 reaches itself through a type constructor (via bound (α3 -> α2))
  [1]
  $ simplesub -e 'fun x -> x x'
  - : type error: recursive type: α2 reaches itself through a type constructor (via bound (α2 -> α3))
  [1]
  $ simplesub -e 'let rec len = fun l -> if l.isNil then 0 else succ (len l.tail) in len'
  - : type error: recursive type: α11 reaches itself through a type constructor (via bound α3)
  [1]
  $ simplesub -e 'fun x -> if true then x else {a = x}'
  - : type error: recursive type: α6 reaches itself through a type constructor (via bound {a: α2})
  [1]
  $ simplesub -e 'let rec loop = fun x -> loop x in loop'
  - : ⊤ -> ⊥
  $ simplesub -e 'fun f -> fun x -> if true then f x else x'
  - : ('a -> 'b) -> 'a ∧ 'b -> 'b

Recursion and recursive types (Sec. 3.4.1, 4.3.2), with `--rectypes`

  $ simplesub --rectypes -e 'let rec f = fun x -> f in f'
  - : (⊤ -> 'a as 'a)
  $ simplesub --rectypes -e 'let rec f = fun x -> {L = x; R = f x} in f'
  - : 'a -> ({L: 'a, R: 'b} as 'b)
  $ simplesub --rectypes -e 'let rec x = (let y = x in (fun x -> y)) in x'
  - : (⊤ -> 'a as 'a)
  $ simplesub --rectypes -e 'let rec produce = fun arg -> {head = arg; tail = produce (succ arg)} in produce'
  - : int -> ({head: int, tail: 'a} as 'a)
  $ simplesub --rectypes -e 'let rec consume = fun strm -> add strm.head (consume strm.tail) in consume'
  - : ({head: int, tail: 'a} as 'a) -> int

Self-application and the Y combinator

  $ simplesub --rectypes -e 'fun x -> x x'
  - : 'a ∧ ('a -> 'b) -> 'b
  $ simplesub --rectypes -e 'let y = fun f -> (fun x -> f (x x)) (fun x -> f (x x)) in y (fun f -> fun x -> f)'
  - : (⊤ -> 'a as 'a)

Top-level declarations are generalized and can be reused. A failing
declaration is reported and skipped. `use` is rightly rejected: there is no
flow typing, so `length` demands a `tail` field even on the `isNil = true` node
(its input type is `μb. {tail: b, isNil: bool}`; only a cyclic record fits).

  $ cat > prog.sub <<'SRC'
  > // a small program
  > let id x = x
  > let rec length l = if l.isNil then 0 else succ (length l.tail)
  > let rec nils = {isNil = true; tail = nils}
  > let ok = {a = id 1; b = id {c = true}; n = length nils}
  > let use = length {isNil = false; tail = {isNil = true}}
  > SRC
  $ simplesub --rectypes prog.sub
  let id : 'a -> 'a
  let length : ({isNil: bool, tail: 'a} as 'a) -> int
  let nils : ({isNil: bool, tail: 'a} as 'a)
  let ok : {a: int, b: {c: bool}, n: int}
  let use : type error: missing field: tail in {isNil: bool}
  [1]

Type errors

  $ simplesub -e '1 2'
  - : type error: cannot constrain int <: (int -> α2)
  [1]
  $ simplesub -e 'succ true'
  - : type error: cannot constrain bool <: int
  [1]
  $ simplesub -e '{a = 1}.b'
  - : type error: missing field: b in {a: int}
  [1]
  $ simplesub -e 'fun x -> succ (not x)'
  - : type error: cannot constrain bool <: int
  [1]
  $ simplesub -e 'unbound'
  - : type error: identifier not found: unbound
  [1]
  $ simplesub -e 'let f = fun x -> x.a in f {b = 1}'
  - : type error: missing field: a in {b: int}
  [1]
  $ simplesub --rectypes -e 'let rec f = fun x -> f x.a in f {a = {a = 1}}'
  - : type error: cannot constrain int <: {a: α9}
  [1]

Parse errors

  $ simplesub -e 'fun -> 1'
  parse error: 1:5: expected parameter (at '->')
  [2]

Raw (coalesced but unsimplified) output, Sec. 3.3, versus simplified output

  $ simplesub --raw -e 'fun f -> fun x -> f (f x)'
  - : 'a ∧ ('b -> 'c) ∧ ('d -> 'b) -> 'd -> 'c
  $ simplesub -e 'fun f -> fun x -> f (f x)'
  - : ('a ∨ 'b -> 'a) -> 'b -> 'a
  $ simplesub --rectypes --raw -e 'let rec f = fun x -> {L = x; R = f x} in f'
  - : 'a ∨ ('b -> {L: 'b, R: ('d ∨ {L: 'b, R: 'c} as 'c)})
  $ simplesub --rectypes -e 'let rec f = fun x -> {L = x; R = f x} in f'
  - : 'a -> ({L: 'a, R: 'b} as 'b)
  $ simplesub --raw -e 'fun x -> {L = add x 1; R = if true then 0 else x}'
  - : 'a ∧ 'b ∧ 'c ∧ int -> {L: 'd ∨ int, R: 'c ∨ int}
  $ simplesub -e 'fun x -> {L = add x 1; R = if true then 0 else x}'
  - : int -> {L: int, R: int}

More cases from the paper (Secs. 2-4)

  $ simplesub --rectypes -e 'fun x -> x x x'
  - : 'a ∧ ('a -> 'a -> 'b) -> 'b
  $ simplesub --rectypes -e '(fun x -> x x) (fun x -> x x)'
  - : ⊥
  $ simplesub --rectypes -e 'fun x -> {l = x x; r = x}'
  - : 'a ∧ ('a -> 'b) -> {l: 'b, r: 'a}
  $ simplesub --rectypes -e 'fun f -> (fun x -> f (x x)) (fun x -> f (x x))'
  - : ('a -> 'a) -> 'a
  $ simplesub --rectypes -e 'let rec f = fun x -> f x.u in f'
  - : ({u: 'a} as 'a) -> ⊥
  $ simplesub -e 'fun x -> fun y -> fun z -> if x then y else z'
  - : bool -> 'a -> 'a -> 'a
  $ simplesub -e 'if true then {a = 1; b = true} else {b = false; c = 42}'
  - : {b: bool}

Extensible records (rows, after Marques et al. 2024)

  $ simplesub -e 'fun r -> r with {y = 1}'
  - : {y: Abs | 'a} -> {y: int | 'a}
  $ simplesub -e '((fun r -> r with {y = 2}) {x = 1}).x'
  - : int
  $ simplesub -e '{x = 1} with {x = true}'
  - : {x: bool}
  $ simplesub -e 'fun r -> (r with {y = 1}).x'
  - : {x: 'a} -> 'a
  $ simplesub --self-check -e 'fun r -> r with {a = r.a; b = 2}'
  - : {a: 'a, b: Abs | 'b} -> {a: 'a, b: int | 'b}
  $ simplesub --raw -e 'fun r -> r with {a = r.a; b = 2}'
  - : 'a ∧ {a: Abs, b: Abs | 'b} ∧ {a: 'c} -> {a: 'c, b: int | 'b}
  $ simplesub -e 'let rec f r = f (r with {n = succ r.n}) in f'
  - : {n: int} -> ⊥
  $ simplesub -e 'fun r -> fun s -> if true then r with {y = 1} else s with {z = 2}'
  - : {y: Abs | 'a} -> {z: Abs | 'b} -> {y: int | 'a} ∨ {z: int | 'b}
  $ simplesub -e '({x = 1} with {y = 2}).z'
  - : type error: missing field: z in {x: int}
  [1]
  $ simplesub -e 'fun r -> r with {y}'
  parse error: 1:19: expected '=' (at '}')
  [2]

Raw output is contractive: a variable cycle without a constructor in between
becomes the neutral element (here ⊤ in an intersection) instead of an
unguarded recursive type like `('g ∧ 'h as 'g)`

  $ simplesub --raw -e 'let rec count r = if r.done then r else count (r with {n = succ r.n}) in count'
  - : 'a ∨ ('b ∧ {n: Abs | 'c ∧ {done: 'd ∧ bool | 'e}} ∧ {n: 'f ∧ int} ∧ 'g ∧ 'h ∧ 'i ∧ ⊤ ∧ {done: 'd ∧ bool} -> 'h ∨ {n: 'j ∨ int | 'c})

Kinds: the row variable of `r with {y = …}` lacks y; `r with {}` is just r

  $ simplesub -e 'fun r -> r with {}'
  - : 'a -> 'a
  $ simplesub --self-check -e 'fun r -> (r with {a = 1}) with {b = 2}'
  - : {a: Abs, b: Abs | 'a} -> {a: int, b: int | 'a}
  $ simplesub --self-check -e 'fun r -> (r with {a = 1}) with {a = true}'
  - : {a: Abs | 'a} -> {a: bool | 'a}
  $ simplesub --self-check -e 'fun r -> (fun s -> s with {z = 3}) (r with {x = 1})'
  - : {x: Abs, z: Abs | 'a} -> {x: int, z: int | 'a}
