Unsimplified (coalesced-only) types inferred by the core Simple-sub algorithm.
Section 4 simplification is not implemented yet, so expect redundant
variables (e.g. `'a -> int` instead of `⊤ -> int`).

Basics

  $ simplesub -e '42'
  - : int
  $ simplesub -e 'fun x -> 42'
  - : 'a -> int
  $ simplesub -e 'fun x -> x'
  - : 'a -> 'a
  $ simplesub -e 'fun x -> x 42'
  - : 'a ∧ (int -> 'b) -> 'b
  $ simplesub -e '(fun x -> x) 42'
  - : 'a ∨ int
  $ simplesub -e 'fun f -> fun x -> f (f x)'
  - : 'a ∧ ('b -> 'c) ∧ ('d -> 'b) -> 'd -> 'c
  $ simplesub -e 'let twice = fun f -> fun x -> f (f x) in twice'
  - : 'a ∧ ('b -> 'c) ∧ ('d -> 'b) -> 'd -> 'c

Records (width/depth subtyping)

  $ simplesub -e 'fun x -> x.f'
  - : 'a ∧ {f: 'b} -> 'b
  $ simplesub -e '{a = 1; b = true}.a'
  - : 'a ∨ int
  $ simplesub -e 'fun x -> {L = succ x.v; R = x}'
  - : 'a ∧ {v: 'b ∧ int} -> {L: 'c ∨ int, R: 'a}
  $ simplesub -e '(fun r -> r.a) {a = 1; b = 2}'
  - : 'a ∨ int

if-then-else via the `if` combinator; joins of incompatible types are allowed
when they are never eliminated

  $ simplesub -e 'fun x -> if x then 1 else 2'
  - : 'a ∧ bool -> 'b ∨ int
  $ simplesub -e 'fun x -> if true then x else {a = x}'
  - : 'a ∧ 'b ∧ 'c -> 'c ∨ {a: 'a}

Let polymorphism (levels, freshenAbove)

  $ simplesub -e 'let id = fun x -> x in {a = id 1; b = id true}'
  - : {a: 'a ∨ int, b: 'b ∨ bool}
  $ simplesub -e 'fun y -> let f = fun x -> {v = x; w = y} in f'
  - : 'a -> 'b -> {v: 'b, w: 'a}

Extrusion: a lambda-bound variable flowing into a let-bound definition

  $ simplesub -e 'fun x -> let y = fun z -> x z in y'
  - : 'a ∧ ('b -> 'c) -> 'd ∧ 'b -> 'e ∨ 'c
  $ simplesub -e 'fun k -> let f = fun x -> k x in {a = f 1; b = f true}'
  - : 'a ∧ ('b ∨ bool ∨ int -> 'c ∧ 'd ∧ 'e) -> {a: 'e, b: 'd}

Recursion and recursive types (Sec. 3.4.1, 4.3.2)

  $ simplesub -e 'let rec f = fun x -> f in f'
  - : ('b ∨ ('c -> 'a) as 'a)
  $ simplesub -e 'let rec f = fun x -> {L = x; R = f x} in f'
  - : 'a ∨ ('b -> {L: 'b, R: ('d ∨ {L: 'b, R: 'c} as 'c)})
  $ simplesub -e 'let rec x = (let y = x in (fun x -> y)) in x'
  - : ('b ∨ ('c -> 'a) as 'a)
  $ simplesub -e 'let rec produce = fun arg -> {head = arg; tail = produce (succ arg)} in produce'
  - : 'a ∨ ('b ∧ int -> {head: 'b ∨ int, tail: ('d ∨ {head: 'b ∨ int, tail: 'c} as 'c)})
  $ simplesub -e 'let rec consume = fun strm -> add strm.head (consume strm.tail) in consume'
  - : 'a ∨ (('c ∧ {tail: 'd ∧ 'b} ∧ {head: 'e ∧ int} as 'b) -> 'f ∨ int)

Self-application and the Y combinator

  $ simplesub -e 'fun x -> x x'
  - : 'a ∧ ('a -> 'b) -> 'b
  $ simplesub -e 'let y = fun f -> (fun x -> f (x x)) (fun x -> f (x x)) in y (fun f -> fun x -> f)'
  - : 'a ∨ ('b -> ('d ∨ ('b -> 'c) as 'c))

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
  $ simplesub prog.sub
  let id : 'a -> 'a
  let length : 'a ∨ (('c ∧ {tail: 'd ∧ 'b} ∧ {isNil: 'e ∧ bool} as 'b) -> 'f ∨ int)
  let nils : ('b ∨ {isNil: bool, tail: 'a} as 'a)
  let ok : {a: 'a ∨ int, b: 'b ∨ {c: bool}, n: 'c ∨ int}
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
  $ simplesub -e 'let rec f = fun x -> f x.a in f {a = {a = 1}}'
  - : type error: cannot constrain int <: {a: α9}
  [1]

Parse errors

  $ simplesub -e 'fun -> 1'
  parse error: 1:5: expected parameter (at '->')
  [2]
