Subsumption: `--compare T1 T2` decides T1 ≤∀ T2 and T2 ≤∀ T1.
"More general" means T1 can be used wherever T2 is expected.

Instantiation and rigid variables

  $ simplesub --compare "'a -> 'a" "int -> int"
  'a -> 'a is more general than int -> int
  $ simplesub --compare "'a -> 'a" "'b -> 'c"
  'a -> 'a is less general than 'a -> 'b
  $ simplesub --compare "int -> int" "bool -> bool"
  int -> int is incomparable to bool -> bool

Polar variables, sandwiches (Sec. 4.3.1)

  $ simplesub --compare "⊤ -> int" "'a -> int"
  ⊤ -> int is equivalent to 'a -> int
  $ simplesub --compare "'a ∧ int -> 'a ∨ int" "int -> int"
  'a ∧ int -> 'a ∨ int is equivalent to int -> int
  $ simplesub --compare "'a ∧ int -> 'a" "int -> int"
  'a ∧ int -> 'a is more general than int -> int

Unions, intersections, records

  $ simplesub --compare "int" "int ∨ bool"
  int is more general than int ∨ bool
  $ simplesub --compare "{x: int, y: int}" "{x: int}"
  {x: int, y: int} is more general than {x: int}
  $ simplesub --compare "bool -> 'a -> 'a -> 'a" "bool -> 'a -> 'b -> 'a ∨ 'b"
  bool -> 'a -> 'a -> 'a is equivalent to bool -> 'a -> 'b -> 'a ∨ 'b
  $ simplesub --compare "(int -> int) ∧ (bool -> bool) -> ⊤" "(int ∨ bool -> int ∧ bool) -> ⊤"
  (int -> int) ∧ (bool -> bool) -> ⊤ is equivalent to (int ∨ bool -> int ∧ bool) -> ⊤
  $ simplesub --compare "{x: int} ∧ {y: bool} -> ⊤" "{x: int, y: bool} -> ⊤"
  {x: int} ∧ {y: bool} -> ⊤ is equivalent to {x: int, y: bool} -> ⊤

The two simplified forms of `twice` are equivalent (see README)

  $ simplesub --compare "('a ∨ 'b -> 'a) -> 'b -> 'a" "('a -> 'a ∧ 'b) -> 'a -> 'b"
  ('a ∨ 'b -> 'a) -> 'b -> 'a is equivalent to ('a -> 'a ∧ 'b) -> 'a -> 'b
  $ simplesub --compare "('a ∨ 'b -> 'a) -> 'b -> 'a" "('a -> 'a) -> 'a -> 'a"
  ('a ∨ 'b -> 'a) -> 'b -> 'a is more general than ('a -> 'a) -> 'a -> 'a

Recursive types: unrolling preserves meaning

  $ simplesub --compare "(⊤ -> 'a as 'a)" "⊤ -> ⊤ -> (⊤ -> 'a as 'a)"
  (⊤ -> 'a as 'a) is equivalent to ⊤ -> ⊤ -> (⊤ -> 'a as 'a)
  $ simplesub --compare "({head: int, tail: 'a} as 'a) -> int" "{head: int, tail: {head: int, tail: ({head: int, tail: 'a} as 'a)}} -> int"
  ({head: int, tail: 'a} as 'a) -> int is equivalent to {head: int, tail: {head: int, tail: ({head: int, tail: 'a} as 'a)}} -> int
  $ simplesub --compare "({head: int, tail: 'a} as 'a) -> int" "{head: int} -> int"
  ({head: int, tail: 'a} as 'a) -> int is less general than {head: int} -> int
  $ simplesub --compare "(int -> 'a as 'a)" "(int -> int -> 'b as 'b)"
  (int -> 'a as 'a) is equivalent to (int -> int -> 'a as 'a)

ASCII syntax

  $ simplesub --compare "top -> int | bool" "'a -> bool | int"
  ⊤ -> int ∨ bool is equivalent to 'a -> bool ∨ int

Non-polar types are rejected

  $ simplesub --compare "int ∨ bool -> ⊤" "⊤"
  error: not a polar type: union in negative position
  [2]

`--expect` checks inferred types against the paper, modulo equivalence

  $ simplesub -e 'fun f -> fun x -> f (f x)' --expect "('a ∨ 'b -> 'b) -> 'a -> 'b"
  - : ('a ∨ 'b -> 'a) -> 'b -> 'a
  $ simplesub -e 'fun x -> 42' --expect "⊤ -> int"
  - : ⊤ -> int
  $ simplesub -e 'let rec f = fun x -> {L = x; R = f x} in f' --expect "'a -> ({L: 'a, R: 'b} as 'b)"
  - : 'a -> ({L: 'a, R: 'b} as 'b)
  $ simplesub -e 'let rec f = fun x -> f in f' --expect "(⊤ -> 'a as 'a)"
  - : (⊤ -> 'a as 'a)
  $ simplesub -e 'let rec x = (let y = x in (fun x -> y)) in x' --expect "(⊤ -> 'a as 'a)"
  - : (⊤ -> 'a as 'a)
  $ simplesub -e 'fun x -> {L = add x 1; R = if true then 0 else x}' --expect "int -> {L: int, R: int}"
  - : int -> {L: int, R: int}

A mismatch is reported with the direction of the difference

  $ simplesub -e 'fun f -> fun x -> f (f x)' --expect "('a -> 'a) -> 'a -> 'a"
  - : ('a ∨ 'b -> 'a) -> 'b -> 'a
    expected ('a -> 'a) -> 'a -> 'a, but inferred type is strictly more general
  [1]
  $ simplesub -e 'fun x -> x' --expect "⊤ -> ⊥"
  - : 'a -> 'a
    expected ⊤ -> ⊥, but inferred type is strictly less general
  [1]
