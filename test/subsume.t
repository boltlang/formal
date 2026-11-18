Subsumption: `--compare T1 T2` decides T1 ≤∀ T2 and T2 ≤∀ T1.
"More general" means T1 can be used wherever T2 is expected.

Instantiation and rigid variables

  $ boltcore --compare "'a -> 'a" "int -> int"
  'a -> 'a is strictly more general than int -> int
  $ boltcore --compare "'a -> 'a" "'b -> 'c"
  'a -> 'a is strictly less general than 'a -> 'b
  $ boltcore --compare "int -> int" "bool -> bool"
  int -> int is incomparable to bool -> bool

Polar variables, sandwiches (Sec. 4.3.1)

  $ boltcore --compare "⊤ -> int" "'a -> int"
  ⊤ -> int is equivalent to 'a -> int
  $ boltcore --compare "'a ∧ int -> 'a ∨ int" "int -> int"
  'a ∧ int -> 'a ∨ int is equivalent to int -> int
  $ boltcore --compare "'a ∧ int -> 'a" "int -> int"
  'a ∧ int -> 'a is strictly more general than int -> int

Unions, intersections, records

  $ boltcore --compare "int" "int ∨ bool"
  int is strictly more general than int ∨ bool
  $ boltcore --compare "{x: int, y: int, ..}" "{x: int, ..}"
  {x: int, y: int, ..} is strictly more general than {x: int, ..}
  $ boltcore --compare "bool -> 'a -> 'a -> 'a" "bool -> 'a -> 'b -> 'a ∨ 'b"
  bool -> 'a -> 'a -> 'a is equivalent to bool -> 'a -> 'b -> 'a ∨ 'b
  $ boltcore --compare "(int -> int) ∧ (bool -> bool) -> ⊤" "(int ∨ bool -> int ∧ bool) -> ⊤"
  (int -> int) ∧ (bool -> bool) -> ⊤ is equivalent to (int ∨ bool -> int ∧ bool) -> ⊤
  $ boltcore --compare "{x: int, ..} ∧ {y: bool, ..} -> ⊤" "{x: int, y: bool, ..} -> ⊤"
  {x: int, ..} ∧ {y: bool, ..} -> ⊤ is equivalent to {x: int, y: bool, ..} -> ⊤

The two simplified forms of `twice` are equivalent (see README)

  $ boltcore --compare "('a ∨ 'b -> 'a) -> 'b -> 'a" "('a -> 'a ∧ 'b) -> 'a -> 'b"
  ('a ∨ 'b -> 'a) -> 'b -> 'a is equivalent to ('a -> 'a ∧ 'b) -> 'a -> 'b
  $ boltcore --compare "('a ∨ 'b -> 'a) -> 'b -> 'a" "('a -> 'a) -> 'a -> 'a"
  ('a ∨ 'b -> 'a) -> 'b -> 'a is strictly more general than ('a -> 'a) -> 'a -> 'a

Recursive types: unrolling preserves meaning

  $ boltcore --compare "(⊤ -> 'a as 'a)" "⊤ -> ⊤ -> (⊤ -> 'a as 'a)"
  (⊤ -> 'a as 'a) is equivalent to ⊤ -> ⊤ -> (⊤ -> 'a as 'a)
  $ boltcore --compare "({head: int, tail: 'a} as 'a) -> int" "{head: int, tail: {head: int, tail: ({head: int, tail: 'a} as 'a)}} -> int"
  ({head: int, tail: 'a} as 'a) -> int is equivalent to {head: int, tail: {head: int, tail: ({head: int, tail: 'a} as 'a)}} -> int
  $ boltcore --compare "({head: int, tail: 'a, ..} as 'a) -> int" "{head: int, ..} -> int"
  ({head: int, tail: 'a, ..} as 'a) -> int is strictly less general than {head: int, ..} -> int
  $ boltcore --compare "(int -> 'a as 'a)" "(int -> int -> 'b as 'b)"
  (int -> 'a as 'a) is equivalent to (int -> int -> 'a as 'a)

ASCII syntax

  $ boltcore --compare "top -> int | bool" "'a -> bool | int"
  ⊤ -> int ∨ bool is equivalent to 'a -> bool ∨ int

Non-polar types are rejected

  $ boltcore --compare "int ∨ bool -> ⊤" "⊤"
  error: not a polar type: union in negative position
  [2]

`--expect` checks inferred types against the paper, modulo equivalence

  $ boltcore -e 'fun f -> fun x -> f (f x)' --expect "('a ∨ 'b -> 'b) -> 'a -> 'b"
  - : ('a ∨ 'b -> 'a) -> 'b -> 'a
  $ boltcore -e 'fun x -> 42' --expect "⊤ -> int"
  - : ⊤ -> int
  $ boltcore --rectypes -e 'let rec f = fun x -> {L = x; R = f x} in f' --expect "'a -> ({L: 'a, R: 'b} as 'b)"
  - : 'a -> ({L: 'a, R: 'b} as 'b)
  $ boltcore --rectypes -e 'let rec f = fun x -> f in f' --expect "(⊤ -> 'a as 'a)"
  - : (⊤ -> 'a as 'a)
  $ boltcore --rectypes -e 'let rec x = (let y = x in (fun x -> y)) in x' --expect "(⊤ -> 'a as 'a)"
  - : type error: let rec x: the right-hand side must be a function
  [1]
  $ boltcore -e 'fun x -> {L = add x 1; R = if true then 0 else x}' --expect "int -> {L: int, R: int}"
  - : int -> {L: int, R: int}

A mismatch is reported with the direction of the difference

  $ boltcore -e 'fun f -> fun x -> f (f x)' --expect "('a -> 'a) -> 'a -> 'a"
  - : ('a ∨ 'b -> 'a) -> 'b -> 'a
    expected ('a -> 'a) -> 'a -> 'a, but inferred type is strictly more general
  [1]
  $ boltcore -e 'fun x -> x' --expect "⊤ -> ⊥"
  - : 'a -> 'a
    expected ⊤ -> ⊥, but inferred type is strictly less general
  [1]

Rows: `{fields | tail}`; inside braces `|` starts the row tail, so unions in
field types use `∨`. `Abs` is the top field ("no guarantee"). `{x: int, ..}`
is open: its tail is the top row.

  $ boltcore --compare "{y: Abs | 'a} -> {y: int | 'a}" "{x: int} -> {x: int, y: int}"
  {y: Abs | 'a} -> {y: int | 'a} is strictly more general than {x: int} -> {x: int, y: int}
Kinds are inferred from use: 'a is the tail of a row listing y, so 'a lacks
y, and `{| 'a}` (in which nothing lists y) means `{y: Abs | 'a}`.

  $ boltcore --compare "{y: Abs | 'a} -> {y: int | 'a}" "{| 'a} -> {y: int | 'a}"
  {y: Abs | 'a} -> {y: int | 'a} is equivalent to {| 'a} -> {y: int | 'a}
  $ boltcore --compare "{y: Abs | 'a} -> {y: int | 'a}" "{y: Abs | 'a} -> {| 'a}"
  {y: Abs | 'a} -> {y: int | 'a} is strictly more general than {y: Abs | 'a} -> {| 'a}
  $ boltcore --compare "{x: int | 'a}" "{x: int}"
  {x: int | 'a} is strictly more general than {x: int}
  $ boltcore --compare "{x: int, y: Abs, ..}" "{x: int, ..}"
  {x: int, y: Abs, ..} is equivalent to {x: int, ..}
  $ boltcore --compare "{x: Abs, ..}" "{..}"
  {x: Abs, ..} is equivalent to {..}
  $ boltcore --compare "{x: int, ..} -> ⊤" "{x: int | 'a} -> ⊤"
  {x: int, ..} -> ⊤ is equivalent to {x: int | 'a} -> ⊤
  $ boltcore --compare "{x: int ∨ bool}" "{x: int | 'a}"
  {x: int ∨ bool} is strictly less general than {x: int | 'a}
  $ boltcore --compare "{n: int | 'b ∧ {done: bool, ..}} -> ⊤" "{n: int, done: bool, ..} -> ⊤"
  {n: int | 'a ∧ {done: bool, ..}} -> ⊤ is equivalent to {n: int, done: bool, ..} -> ⊤

Closed and open records: `{x: int}` has no other fields

  $ boltcore --compare "{x: int, y: int}" "{x: int}"
  {x: int, y: int} is incomparable to {x: int}
  $ boltcore --compare "{x: int}" "{x: int, ..}"
  {x: int} is strictly more general than {x: int, ..}
  $ boltcore --compare "{x: int} -> ⊤" "{x: int, ..} -> ⊤"
  {x: int} -> ⊤ is strictly less general than {x: int, ..} -> ⊤
  $ boltcore --compare "{x: int | 'a} -> {| 'a}" "{x: int} -> {}"
  {x: int | 'a} -> {| 'a} is strictly more general than {x: int} -> {}
  $ boltcore --compare "{x: int, y: Missing}" "{x: int}"
  {x: int, y: Missing} is equivalent to {x: int}

`Abs` in a parameter does not ask for the field; a type variable does

  $ boltcore --compare "{x: Abs, ..} -> int" "{x: 'a, ..} -> int"
  {x: Abs, ..} -> int is strictly more general than {x: 'a, ..} -> int

Optional fields: `Pre τ ≤ Opt τ`, `Missing ≤ Opt τ`, `Opt τ ≤ Abs`

  $ boltcore --compare "{y: int}" "{y?: int}"
  {y: int} is strictly more general than {y?: int}
  $ boltcore --compare "{}" "{y?: int}"
  {} is strictly more general than {y?: int}
  $ boltcore --compare "{y?: int}" "{y?: int, ..}"
  {y?: int} is strictly more general than {y?: int, ..}
  $ boltcore --compare "{y?: int, ..}" "{..}"
  {y?: int, ..} is strictly more general than {..}
  $ boltcore --compare "{y?: int, ..} -> int" "{y: int, ..} -> int"
  {y?: int, ..} -> int is strictly more general than {y: int, ..} -> int
  $ boltcore --compare "{y?: int, ..} -> int" "{} -> int"
  {y?: int, ..} -> int is strictly more general than {} -> int
  $ boltcore --compare "{y?: int, ..} -> int" "{..} -> int"
  {y?: int, ..} -> int is strictly less general than {..} -> int
  $ boltcore --compare "{y?: int, ..} -> int" "{y: bool} -> int"
  {y?: int, ..} -> int is incomparable to {y: bool} -> int

The lattice equations of fields that simplification uses

  $ boltcore --compare "{x: int} ∨ {}" "{x?: int}"
  {x: int} ∨ {} is equivalent to {x?: int}
  $ boltcore --compare "{x: int} ∨ {y: bool}" "{x?: int, y?: bool}"
  {x: int} ∨ {y: bool} is equivalent to {x?: int, y?: bool}
  $ boltcore --compare "{x: int, ..} ∧ {x?: bool, ..} -> int" "{x: int ∧ bool, ..} -> int"
  {x: int, ..} ∧ {x?: bool, ..} -> int is equivalent to {x: int ∧ bool, ..} -> int
  $ boltcore --compare "{x?: int, ..} ∧ {x?: bool, ..} -> int" "{x?: int ∧ bool, ..} -> int"
  {x?: int, ..} ∧ {x?: bool, ..} -> int is equivalent to {x?: int ∧ bool, ..} -> int
  $ boltcore --compare "{x?: int, ..} ∧ {x: Missing, ..} -> int" "{x: Missing, ..} -> int"
  {x?: int, ..} ∧ {x: Missing, ..} -> int is equivalent to {x: Missing, ..} -> int
  $ boltcore --compare "{y: int ∧ Missing, ..} -> int" "{y: Missing, ..} -> int"
  {y: int ∧ Missing, ..} -> int is strictly less general than {y: Missing, ..} -> int
  $ boltcore --compare "{x?: ⊥}" "{}"
  {x?: ⊥} is equivalent to {}

The meaning of unguarded recursion (from raw coalescing of variable cycles)
is the neutral element of its context

  $ boltcore --compare "('g ∧ int as 'g) -> ⊤" "int -> ⊤"
  ('a ∧ int as 'a) -> ⊤ is equivalent to int -> ⊤
  $ boltcore --compare "⊤ -> ('g ∨ int as 'g)" "⊤ -> int"
  ⊤ -> ('a ∨ int as 'a) is equivalent to ⊤ -> int

`--expect` on rows, against Marques et al.'s type for record extension

  $ boltcore -e 'fun r -> r with {y = 1}' --expect "{y: Abs | 'r} -> {y: int | 'r}"
  - : {y: Abs | 'a} -> {y: int | 'a}
  $ boltcore -e '(fun r -> r with {y = 1}) {x = 1}' --expect "{x: int, y: int}"
  - : {x: int, y: int}
  $ boltcore -e 'fun r -> r with {y = 1}' --expect "{| 'r} -> {y: int | 'r}"
  - : {y: Abs | 'a} -> {y: int | 'a}
  $ boltcore --compare "{x: int | 'a} -> {y: int | 'a}" "{x: int, y: Abs | 'a} -> {y: int | 'a}"
  {x: int | 'a} -> {y: int | 'a} is equivalent to {x: int, y: Abs | 'a} -> {y: int | 'a}
  $ boltcore -e 'fun r -> r with {y = 1}' --expect "{x: int} -> {x: int, y: int}"
  - : {y: Abs | 'a} -> {y: int | 'a}
    expected {x: int} -> {x: int, y: int}, but inferred type is strictly more general
  [1]
