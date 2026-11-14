Snapshots of every program in examples/. --self-check also verifies that each
simplified type is equivalent to the raw coalesced one.

  $ simplesub --self-check ../examples/basics.sub
  let const : 'a -> ⊤ -> 'a
  let id : 'a -> 'a
  let apply : ('a -> 'b) -> 'a -> 'b
  let compose : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  let twice : ('a ∨ 'b -> 'a) -> 'b -> 'a
  let flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  let inc : int -> int
  let plus2 : int -> int
  let negate_twice : bool -> bool
  $ simplesub --self-check ../examples/errors.sub
  let not_a_function : type error: cannot constrain int <: (int -> α2)
  let wrong_arg : type error: cannot constrain bool <: int
  let missing_field : type error: missing field: b in {a: int}
  let bad_record_arg : type error: missing field: a in {b: int}
  let conflict : bool ∧ int -> int
  let call_conflict : type error: cannot constrain bool <: int
  let length : ({isNil: bool, tail: 'a} as 'a) -> int
  let finite : type error: missing field: tail in {isNil: bool}
  let fine : int
  [1]
  $ simplesub --self-check ../examples/polymorphism.sub
  let id : 'a -> 'a
  let pair : {a: int, b: bool}
  let local : {b: {v: bool}, i: {v: int}}
  let extruded : (bool ∨ int -> 'a) -> {a: 'a, b: 'a}
  let mono : (bool ∨ int -> 'a) -> {a: 'a, b: 'a}
  $ simplesub --self-check ../examples/records.sub
  let get_x : {x: 'a} -> 'a
  let norm1 : {x: int, y: int} -> int
  let n : int
  let origin_x : {origin: {x: 'a}} -> 'a
  let ox : int
  let tag : 'a ∧ {size: int} -> {size: int, value: 'a}
  let tagged : {size: int, value: {name: int, size: int}}
  let inner : int
  $ simplesub --self-check ../examples/recursion.sub
  let produce : int -> ({head: int, tail: 'a} as 'a)
  let sum : ({head: int, tail: 'a} as 'a) -> int
  let total : int
  let eat : (⊤ -> 'a as 'a)
  let ones : ({head: int, tail: 'a} as 'a)
  let first : int
  let self : 'a ∧ ('a -> 'b) -> 'b
  let y : ('a -> 'a) -> 'a
  let yeat : (⊤ -> 'a as 'a)
  $ simplesub --self-check ../examples/unions.sub
  let either : bool -> int ∨ {a: int}
  let both : {f: 'a} ∧ (int -> 'b) -> {r: 'a, s: 'b}
  let pick : bool -> {x: int}
  let picked_x : bool -> int
  let choose : bool -> 'a -> 'a -> 'a
  let mixed : int ∨ {a: int}
