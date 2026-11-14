Snapshots of every program in examples/.

  $ simplesub ../examples/basics.sub
  let const : 'a -> 'b -> 'a
  let id : 'a -> 'a
  let apply : 'a ∧ ('b -> 'c) -> 'b -> 'c
  let compose : 'a ∧ ('b -> 'c) -> 'd ∧ ('e -> 'b) -> 'e -> 'c
  let twice : 'a ∧ ('b -> 'c) ∧ ('d -> 'b) -> 'd -> 'c
  let flip : 'a ∧ ('b -> 'c ∧ ('d -> 'e)) -> 'd -> 'b -> 'e
  let inc : 'a ∨ (int -> int)
  let plus2 : 'a ∨ ('b ∧ int -> 'c ∨ int)
  let negate_twice : 'a ∨ ('b ∧ bool -> 'c ∨ bool)
  $ simplesub ../examples/errors.sub
  let not_a_function : type error: cannot constrain int <: (int -> α2)
  let wrong_arg : type error: cannot constrain bool <: int
  let missing_field : type error: missing field: b in {a: int}
  let bad_record_arg : type error: missing field: a in {b: int}
  let conflict : 'a ∧ 'b ∧ 'c ∧ int ∧ bool -> 'd ∨ int
  let call_conflict : type error: cannot constrain bool <: int
  let length : 'a ∨ (('c ∧ {tail: 'd ∧ 'b} ∧ {isNil: 'e ∧ bool} as 'b) -> 'f ∨ int)
  let finite : type error: missing field: tail in {isNil: bool}
  let fine : 'a ∨ int
  [1]
  $ simplesub ../examples/polymorphism.sub
  let id : 'a -> 'a
  let pair : {a: 'a ∨ int, b: 'b ∨ bool}
  let local : {i: 'a ∨ {v: 'b ∨ int}, b: 'c ∨ {v: 'd ∨ bool}}
  let extruded : 'a ∧ ('b ∨ bool ∨ int -> 'c ∧ 'd ∧ 'e) -> {a: 'e, b: 'd}
  let mono : 'a ∧ (bool -> 'b) ∧ (int -> 'c) -> {a: 'c, b: 'b}
  $ simplesub ../examples/records.sub
  let get_x : 'a ∧ {x: 'b} -> 'b
  let norm1 : 'a ∧ {y: 'b ∧ int} ∧ {x: 'c ∧ int} -> 'd ∨ int
  let n : 'a ∨ int
  let origin_x : 'a ∧ {origin: 'b ∧ {x: 'c}} -> 'c
  let ox : 'a ∨ int
  let tag : 'a ∧ {size: 'b ∧ int} -> {value: 'a, size: 'c ∨ int}
  let tagged : 'a ∨ {value: 'b ∨ {size: int, name: int}, size: 'c ∨ int}
  let inner : 'a ∨ int
  $ simplesub ../examples/recursion.sub
  let produce : 'a ∨ ('b ∧ int -> {head: 'b ∨ int, tail: ('d ∨ {head: 'b ∨ int, tail: 'c} as 'c)})
  let sum : 'a ∨ (('c ∧ {tail: 'd ∧ 'b} ∧ {head: 'e ∧ int} as 'b) -> 'f ∨ int)
  let total : 'a ∨ int
  let eat : ('b ∨ ('c -> 'a) as 'a)
  let ones : ('b ∨ {head: int, tail: 'a} as 'a)
  let first : 'a ∨ int
  let self : 'a ∧ ('a -> 'b) -> 'b
  let y : 'a ∧ ('b -> 'c ∧ 'd ∧ 'b) ∧ ('d -> 'e ∧ 'f) -> 'f
  let yeat : 'a ∨ ('b -> ('d ∨ ('b -> 'c) as 'c))
  $ simplesub ../examples/unions.sub
  let either : 'a ∧ bool -> 'b ∨ int ∨ {a: int}
  let both : 'a ∧ (int -> 'b) ∧ {f: 'c} -> {r: 'c, s: 'b}
  let pick : 'a ∧ bool -> 'b ∨ {x: int, y: bool} ∨ {x: int, z: bool}
  let picked_x : 'a ∧ 'b ∧ bool -> 'c ∨ int
  let choose : 'a ∧ bool -> 'b ∧ 'c ∧ 'd -> 'e ∧ 'c ∧ 'd -> 'd
  let mixed : 'a ∨ int ∨ {a: int}
