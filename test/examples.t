Snapshots of every program in examples/. --self-check also verifies that each
simplified type is equivalent to the raw coalesced one.

  $ boltcore --self-check ../examples/basics.sub
  let const : (x: 'a, y: ⊤) -> 'a
  let id : (x: 'a) -> 'a
  let apply : (f: {*: ['a]} -> 'b, x: 'a) -> 'b
  let compose : (f: {*: ['a]} -> 'b, g: {*: ['c]} -> 'a) -> (x: 'c) -> 'b
  let twice : (f: {*: ['a ∨ 'b]} -> 'a) -> (x: 'b) -> 'a
  let flip : (f: {*: ['a, 'b]} -> 'c) -> (x: 'b, y: 'a) -> 'c
  let inc : (x: int) -> int
  let plus2 : (x: int) -> int
  let negate_twice : (x: bool) -> bool
  $ boltcore --self-check ../examples/calls.sub
  let f : (x: int, y?: int) -> int
  let defaulted : int
  let positional : int
  let mixed : int
  let by_name : int
  let missing : type error: missing argument x
  let twice_x : type error: argument x is given twice, by position and by name
  let too_many : type error: too many positional arguments: 3 given, at most 2
  let unknown : type error: unexpected argument z
  let g : (int, /, b: int, c?: int, *, d: int) -> int
  let g1 : int
  let g2 : int
  let g_named_a : type error: argument a is positional-only
  let g_no_d : type error: too many positional arguments: 4 given, at most 3
  let range : (lo: 'a ∧ int, hi?: 'b) -> {hi: 'b ∨ int, lo: 'a}
  let r : {hi: int, lo: int}
  let call_xy : (h: {*: [], x: int} ∨ {*: [int]} -> 'a) -> {a: 'a, b: 'a}
  let ok : {a: int, b: int}
  let not_by_name : type error: too few positional arguments: 0 given, at least 1
  let zero : () -> int
  let z : int
  [1]
  $ boltcore --rectypes --self-check ../examples/errors.sub
  let not_a_function : type error: cannot constrain int <: ({*: [int]} -> α1)
  let wrong_arg : type error: cannot constrain bool <: int
  let missing_field : type error: missing field: b in {a: int}
  let bad_record_arg : type error: missing field: a in {b: int}
  let conflict : (x: bool ∧ int) -> int
  let call_conflict : type error: cannot constrain bool <: int
  let length : (l: ({isNil: bool, tail: 'a, ..} as 'a)) -> int
  let finite : type error: missing field: tail in {isNil: bool}
  let fine : int
  [1]
  $ boltcore --self-check ../examples/optional.sub
  let get_y : (r: {y?: 'a, ..}) -> 'a ∨ int
  let none : int
  let some : int
  let other : bool ∨ int
  let maybe : (b: bool) -> {y?: int}
  let read : (b: bool) -> int
  let unsafe : type error: missing field: y in {}
  let both : (r: {y: 'a, ..}) -> {a: 'a ∨ int, b: 'a}
  let chain : (r: {x?: 'a, y?: 'a, ..}) -> 'a ∨ int
  let nested : (r: {a?: {b?: 'a, ..}, ..}) -> 'a ∨ int
  let pick : (b: bool) -> {x?: int, y?: bool}
  let extend : (b: bool, r: {x: Abs | 'a}) -> {} ∨ {x: int | 'a}
  [1]
  $ boltcore --self-check ../examples/polymorphism.sub
  let id : (x: 'a) -> 'a
  let pair : {a: int, b: bool}
  let local : {b: {v: bool}, i: {v: int}}
  let extruded : (k: {*: [bool ∨ int]} -> 'a) -> {a: 'a, b: 'a}
  let mono : (g: {*: [bool ∨ int]} -> 'a) -> {a: 'a, b: 'a}
  $ boltcore --self-check ../examples/records.sub
  let get_x : (p: {x: 'a, ..}) -> 'a
  let norm1 : (p: {x: int, y: int, ..}) -> int
  let n : int
  let origin_x : (shape: {origin: {x: 'a, ..}, ..}) -> 'a
  let ox : int
  let tag : (p: 'a ∧ {size: int, ..}) -> {size: int, value: 'a}
  let tagged : {size: int, value: {name: int, size: int}}
  let inner : int
  $ boltcore --self-check ../examples/rows.sub
  let addY : (r: {y: Abs | 'a}) -> {y: int | 'a}
  let fromX : {x: int, y: int}
  let xAgain : int
  let flipX : (r: {x: bool | 'a}) -> {x: bool | 'a}
  let boolToInt : (r: {x: bool | 'a}) -> {x: int | 'a}
  let changed : {keep: int, x: int}
  let setBoth : (r: {a: Abs, b: Abs | 'a}) -> {a: int, b: bool | 'a}
  let both : {fromX: int, fromZ: bool}
  let either : (b: bool, r: {y: Abs | 'a}, s: {z: Abs | 'b}) -> {z: int | 'b} ∨ {y: int | 'a}
  let count : (r: 'a ∧ {n: int | 'b ∧ {done: bool, ..}} ∧ {done: bool, ..}) -> 'a ∨ {n: int | 'b}
  let noZ : type error: missing field: z in {x: int}
  [1]
  $ boltcore --rectypes --self-check ../examples/recursion.sub
  let produce : (n: int) -> ({head: int, tail: 'a} as 'a)
  let sum : (s: ({head: int, tail: 'a, ..} as 'a)) -> int
  let total : int
  let eat : ((x: ⊤) -> 'a as 'a)
  let ones : type error: let rec ones: the right-hand side must be a function
  let first : type error: identifier not found: ones
  let self : (x: 'a ∧ ({*: ['a]} -> 'b)) -> 'b
  let y : (f: {*: ['a]} -> 'a) -> 'a
  let yeat : ((x: ⊤) -> 'a as 'a)
  [1]
  $ boltcore --self-check ../examples/unions.sub
  let either : (b: bool) -> int ∨ {a: int}
  let both : (x: {f: 'a, ..} ∧ ({*: [int]} -> 'b)) -> {r: 'a, s: 'b}
  let pick : (b: bool) -> {x: int, y?: bool, z?: bool}
  let picked_x : (b: bool) -> int
  let choose : (b: bool, x: 'a, y: 'a) -> 'a
  let mixed : int ∨ {a: int}
