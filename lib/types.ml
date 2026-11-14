(** Internal (inference-time) and user-facing type representations.

    Internal types follow Fig. 6 of the paper: type variables carry mutable
    lists of lower and upper bounds plus a level used for let-polymorphism.
    User-facing types follow Fig. 5 and are produced by {!Coalesce}. *)

(** {1 Internal types (Fig. 6)} *)

type simple_type =
  | Variable of var_state
  | Primitive of string
  | Function of simple_type * simple_type
  | Record of (string * simple_type) list

and var_state = {
  id : int;  (** unique identity; variables are compared by [id] only *)
  level : int;
  mutable lower_bounds : simple_type list;
  mutable upper_bounds : simple_type list;
}

(** [Simple t] plays the role of a [SimpleType] used as a [TypeScheme] in the
    paper; [Poly (lvl, body)] is [PolymorphicType(level, body)]: variables in
    [body] whose level is strictly greater than [lvl] are quantified. *)
type type_scheme = Simple of simple_type | Poly of int * simple_type

let counter = ref 0

let fresh_id () =
  incr counter;
  !counter

let fresh_state lvl =
  { id = fresh_id (); level = lvl; lower_bounds = []; upper_bounds = [] }

let fresh_var lvl = Variable (fresh_state lvl)

(** Maximum level of any variable occurring (syntactically, not through
    bounds) in the type. The paper caches this in a [lazy val]; we recompute
    it, which is fine for experimentation. *)
let rec level = function
  | Variable vs -> vs.level
  | Primitive _ -> 0
  | Function (l, r) -> max (level l) (level r)
  | Record fs -> List.fold_left (fun acc (_, t) -> max acc (level t)) 0 fs

(** Structural equality where variables are compared by identity. This is the
    equality the constraint cache relies on (Scala's case-class equality with
    [VariableState] being a plain class). Never recurses into bounds, so it
    terminates even when bounds are cyclic. *)
let rec equal a b =
  match (a, b) with
  | Variable v, Variable w -> v.id = w.id
  | Primitive n, Primitive m -> String.equal n m
  | Function (a1, b1), Function (a2, b2) -> equal a1 a2 && equal b1 b2
  | Record fs, Record gs ->
      List.equal (fun (n, t) (m, u) -> String.equal n m && equal t u) fs gs
  | _ -> false

let rec hash = function
  | Variable v -> Hashtbl.hash (0, v.id)
  | Primitive n -> Hashtbl.hash (1, n)
  | Function (l, r) -> Hashtbl.hash (2, hash l, hash r)
  | Record fs ->
      Hashtbl.hash (3, List.map (fun (n, t) -> Hashtbl.hash (n, hash t)) fs)

(** Debug rendering of internal types. Bounds are not shown. *)
let rec show_simple = function
  | Variable vs -> Printf.sprintf "α%d" vs.id
  | Primitive n -> n
  | Function (l, r) ->
      Printf.sprintf "(%s -> %s)" (show_simple l) (show_simple r)
  | Record fs ->
      "{"
      ^ String.concat ", "
          (List.map (fun (n, t) -> n ^ ": " ^ show_simple t) fs)
      ^ "}"

(** Debug rendering of a variable together with its bounds. *)
let show_var_state vs =
  Printf.sprintf "α%d@%d [%s] <: α%d <: [%s]" vs.id vs.level
    (String.concat ", " (List.map show_simple vs.lower_bounds))
    vs.id
    (String.concat ", " (List.map show_simple vs.upper_bounds))

(** {1 User-facing types (Fig. 5)} *)

type typ =
  | Top
  | Bot
  | Union of typ * typ
  | Inter of typ * typ
  | FunctionType of typ * typ
  | RecordType of (string * typ) list
  | RecursiveType of string * typ
  | TypeVariable of string
  | PrimitiveType of string

(** Pretty-print a user-facing type, renaming variables to ['a], ['b], ... in
    order of first occurrence. Notation follows the reference implementation:
    [∨] for unions, [∧] for intersections, [(t as 'a)] for recursive types. *)
let show_typ (t : typ) : string =
  let names = Hashtbl.create 16 in
  let next = ref 0 in
  let name_of v =
    match Hashtbl.find_opt names v with
    | Some n -> n
    | None ->
        let i = !next in
        incr next;
        let letter = String.make 1 (Char.chr (Char.code 'a' + (i mod 26))) in
        let n = "'" ^ letter ^ if i >= 26 then string_of_int (i / 26) else "" in
        Hashtbl.add names v n;
        n
  in
  (* precedences: -> = 10, ∨ = 20, ∧ = 25; recursive types are always
     parenthesized *)
  let paren b s = if b then "(" ^ s ^ ")" else s in
  let rec go outer = function
    | Top -> "⊤"
    | Bot -> "⊥"
    | TypeVariable v -> name_of v
    | PrimitiveType n -> n
    (* [let] sequencing: OCaml evaluates operands right-to-left, and naming
       must follow left-to-right reading order *)
    | FunctionType (l, r) ->
        let l = go 11 l in
        let r = go 10 r in
        paren (outer > 10) (l ^ " -> " ^ r)
    | Union (l, r) ->
        let l = go 20 l in
        let r = go 20 r in
        paren (outer > 20) (l ^ " ∨ " ^ r)
    | Inter (l, r) ->
        let l = go 25 l in
        let r = go 25 r in
        paren (outer > 25) (l ^ " ∧ " ^ r)
    | RecordType fs ->
        "{"
        ^ String.concat ", " (List.map (fun (n, t) -> n ^ ": " ^ go 0 t) fs)
        ^ "}"
    | RecursiveType (v, body) ->
        (* name the binder first so it gets the earliest letter *)
        let n = name_of v in
        let body = go 10 body in
        "(" ^ body ^ " as " ^ n ^ ")"
  in
  go 0 t
