(** Internal (inference-time) and user-facing type representations.

    Internal types follow Fig. 6 of the paper: type variables carry mutable
    lists of lower and upper bounds plus a level used for let-polymorphism.
    User-facing types follow Fig. 5 and are produced by {!Coalesce}. *)

(** {1 Internal types (Fig. 6)} *)

module SSet = Set.Make (String)

(** How a parameter can be passed (issue #2): by position only (before a
    [/]), by position or by name, or by name only (after a [*]). *)
type pkind = PosOnly | Either | KwOnly

(** The label of the positional arguments in an argument record. Source code
    cannot write it: it is not an identifier. *)
let args_label = "*"

type simple_type =
  | Variable of var_state
  | Primitive of string
  | Function of simple_type * simple_type
  | Record of (string * simple_type) list * simple_type
      (** [Record (fields, tail)]: a record type, or a row when in tail
          position. Each field is [Abs] or a type [τ] (Rémy's [Pre τ]); the
          tail is [Abs], a row variable, or (transiently) another row. *)
  | Abs
      (** The top field type ("no guarantee", [Pre τ ≤ Abs]) and, in tail
          position, the top row (all remaining fields [Abs]). Open records
          [{x: τ, ..}] are [Record ([x, τ], Abs)]. *)
  | Missing
      (** The field that is definitely absent. [Missing ≤ Opt τ ≤ Abs]; it
          is unrelated to a present field. *)
  | Opt of simple_type
      (** A field only: missing, or present at the type ([Pre τ ≤ Opt τ],
          [Missing ≤ Opt τ]). *)
  | Nil
      (** In tail position only: the empty row, whose field at every label
          is [Missing]. Closed records [{x: τ}] are [Record ([x, τ], Nil)]. *)
  | Sig of sparam list
      (** A parameter list, as the domain of a function only: it stands for
          the union of the closed argument records [Dₖ] ({!sig_domains}),
          which simple types cannot write since they have no unions in
          negative positions. The parameters are in order: positional-only,
          then either-way, then keyword-only. *)

and sparam = {
  sname : string;
  skind : pkind;
  sty : simple_type;
  sopt : bool;  (** has a default: can be left out *)
}

and var_state = {
  id : int;  (** unique identity; variables are compared by [id] only *)
  level : int;
  kind : SSet.t;
      (** For a row variable: the labels it does *not* represent, because the
          record it is the tail of lists them explicitly (Rémy's kinds). A
          label in the kind projects to [Abs] from this variable. Empty for
          ordinary type variables. *)
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

(** Every variable ever created, by id (certificates need the variables
    created while typing a [let]'s right-hand side, see [Typer]). *)
let all_vars : (int, var_state) Hashtbl.t = Hashtbl.create 256

let fresh_state ?(kind = SSet.empty) lvl =
  let vs = { id = fresh_id (); level = lvl; kind; lower_bounds = []; upper_bounds = [] } in
  Hashtbl.replace all_vars vs.id vs;
  vs

let fresh_var ?kind lvl = Variable (fresh_state ?kind lvl)

(** Maximum level of any variable occurring (syntactically, not through
    bounds) in the type. The paper caches this in a [lazy val]; we recompute
    it, which is fine for experimentation. *)
let rec level = function
  | Variable vs -> vs.level
  | Primitive _ -> 0
  | Function (l, r) -> max (level l) (level r)
  | Record (fs, t) -> List.fold_left (fun acc (_, f) -> max acc (level f)) (level t) fs
  | Opt t -> level t
  | Abs | Missing | Nil -> 0
  | Sig ps -> List.fold_left (fun acc p -> max acc (level p.sty)) 0 ps

(** Structural equality where variables are compared by identity. This is the
    equality the constraint cache relies on (Scala's case-class equality with
    [VariableState] being a plain class). Never recurses into bounds, so it
    terminates even when bounds are cyclic. *)
let rec equal a b =
  match (a, b) with
  | Variable v, Variable w -> v.id = w.id
  | Primitive n, Primitive m -> String.equal n m
  | Function (a1, b1), Function (a2, b2) -> equal a1 a2 && equal b1 b2
  | Record (fs, t), Record (gs, u) ->
      List.equal (fun (n, t) (m, u) -> String.equal n m && equal t u) fs gs
      && equal t u
  | Abs, Abs | Missing, Missing | Nil, Nil -> true
  | Opt a, Opt b -> equal a b
  | Sig ps, Sig qs ->
      List.equal
        (fun p q ->
          String.equal p.sname q.sname && p.skind = q.skind && p.sopt = q.sopt
          && equal p.sty q.sty)
        ps qs
  | _ -> false

let rec hash = function
  | Variable v -> Hashtbl.hash (0, v.id)
  | Primitive n -> Hashtbl.hash (1, n)
  | Function (l, r) -> Hashtbl.hash (2, hash l, hash r)
  | Record (fs, t) ->
      Hashtbl.hash
        (3, List.map (fun (n, t) -> Hashtbl.hash (n, hash t)) fs, hash t)
  | Abs -> Hashtbl.hash 4
  | Missing -> Hashtbl.hash 5
  | Nil -> Hashtbl.hash 6
  | Opt t -> Hashtbl.hash (7, hash t)
  | Sig ps -> Hashtbl.hash (8, List.map (fun p -> Hashtbl.hash (p.sname, hash p.sty)) ps)

(** {1 Argument records}

    A call passes one closed record: the positional arguments as a list
    under {!args_label}, and one field per named argument. A list is nested
    closed records: [[a, b]] is [{hd = a; tl = {hd = b; tl = {}}}]. *)

let rec list_type = function
  | [] -> Record ([], Nil)
  | t :: ts -> Record ([ ("hd", t); ("tl", list_type ts) ], Nil)

(** The number of positional parameters without a default that must be
    passed by position ([m]: the positional-only ones without a default),
    and the number that can be ([p]). *)
let sig_bounds ps =
  let positional = List.filter (fun p -> p.skind <> KwOnly) ps in
  let m = List.length (List.filter (fun p -> p.skind = PosOnly && not p.sopt) ps) in
  (m, List.length positional)

(** [Dₖ] for [k] arguments passed by position:
    [{*: [τ₁, …, τₖ], Eₖ, Q | nil}], where [Eₖ] has a field for each
    either-way parameter after the [k]-th and [Q] one for each keyword-only
    parameter; a field is [Opt τ] when the parameter has a default. [None]
    unless [m ≤ k ≤ p]. *)
let sig_domain ps k =
  let m, p = sig_bounds ps in
  if k < m || k > p then None
  else
    let field q = (q.sname, if q.sopt then Opt q.sty else q.sty) in
    let rec split i = function
      | q :: rest when q.skind <> KwOnly ->
          let pos, named = split (i + 1) rest in
          if i < k then (q.sty :: pos, named)
          else if q.skind = Either then (pos, field q :: named)
          else (pos, named)
      | rest -> ([], List.map field rest)
    in
    let pos, named = split 0 ps in
    Some (Record ((args_label, list_type pos) :: named, Nil))

(** Every [(k, Dₖ)]. *)
let sig_domains ps =
  let m, p = sig_bounds ps in
  List.filter_map
    (fun k -> Option.map (fun d -> (k, d)) (sig_domain ps k))
    (List.init (p - m + 1) (fun i -> m + i))

(** The elements of a list type, if its spine is known. *)
let rec list_elems = function
  | Record (fs, t) -> (
      match (List.assoc_opt "hd" fs, List.assoc_opt "tl" fs, fs, t) with
      | Some hd, Some tl, [ _; _ ], Nil ->
          Option.map (fun ts -> hd :: ts) (list_elems tl)
      | None, None, [], Nil -> Some []
      | _ -> None)
  | _ -> None

(** Render a parameter list from its parameters' kinds and renderings:
    positional-only parameters, then [/], then either-way ones, then [*]
    and keyword-only ones. *)
let show_params (ps : (pkind * string) list) =
  let rec go prev = function
    | [] -> if prev = Some PosOnly then [ "/" ] else []
    | (k, s) :: rest ->
        let marks =
          (if prev = Some PosOnly && k <> PosOnly then [ "/" ] else [])
          @ if k = KwOnly && prev <> Some KwOnly then [ "*" ] else []
        in
        marks @ (s :: go (Some k) rest)
  in
  "(" ^ String.concat ", " (go None ps) ^ ")"

(** Debug rendering of internal types. Bounds are not shown. Records are
    written as in {!show_typ}: [{x: τ}] is closed, [{x: τ, ..}] open. *)
let rec show_simple = function
  | Variable vs -> Printf.sprintf "α%d" vs.id
  | Primitive n -> n
  | Function (l, r) ->
      Printf.sprintf "(%s -> %s)" (show_simple l) (show_simple r)
  | Record (fs, t) ->
      let field = function
        | n, Opt t -> n ^ "?: " ^ show_simple t
        | n, t when n = args_label -> (
            match list_elems t with
            | Some ts -> n ^ ": [" ^ String.concat ", " (List.map show_simple ts) ^ "]"
            | None -> n ^ ": " ^ show_simple t)
        | n, t -> n ^ ": " ^ show_simple t
      in
      let fields = List.map field fs in
      "{"
      ^ (match t with
         | Nil -> String.concat ", " fields
         | Abs -> String.concat ", " (fields @ [ ".." ])
         | t -> String.concat ", " fields ^ (if fs = [] then "| " else " | ") ^ show_simple t)
      ^ "}"
  | Abs -> "Abs"
  | Missing -> "Missing"
  | Opt t -> show_simple t ^ "?"
  | Nil -> "{}"
  | Sig ps ->
      show_params
        (List.map
           (fun p ->
             let t = show_simple p.sty in
             ( p.skind,
               match p.skind with
               | PosOnly -> if p.sopt then t ^ "?" else t
               | _ -> p.sname ^ (if p.sopt then "?: " else ": ") ^ t ))
           ps)

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
  | RecordType of (string * typ) list * typ
      (** fields ([AbsType], [MissingType], [Optional τ] or a type) and row
          tail ([NilType] = closed, [AbsType] = open) *)
  | AbsType  (** [Abs]: the top field / the top row *)
  | MissingType  (** the field that is definitely absent *)
  | Optional of typ  (** a field: missing, or present at the type *)
  | NilType  (** the empty row *)
  | RecursiveType of string * typ
  | TypeVariable of string
  | PrimitiveType of string
  | SigType of tparam list
      (** a parameter list, as a function domain ({!Sig}) *)

and tparam = { tname : string; tkind : pkind; tty : typ; topt : bool }

(** The elements of a list type, if it is one. *)
let rec typ_list_elems = function
  | RecordType ([], NilType) -> Some []
  | RecordType ([ ("hd", hd); ("tl", tl) ], NilType) ->
      Option.map (fun ts -> hd :: ts) (typ_list_elems tl)
  | _ -> None

(** Pretty-print a user-facing type, renaming variables to ['a], ['b], ... in
    order of first occurrence. Notation follows the reference implementation:
    [∨] for unions, [∧] for intersections, [(t as 'a)] for recursive types.

    Records: [{x: τ}] is closed (tail [NilType]), [{x: τ, ..}] open (tail
    [AbsType]) and [{x: τ | ρ}] has the row [ρ]. An optional field is
    written [x?: τ]; away from a field, [Optional τ] is [τ?] and the empty
    row [{}]. *)
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
        let l = match l with SigType ps -> sig_ ps | l -> go 11 l in
        let r = go 10 r in
        paren (outer > 10) (l ^ " -> " ^ r)
    | SigType ps -> sig_ ps
    | Union (l, r) ->
        let l = go 20 l in
        let r = go 20 r in
        paren (outer > 20) (l ^ " ∨ " ^ r)
    | Inter (l, r) ->
        let l = go 25 l in
        let r = go 25 r in
        paren (outer > 25) (l ^ " ∧ " ^ r)
    | AbsType -> "Abs"
    | MissingType -> "Missing"
    | NilType -> "{}"
    | Optional t -> go 30 t ^ "?"
    | RecordType (fs, tail) ->
        let field = function
          | n, Optional t -> n ^ "?: " ^ go 0 t
          | n, t when n = args_label && typ_list_elems t <> None ->
              let ts = Option.get (typ_list_elems t) in
              n ^ ": [" ^ String.concat ", " (List.map (go 0) ts) ^ "]"
          | n, t -> n ^ ": " ^ go 0 t
        in
        let fields = List.map field fs in
        "{"
        ^ (match tail with
           | NilType -> String.concat ", " fields
           | AbsType -> String.concat ", " (fields @ [ ".." ])
           | t -> String.concat ", " fields ^ (if fs = [] then "| " else " | ") ^ go 0 t)
        ^ "}"
    | RecursiveType (v, body) ->
        (* name the binder first so it gets the earliest letter *)
        let n = name_of v in
        let body = go 10 body in
        "(" ^ body ^ " as " ^ n ^ ")"
  and sig_ ps =
    show_params
      (List.map
         (fun p ->
           let t = go 30 p.tty in
           ( p.tkind,
             match p.tkind with
             | PosOnly -> if p.topt then t ^ "?" else t
             | _ -> p.tname ^ (if p.topt then "?: " else ": ") ^ go 0 p.tty ))
         ps)
  in
  go 0 t
