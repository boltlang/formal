(** Simple-sub type inference: [typeTerm] (Fig. 8), [constrain] (Fig. 9),
    [extrude] (Fig. 7) and [freshenAbove] (described in Sec. 3.5.1). *)

open Types
open Syntax

exception Type_error of string

let err msg = raise (Type_error msg)

module StringMap = Map.Make (String)

type ctx = type_scheme StringMap.t

(** Cache of constraints already being solved / solved (Sec. 3.2.2). *)
module Cache = Hashtbl.Make (struct
  type t = simple_type * simple_type

  let equal (a1, b1) (a2, b2) = Types.equal a1 a2 && Types.equal b1 b2
  let hash (a, b) = Hashtbl.hash (Types.hash a, Types.hash b)
end)

(** Polar variables: a variable id together with a polarity
    ([true] = positive). *)
module PolarTbl = Hashtbl.Make (struct
  type t = int * bool

  let equal = ( = )
  let hash = Hashtbl.hash
end)

(** {1 Extrusion (Fig. 7)}

    Copy [ty] so that the result has level at most [lvl], creating
    approximating copies of the variables whose level is too high. *)
let rec extrude (ty : simple_type) (pol : bool) (lvl : int)
    (c : var_state PolarTbl.t) : simple_type =
  if level ty <= lvl then ty
  else
    match ty with
    | Primitive _ -> ty
    | Function (l, r) ->
        let l = extrude l (not pol) lvl c in
        Function (l, extrude r pol lvl c)
    | Record fs -> Record (List.map (fun (n, t) -> (n, extrude t pol lvl c)) fs)
    | Variable vs -> (
        match PolarTbl.find_opt c (vs.id, pol) with
        | Some nvs -> Variable nvs
        | None ->
            let nvs = fresh_state lvl in
            PolarTbl.add c (vs.id, pol) nvs;
            if pol then begin
              vs.upper_bounds <- Variable nvs :: vs.upper_bounds;
              nvs.lower_bounds <-
                List.map (fun t -> extrude t pol lvl c) vs.lower_bounds
            end
            else begin
              vs.lower_bounds <- Variable nvs :: vs.lower_bounds;
              nvs.upper_bounds <-
                List.map (fun t -> extrude t pol lvl c) vs.upper_bounds
            end;
            Variable nvs)

(** {1 Constraining (Fig. 9)} *)

let constrain (lhs : simple_type) (rhs : simple_type) : unit =
  let cache = Cache.create 64 in
  let rec go lhs rhs =
    (* Deviation from Fig. 9: skip reflexive constraints. Without this,
       [α <: α] records α as its own bound, which is sound but shows up as
       junk recursive types such as [('a ∧ 'b as 'b)] after coalescing. *)
    if Types.equal lhs rhs || Cache.mem cache (lhs, rhs) then ()
    else begin
      Cache.add cache (lhs, rhs) ();
      match (lhs, rhs) with
      | Primitive n0, Primitive n1 when String.equal n0 n1 -> ()
      | Function (l0, r0), Function (l1, r1) ->
          go l1 l0;
          go r0 r1
      | Record fs0, Record fs1 ->
          List.iter
            (fun (n1, t1) ->
              match List.assoc_opt n1 fs0 with
              | None ->
                  err
                    (Printf.sprintf "missing field: %s in %s" n1
                       (show_simple lhs))
              | Some t0 -> go t0 t1)
            fs1
      | Variable lv, _ when level rhs <= lv.level ->
          (* install the new bound *before* propagating (see Sec. 3.2.2) *)
          lv.upper_bounds <- rhs :: lv.upper_bounds;
          List.iter (fun lb -> go lb rhs) lv.lower_bounds
      | _, Variable rv when level lhs <= rv.level ->
          rv.lower_bounds <- lhs :: rv.lower_bounds;
          List.iter (fun ub -> go lhs ub) rv.upper_bounds
      | Variable lv, _ ->
          let rhs' = extrude rhs false lv.level (PolarTbl.create 8) in
          go lhs rhs'
      | _, Variable rv ->
          let lhs' = extrude lhs true rv.level (PolarTbl.create 8) in
          go lhs' rhs
      | _ ->
          err
            (Printf.sprintf "cannot constrain %s <: %s" (show_simple lhs)
               (show_simple rhs))
    end
  in
  go lhs rhs

(** {1 Instantiation} *)

(** Copy [ty], replacing every variable of level > [lim] with a fresh
    variable at level [lvl], copying bounds along (they may be cyclic). *)
let freshen_above (lim : int) (ty : simple_type) (lvl : int) : simple_type =
  let freshened : (int, var_state) Hashtbl.t = Hashtbl.create 16 in
  let rec freshen ty =
    if level ty <= lim then ty
    else
      match ty with
      | Variable vs -> (
          match Hashtbl.find_opt freshened vs.id with
          | Some v -> Variable v
          | None ->
              let v = fresh_state lvl in
              Hashtbl.add freshened vs.id v;
              v.lower_bounds <- List.map freshen vs.lower_bounds;
              v.upper_bounds <- List.map freshen vs.upper_bounds;
              Variable v)
      | Function (l, r) ->
          let l = freshen l in
          Function (l, freshen r)
      | Record fs -> Record (List.map (fun (n, t) -> (n, freshen t)) fs)
      | Primitive _ -> ty
  in
  freshen ty

let instantiate (sch : type_scheme) (lvl : int) : simple_type =
  match sch with
  | Simple t -> t
  | Poly (lim, body) -> freshen_above lim body lvl

(** {1 Typing (Fig. 8)} *)

let rec type_term (ctx : ctx) (lvl : int) (trm : term) : simple_type =
  match trm with
  | Lit _ -> Primitive "int"
  | Var name -> (
      match StringMap.find_opt name ctx with
      | Some sch -> instantiate sch lvl
      | None -> err ("identifier not found: " ^ name))
  | Rcd fs -> Record (List.map (fun (n, t) -> (n, type_term ctx lvl t)) fs)
  | Lam (name, body) ->
      let param = fresh_var lvl in
      Function (param, type_term (StringMap.add name (Simple param) ctx) lvl body)
  | App (f, a) ->
      let res = fresh_var lvl in
      let f_ty = type_term ctx lvl f in
      let a_ty = type_term ctx lvl a in
      constrain f_ty (Function (a_ty, res));
      res
  | Sel (obj, name) ->
      let res = fresh_var lvl in
      constrain (type_term ctx lvl obj) (Record [ (name, res) ]);
      res
  | Let (isrec, name, rhs, body) ->
      let sch = type_let_rhs ctx lvl isrec name rhs in
      type_term (StringMap.add name sch ctx) lvl body

(** Type the right-hand side of a (possibly recursive) let binding at level
    [lvl + 1] and generalize it. Shared by local and top-level lets. *)
and type_let_rhs ctx lvl isrec name rhs : type_scheme =
  let rhs_ty =
    if isrec then begin
      let exp = fresh_var (lvl + 1) in
      let inf = type_term (StringMap.add name (Simple exp) ctx) (lvl + 1) rhs in
      constrain inf exp;
      exp
    end
    else type_term ctx (lvl + 1) rhs
  in
  Poly (lvl, rhs_ty)

(** {1 Built-ins} *)

let bool_t = Primitive "bool"
let int_t = Primitive "int"

(** Initial context, as in the reference implementation. [if c then a else b]
    is parsed as [if c a b] with [if : ∀α. bool -> α -> α -> α]. *)
let builtins () : ctx =
  let fn a b = Function (a, b) in
  let if_ty =
    let v = fresh_var 1 in
    Poly (0, fn bool_t (fn v (fn v v)))
  in
  StringMap.of_seq
    (List.to_seq
       [
         ("true", Simple bool_t);
         ("false", Simple bool_t);
         ("not", Simple (fn bool_t bool_t));
         ("succ", Simple (fn int_t int_t));
         ("add", Simple (fn int_t (fn int_t int_t)));
         ("if", if_ty);
       ])
