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
    | Record (fs, t) ->
        let fs = List.map (fun (n, f) -> (n, extrude f pol lvl c)) fs in
        Record (fs, extrude t pol lvl c)
    | Abs -> Abs
    | Variable vs -> (
        match PolarTbl.find_opt c (vs.id, pol) with
        | Some nvs -> Variable nvs
        | None ->
            let nvs = fresh_state ~kind:vs.kind lvl in
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

(** {1 Rows}

    Following Marques et al. (2024), rows are [Record (fields, tail)] where
    each field is [Abs] (top: no guarantee) or a type [τ] ([Pre τ]), and the
    tail is [Abs] or a row variable. A row variable used as the tail of a row
    never "contains" that row's labels; constraining maintains this.

    The paper expands a row variable by substituting into it. We instead
    expand through constraints: to compare [{fs₀ | ρ} ≤ {fs₁ | t₁}] where
    [fs₁] mentions labels [L] missing from [fs₀], we constrain
    [ρ ≤ {L-fields of fs₁ | ρ'}] and then [{fs₀ ∖ fs₁ | ρ'} ≤ t₁]. The
    expansion variable [ρ'] is memoized per [(ρ, L)], so recursive types still
    only produce finitely many distinct constraints.

    {b Kinds.} A row variable's kind is the set of labels it does not
    represent, because the record it is the tail of lists them. A label in
    the kind projects to [Abs] from the variable, so it is never expanded;
    the expansion variable [ρ'] has kind [kind ρ ∪ L], strictly larger since
    [L] avoids [kind ρ]. Every constraint relates rows of equal kind
    ([row_kind]), which [constrain] checks whenever it installs a bound: a
    failure would be a bug in the type checker, not in the program. *)

(** Flatten nested rows: [{fs | {fs' | t}}] becomes [{fs, fs' | t}]. *)
let rec row_view = function
  | Record (fs, t) ->
      let fs', t' = row_view t in
      (fs @ fs', t')
  | t -> ([], t)

let expansions : (int * string list, simple_type) Hashtbl.t = Hashtbl.create 16

let expansion (rho : simple_type) (labels : string list) : simple_type =
  match rho with
  | Variable vs -> (
      let key = (vs.id, List.sort_uniq String.compare labels) in
      match Hashtbl.find_opt expansions key with
      | Some r -> r
      | None ->
          let kind = List.fold_left (fun k l -> SSet.add l k) vs.kind labels in
          let r = fresh_var ~kind vs.level in
          Hashtbl.add expansions key r;
          r)
  | _ -> fresh_var (level rho)

exception Kind_error of string

(** The kind of a row expression: the labels it does not represent. [None]
    for types that are not rows with a variable tail ([Abs] tails, functions,
    primitives), whose kind is unconstrained. Raises [Kind_error] if a record
    lists a label its tail variable does not lack. *)
let rec row_kind = function
  | Variable vs -> Some vs.kind
  | Record (fs, t) -> (
      match row_kind t with
      | None -> None
      | Some k ->
          let labels = SSet.of_list (List.map fst fs) in
          if not (SSet.subset labels k) then
            raise
              (Kind_error
                 (Printf.sprintf "record lists %s, which its tail does not lack"
                    (String.concat ", " (SSet.elements (SSet.diff labels k)))));
          Some (SSet.diff k labels))
  | _ -> None

(** {1 No structural recursive types}

    Like an occurs check, inference rejects a type variable that reaches
    itself through a type constructor, following both upper and lower
    bounds. Cycles of variable bounds only ([α ≤ β ≤ α]) equate variables
    and are allowed. [--rectypes] restores the paper's equi-recursive types.
    Only installing a bound in [constrain] can close a cycle: extrusion and
    instantiation copy an acyclic graph, and copies of it are acyclic. This
    is the check the Lean model's [StructRanked] stands for. *)

let allow_recursive = ref false

let rec vars_of acc = function
  | Variable vs -> vs :: acc
  | Function (l, r) -> vars_of (vars_of acc l) r
  | Record (fs, t) -> List.fold_left (fun acc (_, f) -> vars_of acc f) (vars_of acc t) fs
  | Primitive _ | Abs -> acc

(** Does [v] reach itself through a type constructor? A search over
    (variable, passed a constructor) pairs. *)
let reaches_itself (v : var_state) : bool =
  let seen = Hashtbl.create 16 in
  let rec visit (u : var_state) guarded =
    if u == v && guarded then true
    else if Hashtbl.mem seen (u.id, guarded) then false
    else begin
      Hashtbl.add seen (u.id, guarded) ();
      List.exists (edge guarded) (u.upper_bounds @ u.lower_bounds)
    end
  and edge guarded = function
    | Variable w -> visit w guarded
    | b -> List.exists (fun w -> visit w true) (vars_of [] b)
  in
  List.exists (edge false) (v.upper_bounds @ v.lower_bounds)

(** Reject the bound just installed on [v] if it closes a recursive type. *)
let check_acyclic (v : var_state) (bound : simple_type) =
  if (not !allow_recursive) && reaches_itself v then
    err
      (Printf.sprintf
         "recursive type: %s reaches itself through a type constructor (via bound %s)"
         (show_simple (Variable v)) (show_simple bound))

(** Check that a new bound of [v] has [v]'s kind. *)
let check_kind (vs : var_state) (bound : simple_type) =
  match row_kind bound with
  | Some k when not (SSet.equal k vs.kind) ->
      raise
        (Kind_error
           (Printf.sprintf "bound %s of α%d has kind {%s}, expected {%s}"
              (show_simple bound) vs.id
              (String.concat ", " (SSet.elements k))
              (String.concat ", " (SSet.elements vs.kind))))
  | _ -> ()

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
      | _, Abs -> () (* Abs is the top field and the top row *)
      | Abs, Record (fs1, t1) ->
          (* the top row is below a row only if that row guarantees nothing *)
          List.iter (fun (n, f1) -> field lhs n Abs f1) fs1;
          go Abs t1
      | Record _, Record _ ->
          let fs0, t0 = row_view lhs and fs1, t1 = row_view rhs in
          (* fields mentioned on both sides *)
          List.iter
            (fun (n, f1) ->
              match List.assoc_opt n fs0 with
              | Some f0 -> field lhs n f0 f1
              | None -> ())
            fs1;
          (* fields required on the right but only available from t0 *)
          let missing = List.filter (fun (n, _) -> not (List.mem_assoc n fs0)) fs1 in
          let t0 =
            if missing = [] then t0
            else
              match t0 with
              | Abs ->
                  List.iter (fun (n, f1) -> field lhs n Abs f1) missing;
                  Abs
              | Variable vs ->
                  (* labels in the tail's kind are not represented by it:
                     they are absent; only the others are expanded *)
                  let absent, present =
                    List.partition (fun (n, _) -> SSet.mem n vs.kind) missing
                  in
                  List.iter (fun (n, f1) -> field lhs n Abs f1) absent;
                  if present = [] then t0
                  else begin
                    let rho' = expansion t0 (List.map fst present) in
                    go t0 (Record (present, rho'));
                    rho'
                  end
              | _ ->
                  let rho' = expansion t0 (List.map fst missing) in
                  go t0 (Record (missing, rho'));
                  rho'
          in
          (* what is left of the left row flows into the right tail *)
          let extra = List.filter (fun (n, _) -> not (List.mem_assoc n fs1)) fs0 in
          go (if extra = [] then t0 else Record (extra, t0)) t1
      | Variable lv, _ when level rhs <= lv.level ->
          check_kind lv rhs;
          (* install the new bound *before* propagating (see Sec. 3.2.2) *)
          lv.upper_bounds <- rhs :: lv.upper_bounds;
          check_acyclic lv rhs;
          List.iter (fun lb -> go lb rhs) lv.lower_bounds
      | _, Variable rv when level lhs <= rv.level ->
          check_kind rv lhs;
          rv.lower_bounds <- lhs :: rv.lower_bounds;
          check_acyclic rv lhs;
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
  (* field types: Abs is the top; an absent field cannot satisfy a present one *)
  and field record n f0 f1 =
    match (f0, f1) with
    | _, Abs -> ()
    | Abs, _ -> err (Printf.sprintf "missing field: %s in %s" n (show_simple record))
    | _ -> go f0 f1
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
              let v = fresh_state ~kind:vs.kind lvl in
              Hashtbl.add freshened vs.id v;
              v.lower_bounds <- List.map freshen vs.lower_bounds;
              v.upper_bounds <- List.map freshen vs.upper_bounds;
              Variable v)
      | Function (l, r) ->
          let l = freshen l in
          Function (l, freshen r)
      | Record (fs, t) ->
          let fs = List.map (fun (n, f) -> (n, freshen f)) fs in
          Record (fs, freshen t)
      | Primitive _ | Abs -> ty
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
  | Rcd fs -> Record (List.map (fun (n, t) -> (n, type_term ctx lvl t)) fs, Abs)
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
      constrain (type_term ctx lvl obj) (Record ([ (name, res) ], Abs));
      res
  | Ext (obj, fs) ->
      (* [obj with {l = e, ...}] overwrites or adds the fields: [obj] may have
         anything at the labels, and its other fields are carried by [rho] *)
      let obj_ty = type_term ctx lvl obj in
      let fs = List.map (fun (n, t) -> (n, type_term ctx lvl t)) fs in
      let fs =
        (* a later binding of the same label wins *)
        List.rev
          (List.fold_left (fun acc (n, t) -> (n, t) :: List.remove_assoc n acc) [] fs)
      in
      if fs = [] then obj_ty (* [obj with {}] is just [obj] *)
      else begin
        (* [rho] stands for the other fields: it lacks the extended labels *)
        let rho = fresh_var ~kind:(SSet.of_list (List.map fst fs)) lvl in
        constrain obj_ty (Record (List.map (fun (n, _) -> (n, Abs)) fs, rho));
        Record (fs, rho)
      end
  | Let (isrec, name, rhs, body) ->
      let sch = type_let_rhs ctx lvl isrec name rhs in
      type_term (StringMap.add name sch ctx) lvl body

(** Type the right-hand side of a (possibly recursive) let binding at level
    [lvl + 1] and generalize it. Shared by local and top-level lets.

    The language is eagerly evaluated, so [let rec x = s] evaluates [s]
    once, before [x] exists: [s] must be a function, whose body only runs
    (and reads [x]) once it is called. Cyclic data such as
    [let rec ones = {head = 1; tail = ones}] is rejected. *)
and type_let_rhs ctx lvl isrec name rhs : type_scheme =
  (match rhs with
  | Lam _ -> ()
  | _ when isrec ->
      err (Printf.sprintf "let rec %s: the right-hand side must be a function" name)
  | _ -> ());
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
