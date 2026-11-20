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

(** {1 Certificates}

    Ghost state for certificates ({!Cert}), which the Lean checker
    ([lean/Main.lean]) verifies: every constraint [constrain] accepts, the
    relation between each extruded type and its original, and each
    instantiation. Recorded only while [recording] is set; nothing here
    affects inference. *)

let recording = ref false

(** Accepted constraints, newest first. *)
let accepted : (simple_type * simple_type) list ref = ref []

let note a b = if !recording then accepted := (a, b) :: !accepted

(** A use of a let-bound name: the scheme's generalized variables, and a
    copy of each, by original id. [freshen_above] copies the variables
    reachable from the scheme's type; while recording, the others get a
    copy too, with the renamed bounds, so that a certificate can instantiate
    every constraint of the scheme. *)
type inst = { gen : var_state list; copies : (int * var_state) list }

let rec rename (m : (int, var_state) Hashtbl.t) = function
  | Variable vs -> (
      match Hashtbl.find_opt m vs.id with Some w -> Variable w | None -> Variable vs)
  | Function (a, b) -> Function (rename m a, rename m b)
  | Record (fs, t) -> Record (List.map (fun (n, f) -> (n, rename m f)) fs, rename m t)
  | Opt t -> Opt (rename m t)
  | Sig ps -> Sig (List.map (fun p -> { p with sty = rename m p.sty }) ps)
  | (Primitive _ | Abs | Missing | Nil) as t -> t

(** Copy the generalized variables [freshen_above] did not copy. *)
let complete_copies (gen : var_state list) copies lvl : (int * var_state) list =
  let m = Hashtbl.create 16 in
  List.iter (fun (id, c) -> Hashtbl.replace m id c) copies;
  let fresh =
    List.filter_map
      (fun (a : var_state) ->
        if Hashtbl.mem m a.id then None
        else begin
          let v = fresh_state ~kind:a.kind lvl in
          Hashtbl.replace m a.id v;
          Some (a, v)
        end)
      gen
  in
  List.iter
    (fun ((a : var_state), v) ->
      v.lower_bounds <- List.map (rename m) a.lower_bounds;
      v.upper_bounds <- List.map (rename m) a.upper_bounds)
    fresh;
  List.map (fun (a : var_state) -> (a.id, Hashtbl.find m a.id)) gen

(** Instantiations, newest first. *)
let insts : inst list ref = ref []

(** The generalized variables of each [Poly] scheme, by physical identity:
    the variables above its level created while typing the right-hand
    side, reachable from the type or not. *)
let gens : (type_scheme * var_state list) list ref = ref []

let gen_of sch = try List.assq sch !gens with Not_found -> []

(** What relates a signature to its extruded copy, for certificates.
    [extrude] records the pair of signatures and the pairs of parameter
    types. A step of the checker also needs what [constrain] would go
    through: each argument record of the lower signature below the upper
    signature and below its record for the same number of positional
    arguments, and their lists of positional arguments, suffix by suffix. *)
let note_sig pol ps ps' =
  if !recording then begin
    let lo, hi = if pol then (ps, ps') else (ps', ps) in
    let rec lists a b =
      match (a, b) with
      | Record ([ ("hd", _); ("tl", ta) ], Nil), Record ([ ("hd", _); ("tl", tb) ], Nil) ->
          note a b;
          lists ta tb
      | _ -> ()
    in
    List.iter
      (fun (k, d) ->
        match sig_domain hi k with
        | None -> ()
        | Some d' -> (
            note d (Sig hi);
            note d d';
            match (d, d') with
            | Record ((_, l) :: _, _), Record ((_, l') :: _, _) -> lists l l'
            | _ -> ()))
      (sig_domains lo)
  end

(** {1 Extrusion (Fig. 7)}

    Copy [ty] so that the result has level at most [lvl], creating
    approximating copies of the variables whose level is too high. *)
let rec extrude (ty : simple_type) (pol : bool) (lvl : int)
    (c : var_state PolarTbl.t) : simple_type =
  if level ty <= lvl then ty
  else begin
    let ty' = extrude1 ty pol lvl c in
    (* a positive copy is above the original, a negative one below *)
    if pol then note ty ty' else note ty' ty;
    ty'
  end

and extrude1 ty pol lvl c =
    match ty with
    | Primitive _ -> ty
    | Function (l, r) ->
        let l = extrude l (not pol) lvl c in
        Function (l, extrude r pol lvl c)
    | Record (fs, t) ->
        (* an optional field is not a type: only the type in it is recorded *)
        let field = function
          | Opt t -> Opt (extrude t pol lvl c)
          | f -> extrude f pol lvl c
        in
        let fs = List.map (fun (n, f) -> (n, field f)) fs in
        Record (fs, extrude t pol lvl c)
    | Opt t -> Opt (extrude t pol lvl c)
    | Sig ps ->
        (* parameters are fields of the argument records: same polarity *)
        let ps' = List.map (fun p -> { p with sty = extrude p.sty pol lvl c }) ps in
        note_sig pol ps ps';
        Sig ps'
    | Abs | Missing | Nil -> ty
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

    Two more fields, for optional fields and closed records: [Missing]
    (definitely absent) and [Opt τ] (missing, or present at [τ]), with
    [Pre τ ≤ Opt τ], [Missing ≤ Opt τ] and [Opt τ ≤ Abs]. The tail [Nil] is
    the empty row, [Missing] at every label: a record literal is closed.
    Width subtyping is kept, since [Nil ≤ Abs].

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
  | Opt t -> vars_of acc t
  | Sig ps -> List.fold_left (fun acc p -> vars_of acc p.sty) acc ps
  | Primitive _ | Abs | Missing | Nil -> acc

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
      note lhs rhs;
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
      | Nil, Record (fs1, t1) ->
          (* the empty row is below a row that accepts every label missing *)
          List.iter (fun (n, f1) -> field lhs n Missing f1) fs1;
          go Nil t1
      | Record _, Nil ->
          (* a row is below the empty row if it has no field at all *)
          let fs0, t0 = row_view lhs in
          List.iter (fun (n, f0) -> field lhs n f0 Missing) fs0;
          go t0 Nil
      | Abs, Nil ->
          err "a record that may have other fields cannot be used as a closed record"
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
              | Nil ->
                  List.iter (fun (n, f1) -> field lhs n Missing f1) missing;
                  Nil
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
      | Record _, Sig ps -> call lhs ps
      | Sig ps, (Record _ | Sig _) ->
          (* a signature is the union of its records *)
          List.iter (fun (_, d) -> go d rhs) (sig_domains ps)
      | _ ->
          err
            (Printf.sprintf "cannot constrain %s <: %s" (show_simple lhs)
               (show_simple rhs))
    end
  (* An argument record below a signature: the number of positional
     arguments picks [Dₖ], then it is an ordinary record constraint. When
     the record is closed, its named arguments are checked first, for
     better messages than those of the field constraints. *)
  and call args ps =
    let fs0, t0 = row_view args in
    let elems =
      match List.assoc_opt args_label fs0 with Some l -> list_elems l | None -> None
    in
    let k =
      match elems with
      | Some ts -> List.length ts
      | None -> err "a function with a parameter list needs an argument list of known length"
    in
    let m, p = sig_bounds ps in
    if k > p then
      err (Printf.sprintf "too many positional arguments: %d given, at most %d" k p);
    if k < m then begin
      List.iter
        (fun (n, _) ->
          if List.exists (fun q -> q.sname = n && q.skind = PosOnly) ps then
            err (Printf.sprintf "argument %s is positional-only" n))
        fs0;
      err (Printf.sprintf "too few positional arguments: %d given, at least %d" k m)
    end;
    let d = Option.get (sig_domain ps k) in
    (if t0 = Nil then
       let fsd, _ = row_view d in
       let named = List.filter (fun (n, _) -> n <> args_label) fs0 in
       List.iter
         (fun (n, _) ->
           if not (List.mem_assoc n fsd) then
             match List.find_opt (fun q -> q.sname = n) ps with
             | Some { skind = PosOnly; _ } ->
                 err (Printf.sprintf "argument %s is positional-only" n)
             | Some _ ->
                 err (Printf.sprintf "argument %s is given twice, by position and by name" n)
             | None -> err (Printf.sprintf "unexpected argument %s" n))
         named;
       List.iter
         (fun (n, f) ->
           match f with
           | Opt _ -> ()
           | _ ->
               if n <> args_label && not (List.mem_assoc n named) then
                 err (Printf.sprintf "missing argument %s" n))
         fsd);
    go args d
  (* fields: [Pre τ ≤ Opt τ], [Missing ≤ Opt τ], [Opt τ ≤ Abs]; a field
     that is or may be missing cannot satisfy a present one, and a field
     that is or may be present cannot satisfy [Missing] *)
  and field record n f0 f1 =
    let fail what = err (Printf.sprintf "%s: %s in %s" what n (show_simple record)) in
    match (f0, f1) with
    | _, Abs -> ()
    | Abs, (Missing | Opt _) -> fail "nothing is known about field"
    | Abs, _ -> fail "missing field"
    | Missing, (Missing | Opt _) -> ()
    | Missing, _ -> fail "missing field"
    | Opt t0, Opt t1 -> go t0 t1
    | Opt _, Missing -> fail "unexpected field"
    | Opt _, _ -> fail "field may be missing"
    | _, Missing -> fail "unexpected field"
    | _, Opt t1 -> go f0 t1
    | _ -> go f0 f1
  in
  go lhs rhs

(** {1 Instantiation} *)

(** Copy [ty], replacing every variable of level > [lim] with a fresh
    variable at level [lvl], copying bounds along (they may be cyclic). *)
let freshen_above_copies (lim : int) (ty : simple_type) (lvl : int) :
    simple_type * (int * var_state) list =
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
      | Opt t -> Opt (freshen t)
      | Sig ps -> Sig (List.map (fun p -> { p with sty = freshen p.sty }) ps)
      | Primitive _ | Abs | Missing | Nil -> ty
  in
  let ty = freshen ty in
  (ty, List.of_seq (Hashtbl.to_seq freshened))

let freshen_above lim ty lvl = fst (freshen_above_copies lim ty lvl)

let instantiate (sch : type_scheme) (lvl : int) : simple_type =
  match sch with
  | Simple t -> t
  | Poly (lim, body) -> freshen_above lim body lvl

(** {1 Typing (Fig. 8)}

    [type_term_ann] also returns the term annotated with what a certificate's
    typing skeleton needs (the Lean [Ann]): the type of each [fun] parameter,
    of each application and selection result, the row of each extension, the
    generalized variables of each [let], and each instantiation. *)

type ann =
  | ALit of int
  | AVar of string
  | AInst of string * inst
  | ALam of string * simple_type * ann
  | AApp of ann * ann * simple_type
  | ARcd of (string * ann) list
  | ASel of ann * string * simple_type
  | ASelOr of ann * string * ann * simple_type
  | AExt of ann * (string * ann) list * simple_type
  | ALet of string * var_state list * ann * ann
  | ALetRec of string * var_state list * simple_type * ann * ann
  | AIf of ann * ann * ann * simple_type  (** the type of the result *)
  | AFn of (string * pkind * simple_type * ann option) list * ann
      (** each parameter's kind, type and annotated default *)

(** A [let]'s right-hand side: its generalized variables, the type of the
    name in its own body (for [let rec]), and the annotated term. *)
type let_ann = { gen : var_state list; rec_ty : simple_type option; rhs : ann }

(** The variables above [lvl] created since the counter was [before]. *)
let created_above before lvl =
  List.filter_map
    (fun id ->
      match Hashtbl.find_opt all_vars id with
      | Some vs when vs.level > lvl -> Some vs
      | _ -> None)
    (List.init (!counter - before) (fun i -> before + 1 + i))

let rec type_term_ann (ctx : ctx) (lvl : int) (trm : term) : simple_type * ann =
  match trm with
  | Lit n -> (Primitive "int", ALit n)
  | Var name -> (
      match StringMap.find_opt name ctx with
      | Some (Simple t) -> (t, AVar name)
      | Some (Poly (lim, body) as sch) ->
          let ty, copies = freshen_above_copies lim body lvl in
          let gen = gen_of sch in
          let inst =
            if !recording then begin
              let inst = { gen; copies = complete_copies gen copies lvl } in
              insts := inst :: !insts;
              inst
            end
            else { gen; copies }
          in
          (ty, AInst (name, inst))
      | None -> err ("identifier not found: " ^ name))
  | Rcd fs ->
      let fs = List.map (fun (n, t) -> (n, type_term_ann ctx lvl t)) fs in
      (* a record literal has exactly its fields: its type is closed *)
      ( Record (List.map (fun (n, (ty, _)) -> (n, ty)) fs, Nil),
        ARcd (List.map (fun (n, (_, a)) -> (n, a)) fs) )
  | Lam (name, body) ->
      let param = fresh_var lvl in
      let ty, a = type_term_ann (StringMap.add name (Simple param) ctx) lvl body in
      (Function (param, ty), ALam (name, param, a))
  | App (f, a) ->
      let res = fresh_var lvl in
      let f_ty, f_ann = type_term_ann ctx lvl f in
      let a_ty, a_ann = type_term_ann ctx lvl a in
      constrain f_ty (Function (a_ty, res));
      (res, AApp (f_ann, a_ann, res))
  | Sel (obj, name) ->
      let res = fresh_var lvl in
      let obj_ty, obj_ann = type_term_ann ctx lvl obj in
      constrain obj_ty (Record ([ (name, res) ], Abs));
      (res, ASel (obj_ann, name, res))
  | SelOr (obj, name, default) ->
      (* [obj.name ?? default]: the field may be missing, and [default] is
         only evaluated when it is *)
      let res = fresh_var lvl in
      let obj_ty, obj_ann = type_term_ann ctx lvl obj in
      constrain obj_ty (Record ([ (name, Opt res) ], Abs));
      let d_ty, d_ann = type_term_ann ctx lvl default in
      constrain d_ty res;
      (res, ASelOr (obj_ann, name, d_ann, res))
  | Ext (obj, fs) ->
      (* [obj with {l = e, ...}] overwrites or adds the fields: [obj] may have
         anything at the labels, and its other fields are carried by [rho] *)
      let obj_ty, obj_ann = type_term_ann ctx lvl obj in
      let typed = List.map (fun (n, t) -> (n, type_term_ann ctx lvl t)) fs in
      let anns = List.map (fun (n, (_, a)) -> (n, a)) typed in
      let fs = List.map (fun (n, (ty, _)) -> (n, ty)) typed in
      (* the labels are distinct (the parser checks) *)
      if fs = [] then (obj_ty, AExt (obj_ann, anns, Abs)) (* [obj with {}] is just [obj] *)
      else begin
        (* [rho] stands for the other fields: it lacks the extended labels *)
        let rho = fresh_var ~kind:(SSet.of_list (List.map fst fs)) lvl in
        constrain obj_ty (Record (List.map (fun (n, _) -> (n, Abs)) fs, rho));
        (Record (fs, rho), AExt (obj_ann, anns, rho))
      end
  | Fn (ps, body) ->
      (* each default is typed in the scope of the parameters before it and
         flows into its parameter's type, as an argument would *)
      let ctx', params =
        List.fold_left
          (fun (ctx', acc) (p : param) ->
            let ty = fresh_var lvl in
            let d =
              Option.map
                (fun d ->
                  let d_ty, d_ann = type_term_ann ctx' lvl d in
                  constrain d_ty ty;
                  d_ann)
                p.default
            in
            (StringMap.add p.name (Simple ty) ctx', (p, ty, d) :: acc))
          (ctx, []) ps
      in
      let params = List.rev params in
      let body_ty, body_ann = type_term_ann ctx' lvl body in
      let sg =
        Sig
          (List.map
             (fun ((p : param), ty, d) ->
               { sname = p.name; skind = p.kind; sty = ty; sopt = d <> None })
             params)
      in
      ( Function (sg, body_ty),
        AFn (List.map (fun ((p : param), ty, d) -> (p.name, p.kind, ty, d)) params, body_ann) )
  | If (c, a, b) ->
      (* the condition is a boolean, and both branches flow into the result *)
      let res = fresh_var lvl in
      let c_ty, c_ann = type_term_ann ctx lvl c in
      constrain c_ty (Primitive "bool");
      let a_ty, a_ann = type_term_ann ctx lvl a in
      constrain a_ty res;
      let b_ty, b_ann = type_term_ann ctx lvl b in
      constrain b_ty res;
      (res, AIf (c_ann, a_ann, b_ann, res))
  | Let (isrec, name, rhs, body) ->
      let sch, la = type_let_rhs_ann ctx lvl isrec name rhs in
      let ty, body_ann = type_term_ann (StringMap.add name sch ctx) lvl body in
      ( ty,
        match la.rec_ty with
        | None -> ALet (name, la.gen, la.rhs, body_ann)
        | Some t -> ALetRec (name, la.gen, t, la.rhs, body_ann) )

(** Type the right-hand side of a (possibly recursive) let binding at level
    [lvl + 1] and generalize it. Shared by local and top-level lets.

    The language is eagerly evaluated, so [let rec x = s] evaluates [s]
    once, before [x] exists: [s] must be a function, whose body only runs
    (and reads [x]) once it is called. Cyclic data such as
    [let rec ones = {head = 1; tail = ones}] is rejected. *)
and type_let_rhs_ann ctx lvl isrec name rhs : type_scheme * let_ann =
  (match rhs with
  | Lam _ | Fn _ -> ()
  | _ when isrec ->
      err (Printf.sprintf "let rec %s: the right-hand side must be a function" name)
  | _ -> ());
  let before = !counter in
  let rhs_ty, rec_ty, rhs_ann =
    if isrec then begin
      let exp = fresh_var (lvl + 1) in
      let inf, a = type_term_ann (StringMap.add name (Simple exp) ctx) (lvl + 1) rhs in
      constrain inf exp;
      (exp, Some exp, a)
    end
    else
      let ty, a = type_term_ann ctx (lvl + 1) rhs in
      (ty, None, a)
  in
  let sch = Poly (lvl, rhs_ty) in
  let gen = created_above before lvl in
  gens := (sch, gen) :: !gens;
  (sch, { gen; rec_ty; rhs = rhs_ann })

let type_term ctx lvl trm = fst (type_term_ann ctx lvl trm)
let type_let_rhs ctx lvl isrec name rhs = fst (type_let_rhs_ann ctx lvl isrec name rhs)

(** {1 Built-ins} *)

let bool_t = Primitive "bool"
let int_t = Primitive "int"

(** Initial context. [if c then a else b] is a term of its own ({!Syntax.If}),
    not a function: only the chosen branch is evaluated. *)
let builtins () : ctx =
  (* positional-only parameters, under names source code cannot write *)
  let call ts r =
    Function
      ( Sig (List.mapi (fun i t -> { sname = "#" ^ string_of_int i; skind = PosOnly; sty = t; sopt = false }) ts),
        r )
  in
  StringMap.of_seq
    (List.to_seq
       [
         ("true", Simple bool_t);
         ("false", Simple bool_t);
         ("not", Simple (call [ bool_t ] bool_t));
         ("succ", Simple (call [ int_t ] int_t));
         ("add", Simple (call [ int_t; int_t ] int_t));
       ])
