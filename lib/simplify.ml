(** Type simplification (paper, Sec. 4).

    Pipeline: [compact_type] (SimpleType -> CompactTypeScheme), then
    [simplify] (co-occurrence analysis + rewriting), then [coalesce_compact]
    (CompactTypeScheme -> user-facing type, with hash consing).

    The paper describes these steps but defers the code to its artifact; this
    is a re-implementation from that description. *)

open Types

module ISet = Set.Make (Int)
module IMap = Map.Make (Int)
module SSet = Set.Make (String)
module SMap = Map.Make (String)

(** {1 Compact types (Sec. 4.4)} *)

(** A normalized type: a union (positive) or intersection (negative) of type
    variables, primitives, records, at most one function, and possibly [Abs].

    The same representation is used at field sort ([abs] = the absent field)
    and at row sort (in a row tail: [vars] are row variables, [rows] nested
    rows, and [abs] the top row). Following Simple-sub's conventions, an empty
    compact type means ⊥ in positive and ⊤ in negative position; at row
    sort, ⊤ is [Abs].

    [rows] is a list because two rows can only be merged without losing
    equivalence when every label missing from one row is known in it, which
    holds when that row ends in [Abs] (the label is then [Abs]). In
    [{x: τ | ρ₀} ∨ { | ρ₁}], the type of [x] on the right is inside [ρ₁]. *)
type compact = {
  vars : ISet.t;
  prims : SSet.t;
  rows : row list;
  fn : (compact * compact) option;
  abs : bool;
}

and row = { fields : compact SMap.t; tail : compact }

(** [rec_vars] holds the bounds of recursive variables, which cannot be
    inlined since they are cyclic.

    [rank] orders variables by first appearance in a left-to-right walk of
    the inferred type and its bounds (see {!compact_type}). Simplification
    and printing follow this order rather than variable ids, which only
    reflect allocation order inside the type checker. This makes the output
    depend on the shape of the inferred type alone. *)
type scheme = { term : compact; rec_vars : compact IMap.t; rank : int IMap.t }

let empty =
  { vars = ISet.empty; prims = SSet.empty; rows = []; fn = None; abs = false }

let of_var v = { empty with vars = ISet.singleton v }
let abs_c = { empty with abs = true }

let is_empty c =
  ISet.is_empty c.vars && SSet.is_empty c.prims && c.rows = [] && c.fn = None
  && not c.abs

let is_abs_only c = c.abs && is_empty { c with abs = false }

(** [Abs] is absorbing in unions and neutral in (non-empty) intersections. *)
let normalize pol c =
  if not c.abs then c
  else if pol then abs_c
  else
    let c' = { c with abs = false } in
    if is_empty c' then c else c'

(** Build a row, flattening a tail that is itself a single row, and dropping
    [Abs] fields when the tail is [Abs] (they say nothing more). *)
let rec mk_row fields tail =
  match tail with
  | { rows = [ r ]; _ } when is_empty { tail with rows = [] } ->
      mk_row (SMap.union (fun _ outer _ -> Some outer) fields r.fields) r.tail
  | _ ->
      let fields =
        if is_abs_only tail then SMap.filter (fun _ f -> not (is_abs_only f)) fields
        else fields
      in
      { fields; tail }

(* Sets and maps are balanced trees, so polymorphic [compare] is unreliable
   on them; compare canonically instead. *)
let rec compare_compact a b =
  let c = ISet.compare a.vars b.vars in
  if c <> 0 then c
  else
    let c = SSet.compare a.prims b.prims in
    if c <> 0 then c
    else
      let c = List.compare compare_row a.rows b.rows in
      if c <> 0 then c
      else
        let c = Bool.compare a.abs b.abs in
        if c <> 0 then c
        else
          Option.compare
            (fun (l0, r0) (l1, r1) ->
              let c = compare_compact l0 l1 in
              if c <> 0 then c else compare_compact r0 r1)
            a.fn b.fn

and compare_row a b =
  let c = SMap.compare compare_compact a.fields b.fields in
  if c <> 0 then c else compare_compact a.tail b.tail

let merge_opt f a b =
  match (a, b) with
  | Some x, Some y -> Some (f x y)
  | Some _, None -> a
  | None, _ -> b

(** Union ([pol = true]) or intersection ([pol = false]) of compact types.
    Rows merge field by field (a label missing from a row ending in [Abs] is
    [Abs]); since [Abs] is the top field, a union of records keeps the common
    fields and an intersection keeps all, as before. Function types merge
    contravariantly in the parameter: [(a -> b) ∨ (c -> d) = (a ∧ c) -> (b ∨ d)]. *)
let rec merge pol a b =
  normalize pol
    {
      vars = ISet.union a.vars b.vars;
      prims = SSet.union a.prims b.prims;
      rows = List.fold_left (add_row pol) a.rows b.rows;
      fn =
        merge_opt
          (fun (l0, r0) (l1, r1) -> (merge (not pol) l0 l1, merge pol r0 r1))
          a.fn b.fn;
      abs = a.abs || b.abs;
    }

and add_row pol rows r =
  let labels r = List.map fst (SMap.bindings r.fields) in
  let covers a b =
    (* every label of [b] is known in [a] *)
    is_abs_only a.tail || List.for_all (fun n -> SMap.mem n a.fields) (labels b)
  in
  let mergeable r0 = covers r0 r && covers r r0 in
  match List.find_opt mergeable rows with
  | Some r0 ->
      (* merge into the first compatible row, keeping the others in place *)
      let field r n = Option.value ~default:abs_c (SMap.find_opt n r.fields) in
      let names = SSet.of_list (labels r0 @ labels r) in
      let fields =
        SSet.fold (fun n m -> SMap.add n (merge pol (field r0 n) (field r n)) m) names SMap.empty
      in
      let merged = mk_row fields (merge pol r0.tail r.tail) in
      List.map (fun x -> if x == r0 then merged else x) rows
  | None -> rows @ [ r ]

(** {1 SimpleType -> CompactTypeScheme}

    Like [Coalesce.coalesce_type], but merges bounds into compact types.
    [parents] tracks the variables traversed since the last type
    constructor: reaching one of them again is an unguarded cycle such as
    [α ≤ β ≤ α], which contributes nothing and is dropped. *)
let compact_type (ty : simple_type) : scheme =
  let recursive : (int * bool, int) Hashtbl.t = Hashtbl.create 16 in
  let rec_vars = ref IMap.empty in
  let rank = ref IMap.empty in
  let see v =
    if not (IMap.mem v !rank) then rank := IMap.add v (IMap.cardinal !rank) !rank
  in
  let rec go ty pol parents in_process =
    match ty with
    | Primitive n -> { empty with prims = SSet.singleton n }
    | Function (l, r) ->
        let l = go l (not pol) ISet.empty in_process in
        { empty with fn = Some (l, go r pol ISet.empty in_process) }
    | Abs -> abs_c
    | Record (fs, t) ->
        let fields =
          List.fold_left
            (fun m (n, f) -> SMap.add n (go f pol ISet.empty in_process) m)
            SMap.empty fs
        in
        (* the tail continues the same row: no constructor in between *)
        { empty with rows = [ mk_row fields (go t pol parents in_process) ] }
    | Variable vs ->
        see vs.id;
        let key = (vs.id, pol) in
        if List.mem key in_process then
          if ISet.mem vs.id parents then empty
          else
            let v =
              match Hashtbl.find_opt recursive key with
              | Some v -> v
              | None ->
                  let v = fresh_id () in
                  Hashtbl.add recursive key v;
                  see v;
                  v
            in
            of_var v
        else
          let bounds = if pol then vs.lower_bounds else vs.upper_bounds in
          let parents = ISet.add vs.id parents in
          let in_process = key :: in_process in
          let bound =
            List.fold_left
              (fun acc b -> merge pol acc (go b pol parents in_process))
              (of_var vs.id) bounds
          in
          (match Hashtbl.find_opt recursive key with
           | Some v ->
               rec_vars := IMap.add v bound !rec_vars;
               of_var v
           | None -> bound)
  in
  let term = go ty true ISet.empty [] in
  { term; rec_vars = !rec_vars; rank = !rank }

let rank_of sch v = Option.value ~default:max_int (IMap.find_opt v sch.rank)

(** Variables of [s] in canonical order. *)
let ordered sch (s : ISet.t) =
  List.stable_sort
    (fun a b -> Int.compare (rank_of sch a) (rank_of sch b))
    (ISet.elements s)

(** {1 Simplification (Sec. 4.3.1)} *)

type atom = AVar of int | APrim of string

module ASet = Set.Make (struct
  type t = atom

  let compare = compare
end)

let atoms_of (t : compact) =
  ASet.union
    (ASet.of_seq (Seq.map (fun v -> AVar v) (ISet.to_seq t.vars)))
    (ASet.of_seq (Seq.map (fun p -> APrim p) (SSet.to_seq t.prims)))

let simplify (sch : scheme) : scheme =
  let rec_vars = ref sch.rec_vars in
  let is_rec v = IMap.mem v !rec_vars in
  let all_vars = ref (ISet.of_seq (Seq.map fst (IMap.to_seq sch.rec_vars))) in
  (* (pol, v) -> atoms that occur alongside v in *every* pol occurrence *)
  let cooc : (bool * int, ASet.t) Hashtbl.t = Hashtbl.create 16 in
  let analyzed : (bool * int, unit) Hashtbl.t = Hashtbl.create 16 in
  let rec analyze pol t =
    let here = atoms_of t in
    ISet.iter
      (fun v ->
        all_vars := ISet.add v !all_vars;
        (match Hashtbl.find_opt cooc (pol, v) with
         | Some os -> Hashtbl.replace cooc (pol, v) (ASet.inter os here)
         | None -> Hashtbl.replace cooc (pol, v) here);
        if not (Hashtbl.mem analyzed (pol, v)) then begin
          Hashtbl.add analyzed (pol, v) ();
          Option.iter (analyze pol) (IMap.find_opt v !rec_vars)
        end)
      t.vars;
    List.iter
      (fun r ->
        SMap.iter (fun _ f -> analyze pol f) r.fields;
        analyze pol r.tail)
      t.rows;
    Option.iter
      (fun (l, r) ->
        analyze (not pol) l;
        analyze pol r)
      t.fn
  in
  analyze true sch.term;
  (* v -> Some w: replace v with w; v -> None: remove v *)
  let subst : (int, int option) Hashtbl.t = Hashtbl.create 16 in
  let vars_in_order = ordered sch !all_vars in
  (* candidates in canonical order: variables by rank, then primitives *)
  let ordered_atoms occs =
    let vs = ASet.fold (fun a acc -> match a with AVar v -> ISet.add v acc | APrim _ -> acc) occs ISet.empty in
    List.map (fun v -> AVar v) (ordered sch vs)
    @ List.filter (function APrim _ -> true | AVar _ -> false) (ASet.elements occs)
  in
  (* 1. Remove non-recursive variables occurring in only one polarity. *)
  List.iter
    (fun v ->
      if not (is_rec v) then
        match (Hashtbl.mem cooc (true, v), Hashtbl.mem cooc (false, v)) with
        | true, false | false, true -> Hashtbl.replace subst v None
        | _ -> ())
    vars_in_order;
  (* 2. Unify indistinguishable variables, and 3. flatten sandwiches.

     These rewrites do not commute: merging two variables changes the
     co-occurrences of the survivor, which can block another merge (e.g. in
     [twice], merging the positive pair blocks the negative one and vice
     versa). We fix a canonical order: one pass over all variables for
     negative co-occurrences, then one for positive ones, each in rank
     order. Negative-first reproduces the paper's choice for [twice],
     [(β ∨ γ → γ) → β → γ] (Sec. 3.4.2). *)
  List.iter
    (fun pol ->
      List.iter
        (fun v ->
          let occs =
            Option.value ~default:ASet.empty (Hashtbl.find_opt cooc (pol, v))
          in
          List.iter
            (fun a ->
              if not (Hashtbl.mem subst v) then
                match a with
                | AVar w
                  when w <> v
                       && (not (Hashtbl.mem subst w))
                       && is_rec v = is_rec w
                       (* do not merge recursive with non-recursive variables:
                          the latter need not be strictly polar *) ->
                    let w_occs = Hashtbl.find_opt cooc (pol, w) in
                    if Option.fold ~none:true ~some:(ASet.mem (AVar v)) w_occs
                    then begin
                      (* v and w always occur together at polarity pol *)
                      Hashtbl.replace subst w (Some v);
                      match IMap.find_opt w !rec_vars with
                      | Some b_w ->
                          let b_v = IMap.find v !rec_vars in
                          rec_vars :=
                            IMap.add v (merge pol b_v b_w)
                              (IMap.remove w !rec_vars)
                      | None -> (
                          (* v now stands for w at the opposite polarity too *)
                          let w_opp =
                            Option.value ~default:ASet.empty
                              (Hashtbl.find_opt cooc (not pol, w))
                          in
                          match Hashtbl.find_opt cooc (not pol, v) with
                          | Some v_opp ->
                              Hashtbl.replace cooc (not pol, v)
                                (ASet.filter
                                   (fun t -> t = AVar v || ASet.mem t w_opp)
                                   v_opp)
                          | None -> ())
                    end
                | APrim _
                  when (not (is_rec v))
                       && Option.fold ~none:false ~some:(ASet.mem a)
                            (Hashtbl.find_opt cooc (not pol, v)) ->
                    (* v is sandwiched: a ≤ v ≤ a, so v ≡ a *)
                    Hashtbl.replace subst v None
                | _ -> ())
            (ordered_atoms occs))
        vars_in_order)
    [ false; true ];
  let rec resolve v =
    match Hashtbl.find_opt subst v with
    | None -> Some v
    | Some None -> None
    | Some (Some w) -> resolve w
  in
  let rec go t =
    {
      vars = ISet.filter_map resolve t.vars;
      prims = t.prims;
      rows = List.map (fun r -> mk_row (SMap.map go r.fields) (go r.tail)) t.rows;
      fn = Option.map (fun (l, r) -> (go l, go r)) t.fn;
      abs = t.abs;
    }
  in
  { sch with term = go sch.term; rec_vars = IMap.map go !rec_vars }

(** {1 CompactTypeScheme -> Type, with hash consing (Sec. 4.3.2)}

    Besides recursive variables, whole compact types are remembered while
    they are being coalesced; meeting one again (necessarily by unfolding a
    recursive variable) ties the knot there, which removes redundant outer
    layers such as in [α -> {L: α, R: μβ.{L: α, R: β}}]. *)

type key = KVar of int | KType of compact

module KeyMap = Map.Make (struct
  type t = key * bool

  let compare (k0, p0) (k1, p1) =
    let c = Bool.compare p0 p1 in
    if c <> 0 then c
    else
      match (k0, k1) with
      | KVar a, KVar b -> Int.compare a b
      | KVar _, KType _ -> -1
      | KType _, KVar _ -> 1
      | KType a, KType b -> compare_compact a b
end)

let var_name v = "α" ^ string_of_int v

let coalesce_compact (sch : scheme) : typ =
  (* in-process entries: the name to refer back to it, and whether we did *)
  let enter key pol in_process k =
    match KeyMap.find_opt (key, pol) in_process with
    | Some (name, used) ->
        used := true;
        TypeVariable name
    | None ->
        let name = var_name (fresh_id ()) and used = ref false in
        let res = k (KeyMap.add (key, pol) (name, used) in_process) in
        if !used then RecursiveType (name, res) else res
  in
  let rec go_var v pol in_process =
    match IMap.find_opt v sch.rec_vars with
    | None -> TypeVariable (var_name v)
    | Some b -> enter (KVar v) pol in_process (fun ip -> go b pol ip)
  and go t pol in_process =
    enter (KType t) pol in_process (fun ip ->
        let parts =
          List.map (fun v -> go_var v pol ip) (ordered sch t.vars)
          @ List.map (fun p -> PrimitiveType p) (SSet.elements t.prims)
          @ List.map
              (fun r ->
                let fs = List.map (fun (n, f) -> (n, go f pol ip)) (SMap.bindings r.fields) in
                let tail = go_tail r.tail pol ip in
                (* without a row tail, an Abs field says nothing *)
                let fs = if tail = Absent then List.filter (fun (_, f) -> f <> Absent) fs else fs in
                RecordType (fs, tail))
              t.rows
          @ (match t.fn with
             | Some (l, r) ->
                 let l = go l (not pol) ip in
                 [ FunctionType (l, go r pol ip) ]
             | None -> [])
          @ if t.abs then [ Absent ] else []
        in
        match parts with
        | [] -> if pol then Bot else Top
        | p :: ps ->
            List.fold_left (fun a b -> if pol then Union (a, b) else Inter (a, b)) p ps)
  (* row tails: an empty negative tail is the top row, i.e. no row at all *)
  and go_tail t pol ip =
    if is_abs_only t || ((not pol) && is_empty t) then Absent else go t pol ip
  in
  go sch.term true KeyMap.empty

(** Full pipeline. *)
let simplify_type (ty : simple_type) : typ =
  coalesce_compact (simplify (compact_type ty))
