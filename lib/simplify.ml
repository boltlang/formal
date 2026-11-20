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

(** What a compact type at field or row sort says besides its parts
    (variables, primitives, records, function). "Missing" is the field
    [Missing] at field sort and the empty row at row sort. *)
type pres =
  | P  (** only the parts: a type, a present field, a row *)
  | M  (** missing; there are no parts *)
  | O
      (** positive: the parts ∨ missing, which at field sort is [Opt] of the
          parts; negative, a field: [Opt] of the parts *)
  | PM  (** negative only: the parts ∧ missing *)
  | A  (** [Abs], the top field or the top row; there are no parts *)

(** A normalized type: a union (positive) or intersection (negative) of type
    variables, primitives, records and at most one function.

    The same representation is used at field sort and at row sort (in a row
    tail: [vars] are row variables and [rows] nested rows), where [pres]
    adds the field lattice [Pre τ ≤ Opt τ], [Missing ≤ Opt τ], [Opt τ ≤ Abs]
    and the rows [Nil ≤ Abs]. Following Simple-sub's conventions, an empty
    compact type means ⊥ in positive and ⊤ in negative position; at row
    sort, ⊤ is [Abs].

    [rows] is a list because two rows can only be merged without losing
    equivalence when every label missing from one row is known in it, which
    holds when that row ends in [Abs] (the label is then [Abs]) or in [Nil]
    (it is [Missing]). In [{x: τ | ρ₀} ∨ { | ρ₁}], the type of [x] on the
    right is inside [ρ₁]. *)
type compact = {
  vars : ISet.t;
  prims : SSet.t;
  rows : row list;
  fn : (compact * compact) option;
  sigs : cparam list list;
      (** parameter lists (as a function domain); each stands for a union of
          argument records, so they are never merged with [rows] or with
          each other *)
  pres : pres;
}

and row = { fields : compact SMap.t; tail : compact }

and cparam = { cname : string; ckind : Types.pkind; cty : compact; copt : bool }

(** [rec_vars] holds the bounds of recursive variables, which cannot be
    inlined since they are cyclic.

    [rank] orders variables by first appearance in a left-to-right walk of
    the inferred type and its bounds (see {!compact_type}). Simplification
    and printing follow this order rather than variable ids, which only
    reflect allocation order inside the type checker. This makes the output
    depend on the shape of the inferred type alone. *)
type scheme = {
  term : compact;
  rec_vars : compact IMap.t;
  rank : int IMap.t;
  kinds : Types.SSet.t IMap.t;
      (** the kind of each (row) variable; merging variables of different
          kinds would produce an ill-kinded type *)
}

let empty =
  { vars = ISet.empty; prims = SSet.empty; rows = []; fn = None; sigs = []; pres = P }

let of_var v = { empty with vars = ISet.singleton v }
let abs_c = { empty with pres = A }
let mis_c = { empty with pres = M }

let has_parts c =
  not (ISet.is_empty c.vars && SSet.is_empty c.prims && c.rows = [] && c.fn = None && c.sigs = [])

let is_empty c = c.pres = P && not (has_parts c)
let is_abs_only c = c.pres = A && not (has_parts c)
let is_mis_only c = c.pres = M && not (has_parts c)

(** A row tail that is the empty row. Removing variables can leave
    "the parts ∨ missing" or "the parts ∧ missing" without parts. *)
let is_nil_tail c = (not (has_parts c)) && (c.pres = M || c.pres = O || c.pres = PM)

(** Build a row, flattening a tail that is itself a single row, and dropping
    the fields that say nothing more than the tail: [Abs] fields when the
    tail is [Abs], [Missing] fields when it is the empty row. *)
let rec mk_row fields tail =
  match tail with
  | { rows = [ r ]; _ } when is_empty { tail with rows = [] } ->
      mk_row (SMap.union (fun _ outer _ -> Some outer) fields r.fields) r.tail
  | _ ->
      let fields =
        if is_abs_only tail then SMap.filter (fun _ f -> not (is_abs_only f)) fields
        else if is_nil_tail tail then SMap.filter (fun _ f -> not (is_mis_only f)) fields
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
        let c = compare a.pres b.pres in
        if c <> 0 then c
        else
          let c = List.compare compare_sig a.sigs b.sigs in
          if c <> 0 then c
          else
          Option.compare
            (fun (l0, r0) (l1, r1) ->
              let c = compare_compact l0 l1 in
              if c <> 0 then c else compare_compact r0 r1)
            a.fn b.fn

and compare_sig a b =
  List.compare
    (fun p q ->
      let c = compare (p.cname, p.ckind, p.copt) (q.cname, q.ckind, q.copt) in
      if c <> 0 then c else compare_compact p.cty q.cty)
    a b

and compare_row a b =
  let c = SMap.compare compare_compact a.fields b.fields in
  if c <> 0 then c else compare_compact a.tail b.tail

let merge_opt f a b =
  match (a, b) with
  | Some x, Some y -> Some (f x y)
  | Some _, None -> a
  | None, _ -> b

(** Union ([pol = true]) or intersection ([pol = false]) of compact types.
    An empty compact type is the neutral element. Rows merge field by field
    (a label missing from a row ending in [Abs] is [Abs], from one ending in
    [Nil] it is [Missing]). Function types merge contravariantly in the
    parameter: [(a -> b) ∨ (c -> d) = (a ∧ c) -> (b ∨ d)].

    At field and row sort, with [M] for missing and [τ], [σ] for the parts:
    {v
    τ ∨ M     = Opt τ          Opt τ ∧ σ     = τ ∧ σ
    Opt τ ∨ σ = Opt (τ ∨ σ)    Opt τ ∧ Opt σ = Opt (τ ∧ σ)
    θ ∨ Abs   = Abs            Opt τ ∧ M     = M
                               θ ∧ Abs       = θ
    v}
    [τ ∧ M] is kept as it is: for a field it is ⊥, which a negative compact
    type cannot say; for a row it is the row [τ] with the empty row as a
    further bound. *)
let rec merge pol a b =
  if is_empty a then b
  else if is_empty b then a
  else
    let parts pres =
      {
        vars = ISet.union a.vars b.vars;
        prims = SSet.union a.prims b.prims;
        rows = List.fold_left (add_row pol) a.rows b.rows;
        fn =
          merge_opt
            (fun (l0, r0) (l1, r1) -> (merge (not pol) l0 l1, merge pol r0 r1))
            a.fn b.fn;
        sigs =
          List.fold_left
            (fun acc g -> if List.exists (fun h -> compare_sig g h = 0) acc then acc else acc @ [ g ])
            a.sigs b.sigs;
        pres;
      }
    in
    match (pol, a.pres, b.pres) with
    | true, A, _ | true, _, A -> abs_c
    | false, A, _ -> b
    | false, _, A -> a
    | _, P, P -> parts P
    | _, M, M -> mis_c
    | true, _, _ -> parts O
    | false, O, O -> parts O
    | false, (P | O), (P | O) -> parts P
    | false, M, O | false, O, M -> mis_c
    | false, _, _ -> parts PM

(** The length of a list compact type ([{hd; tl}] cells ending in [{}]),
    if it is one. *)
and list_len c =
  match c with
  | { rows = [ r ]; _ } when is_empty { c with rows = [] } ->
      if SMap.is_empty r.fields && is_nil_tail r.tail then Some 0
      else if SMap.cardinal r.fields = 2 && is_nil_tail r.tail then
        Option.bind (SMap.find_opt "tl" r.fields) (fun tl ->
            if SMap.mem "hd" r.fields then Option.map succ (list_len tl) else None)
      else None
  | _ -> None

(** Argument records stand apart unless they pass the same number of
    positional arguments: a signature picks the record [Dₖ] to compare an
    argument with by that number, so a join of records with different
    numbers is not a record a signature can take. For a fixed number the
    comparison is field by field, and merging is exact. *)
and same_spine r0 r1 =
  match (SMap.find_opt Types.args_label r0.fields, SMap.find_opt Types.args_label r1.fields) with
  | None, None -> true
  | Some l0, Some l1 -> (
      match (list_len l0, list_len l1) with Some a, Some b -> a = b | _ -> false)
  | _ -> false

and add_row pol rows r =
  let labels r = List.map fst (SMap.bindings r.fields) in
  (* the field of a label a row does not list, when its tail tells *)
  let unlisted r =
    if is_abs_only r.tail then Some abs_c
    else if is_mis_only r.tail then Some mis_c
    else None
  in
  let covers a b =
    (* every label of [b] is known in [a] *)
    Option.is_some (unlisted a) || List.for_all (fun n -> SMap.mem n a.fields) (labels b)
  in
  (* an empty row and a row with variables stay apart: merged, the tail
     would be "ρ ∨ {}" or "ρ ∧ {}", which reads worse than two records *)
  let apart a b = is_nil_tail a.tail && has_parts b.tail in
  let mergeable r0 =
    covers r0 r && covers r r0 && (not (apart r0 r || apart r r0)) && same_spine r0 r
  in
  match List.find_opt mergeable rows with
  | Some r0 ->
      (* merge into the first compatible row, keeping the others in place *)
      let field r n =
        match SMap.find_opt n r.fields with
        | Some f -> f
        | None -> Option.value ~default:abs_c (unlisted r)
      in
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
  let kinds = ref IMap.empty in
  let see ?(kind = Types.SSet.empty) v =
    if not (IMap.mem v !rank) then rank := IMap.add v (IMap.cardinal !rank) !rank;
    if not (Types.SSet.is_empty kind) then kinds := IMap.add v kind !kinds
  in
  let rec go ty pol parents in_process =
    match ty with
    | Primitive n -> { empty with prims = SSet.singleton n }
    | Function (l, r) ->
        let l = go l (not pol) ISet.empty in_process in
        { empty with fn = Some (l, go r pol ISet.empty in_process) }
    | Abs -> abs_c
    | Missing | Nil -> mis_c
    | Opt t -> { (go t pol ISet.empty in_process) with pres = O }
    | Sig ps ->
        let param (p : Types.sparam) =
          { cname = p.sname; ckind = p.skind; cty = go p.sty pol ISet.empty in_process; copt = p.sopt }
        in
        { empty with sigs = [ List.map param ps ] }
    | Record (fs, t) ->
        let fields =
          List.fold_left
            (fun m (n, f) -> SMap.add n (go f pol ISet.empty in_process) m)
            SMap.empty fs
        in
        (* the tail continues the same row: no constructor in between *)
        { empty with rows = [ mk_row fields (go t pol parents in_process) ] }
    | Variable vs ->
        see ~kind:vs.kind vs.id;
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
                  see ~kind:vs.kind v;
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
  { term; rec_vars = !rec_vars; rank = !rank; kinds = !kinds }

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
  let kind_of v = Option.value ~default:Types.SSet.empty (IMap.find_opt v sch.kinds) in
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
      t.fn;
    List.iter (List.iter (fun p -> analyze pol p.cty)) t.sigs
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
                          the latter need not be strictly polar *)
                       && Types.SSet.equal (kind_of v) (kind_of w)
                       (* nor variables of different kinds *) ->
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
      sigs = List.map (List.map (fun p -> { p with cty = go p.cty })) t.sigs;
      pres = t.pres;
    }
  in
  { sch with term = go sch.term; rec_vars = IMap.map go !rec_vars }

(** {1 CompactTypeScheme -> Type, with hash consing (Sec. 4.3.2)}

    Besides recursive variables, whole compact types are remembered while
    they are being coalesced; meeting one again (necessarily by unfolding a
    recursive variable) ties the knot there, which removes redundant outer
    layers such as in [α -> {L: α, R: μβ.{L: α, R: β}}]. *)

(** The sort a compact type is read at: it decides what [pres] means. *)
type sort = Ty | Fld | Row

type key = KVar of int | KType of sort * compact

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
      | KType (s0, a), KType (s1, b) ->
          let c = compare s0 s1 in
          if c <> 0 then c else compare_compact a b
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
  let rec go_var sort v pol in_process =
    match IMap.find_opt v sch.rec_vars with
    | None -> TypeVariable (var_name v)
    | Some b -> enter (KVar v) pol in_process (fun ip -> go sort b pol ip)
  and go sort t pol in_process =
    let mrg a b = if pol then Union (a, b) else Inter (a, b) in
    let parts = { t with pres = P } in
    match (sort, t.pres) with
    | _, A -> AbsType
    | Fld, M -> MissingType
    | Row, M -> NilType
    (* an empty negative tail is the top row: the record is open *)
    | Row, P when (not pol) && is_empty t -> AbsType
    | Fld, O ->
        (* positive, without parts: ⊥ ∨ Missing *)
        if pol && not (has_parts t) then MissingType
        else Optional (go Ty parts pol in_process)
    | Fld, PM -> Inter (go Ty parts pol in_process, MissingType)
    | Row, (O | PM) ->
        if has_parts t then mrg (go Row parts pol in_process) NilType else NilType
    | _ -> go_parts sort parts pol in_process
  and go_parts sort t pol in_process =
    (* a present field is a type: the same knot *)
    let sort = if sort = Fld then Ty else sort in
    enter (KType (sort, t)) pol in_process (fun ip ->
        let parts =
          List.map (fun v -> go_var sort v pol ip) (ordered sch t.vars)
          @ List.map (fun p -> PrimitiveType p) (SSet.elements t.prims)
          @ List.map
              (fun r ->
                let fs = List.map (fun (n, f) -> (n, go Fld f pol ip)) (SMap.bindings r.fields) in
                let tail = go Row r.tail pol ip in
                (* a field that says no more than the tail is left out *)
                let fs =
                  match tail with
                  | AbsType -> List.filter (fun (_, f) -> f <> AbsType) fs
                  | NilType -> List.filter (fun (_, f) -> f <> MissingType) fs
                  | _ -> fs
                in
                RecordType (fs, tail))
              t.rows
          @ List.map
              (fun g ->
                SigType
                  (List.map
                     (fun p -> { tname = p.cname; tkind = p.ckind; tty = go Ty p.cty pol ip; topt = p.copt })
                     g))
              t.sigs
          @ (match t.fn with
             | Some (l, r) ->
                 let l = go Ty l (not pol) ip in
                 [ FunctionType (l, go Ty r pol ip) ]
             | None -> [])
        in
        match parts with
        | [] -> if pol then Bot else Top
        | p :: ps ->
            List.fold_left (fun a b -> if pol then Union (a, b) else Inter (a, b)) p ps)
  in
  go Ty sch.term true KeyMap.empty

(** Full pipeline. *)
let simplify_type (ty : simple_type) : typ =
  coalesce_compact (simplify (compact_type ty))
