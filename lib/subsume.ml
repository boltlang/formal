(** Subsumption checking between user-facing type schemes.

    [subsumes s1 s2] decides [s1 ≤∀ s2]: the type variables of [s1] can be
    instantiated so that [s1] becomes a subtype of [s2], where the variables
    of [s2] are universally quantified (rigid). Intuitively, [s1] is at least
    as general as [s2]: a definition of type [s1] can be used wherever [s2] is
    expected. Equivalence is subsumption in both directions.

    Both types must be polar (unions only in positive positions,
    intersections only in negative ones), as MLsub-style inferred types
    always are. With [s1 ≤ s2], this guarantees that the only constraints
    involving a choice (an intersection on the left or a union on the right)
    come from [s2], which contains no flexible variables, so those choices
    never need to undo side effects.

    The subtyping rules are those of Fig. 10 of the paper, extended with
    the MLsub lattice equations used by simplification (Sec. 4.1): an
    intersection of functions [(a -> b) ∧ (c -> d)] is [a ∨ c -> b ∧ d], a
    union of records keeps the common fields, and [⋀X ≤ ⋁Y] holds iff some
    atom of [X] is below some atom of [Y]. *)

open Types

exception Not_polar of string

(** Type graph used during checking. Recursive types become cycles through
    [Ref] cells, so unfolding is dereferencing. *)
type node =
  | Flex of flex  (** instantiable variable of the left-hand scheme *)
  | Rigid of string  (** quantified variable of the right-hand scheme *)
  | Prim of string
  | Fun of node * node
  | Rcd of (string * node) list
  | Union of node list  (** [Union []] is ⊥ *)
  | Inter of node list  (** [Inter []] is ⊤ *)
  | Ref of node ref  (** recursive knot *)

and flex = {
  fid : int;
  mutable lbs : node list;
  mutable ubs : node list;
}

(** Convert a user-facing type into a graph. Free variables become [Flex]
    when [flexible], [Rigid] otherwise. *)
let to_node ~flexible (t : typ) : node =
  let vars : (string, node) Hashtbl.t = Hashtbl.create 8 in
  let var n =
    match Hashtbl.find_opt vars n with
    | Some v -> v
    | None ->
        let v =
          if flexible then Flex { fid = fresh_id (); lbs = []; ubs = [] }
          else Rigid n
        in
        Hashtbl.add vars n v;
        v
  in
  let rec go env pol t =
    match t with
    | Top -> Inter []
    | Bot -> Union []
    | Union (a, b) ->
        if not pol then raise (Not_polar "union in negative position");
        let a = go env pol a in
        Union [ a; go env pol b ]
    | Inter (a, b) ->
        if pol then raise (Not_polar "intersection in positive position");
        let a = go env pol a in
        Inter [ a; go env pol b ]
    | FunctionType (l, r) ->
        let l = go env (not pol) l in
        Fun (l, go env pol r)
    | RecordType fs -> Rcd (List.map (fun (n, f) -> (n, go env pol f)) fs)
    | PrimitiveType n -> Prim n
    | TypeVariable n -> (
        match List.assoc_opt n env with Some cell -> Ref cell | None -> var n)
    | RecursiveType (n, body) ->
        let cell = ref (Union []) in
        cell := go ((n, cell) :: env) pol body;
        Ref cell
  in
  go [] true t

(** Structural equality that does not unfold [Ref] cells (compared by
    identity), hence always terminates. Used for coinductive hypotheses. *)
let rec node_eq a b =
  a == b
  ||
  match (a, b) with
  | Flex x, Flex y -> x.fid = y.fid
  | Rigid x, Rigid y | Prim x, Prim y -> String.equal x y
  | Fun (a1, b1), Fun (a2, b2) -> node_eq a1 a2 && node_eq b1 b2
  | Rcd fs, Rcd gs ->
      List.equal (fun (n, t) (m, u) -> String.equal n m && node_eq t u) fs gs
  | Union xs, Union ys | Inter xs, Inter ys -> List.equal node_eq xs ys
  | Ref c1, Ref c2 -> c1 == c2
  | _ -> false

let mem_pair a b = List.exists (fun (x, y) -> node_eq x a && node_eq y b)

(** Flatten nested intersections (resp. unions), unfolding knots on the way.
    [seen] guards against unguarded cycles such as [μα. α ∧ int]. *)
let rec flatten ~inter seen n =
  match n with
  | Inter xs when inter -> List.concat_map (flatten ~inter seen) xs
  | Union xs when not inter -> List.concat_map (flatten ~inter seen) xs
  | Ref c -> if List.memq c seen then [] else flatten ~inter (c :: seen) !c
  | n -> [ n ]

type atoms = {
  rigids : string list;
  prims : string list;
  funs : (node * node) list;
  rcds : (string * node) list list;
  absorbing : bool;  (** contains ⊥ (in a meet) or ⊤ (in a join) *)
  others : node list;  (** flexible variables etc.: cannot be decided *)
}

let atoms ~inter n =
  List.fold_right
    (fun a acc ->
      match a with
      | Rigid v -> { acc with rigids = v :: acc.rigids }
      | Prim p -> { acc with prims = p :: acc.prims }
      | Fun (l, r) -> { acc with funs = (l, r) :: acc.funs }
      | Rcd fs -> { acc with rcds = fs :: acc.rcds }
      | Union [] when inter -> { acc with absorbing = true }
      | Inter [] when not inter -> { acc with absorbing = true }
      | other -> { acc with others = other :: acc.others })
    (flatten ~inter [] n)
    { rigids = []; prims = []; funs = []; rcds = []; absorbing = false; others = [] }

(** Merge the function atoms of a meet ([inter]) or join. *)
let merge_funs ~inter = function
  | [] -> None
  | [ f ] -> Some f
  | fs ->
      let ps = List.map fst fs and rs = List.map snd fs in
      Some (if inter then (Union ps, Inter rs) else (Inter ps, Union rs))

(** Merge the record atoms of a meet (all fields) or join (common fields). *)
let merge_rcds ~inter = function
  | [] -> None
  | [ r ] -> Some r
  | r :: rs ->
      let names =
        if inter then List.sort_uniq String.compare (List.concat_map (List.map fst) (r :: rs))
        else
          List.filter (fun n -> List.for_all (List.mem_assoc n) rs) (List.map fst r)
      in
      Some
        (List.map
           (fun n ->
             let ts = List.filter_map (List.assoc_opt n) (r :: rs) in
             (n, if inter then Inter ts else Union ts))
           names)

(** [sub hyps pending a b] decides [a ≤ b]. [hyps] are usable assumptions;
    [pending] are assumed but locked (the paper's ▷) until we pass through a
    function or record constructor (◁). *)
let rec sub hyps pending a b =
  if mem_pair a b hyps then true
  else if mem_pair a b pending then false (* unguarded cycle *)
  else
    match (a, b) with
    | Ref c, _ -> sub hyps ((a, b) :: pending) !c b
    | _, Ref c -> sub hyps ((a, b) :: pending) a !c
    | Union xs, _ -> List.for_all (fun x -> sub hyps pending x b) xs
    | _, Inter ys -> List.for_all (fun y -> sub hyps pending a y) ys
    | Flex x, _ ->
        if List.exists (node_eq b) x.ubs then true
        else begin
          x.ubs <- b :: x.ubs;
          List.for_all (fun lb -> sub hyps pending lb b) x.lbs
        end
    | _, Flex y ->
        if List.exists (node_eq a) y.lbs then true
        else begin
          y.lbs <- a :: y.lbs;
          List.for_all (fun ub -> sub hyps pending a ub) y.ubs
        end
    | _ ->
        let l = atoms ~inter:true a and r = atoms ~inter:false b in
        let unlocked = pending @ hyps in
        let shares xs ys = List.exists (fun x -> List.mem x ys) xs in
        l.absorbing || r.absorbing
        || shares l.rigids r.rigids
        || shares l.prims r.prims
        || (match (merge_funs ~inter:true l.funs, merge_funs ~inter:false r.funs) with
            | Some (p0, r0), Some (p1, r1) ->
                sub unlocked [] p1 p0 && sub unlocked [] r0 r1
            | _ -> false)
        ||
        match (merge_rcds ~inter:true l.rcds, merge_rcds ~inter:false r.rcds) with
        | Some fs0, Some fs1 ->
            List.for_all
              (fun (n, t1) ->
                match List.assoc_opt n fs0 with
                | Some t0 -> sub unlocked [] t0 t1
                | None -> false)
              fs1
        | _ -> false

(** [subsumes s1 s2] decides [s1 ≤∀ s2] ([s1] is at least as general).
    @raise Not_polar if either type is not polar. *)
let subsumes (s1 : typ) (s2 : typ) : bool =
  sub [] [] (to_node ~flexible:true s1) (to_node ~flexible:false s2)

type relation = Equivalent | More_general | Less_general | Incomparable

let relate s1 s2 =
  match (subsumes s1 s2, subsumes s2 s1) with
  | true, true -> Equivalent
  | true, false -> More_general
  | false, true -> Less_general
  | false, false -> Incomparable

let equivalent s1 s2 = relate s1 s2 = Equivalent

let show_relation = function
  | Equivalent -> "equivalent"
  | More_general -> "strictly more general"
  | Less_general -> "strictly less general"
  | Incomparable -> "incomparable"
