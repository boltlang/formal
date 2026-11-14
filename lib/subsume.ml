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

(** Raised for types outside the fragment this checker supports. *)
exception Unsupported of string

(** Type graph used during checking. Recursive types become cycles through
    [Ref] cells, so unfolding is dereferencing. *)
type node =
  | Flex of flex  (** instantiable variable of the left-hand scheme *)
  | Rigid of string  (** quantified variable of the right-hand scheme *)
  | Prim of string
  | Fun of node * node
  | Row of (string * node) list * node
      (** record type, or row in tail position: fields ([Absn] or a type)
          and a tail ([Absn] = top row, [Union []] = bottom row, or a row
          variable; unions and intersections are distributed away) *)
  | Absn  (** the absent field (top field) and the top row *)
  | Union of node list  (** [Union []] is ⊥ *)
  | Inter of node list  (** [Inter []] is ⊤ *)
  | Ref of node ref  (** recursive knot *)

and flex = {
  fid : int;
  mutable lbs : node list;
  mutable ubs : node list;
}

(** {1 Undo trail}

    Comparing a meet of rows against a join of rows that cannot be merged
    requires trying several pairs. Bounds recorded on flexible variables by a
    failed attempt are rolled back, so they cannot cause spurious failures
    later. *)

let trail : (flex * node list * node list) list ref = ref []

let save x = trail := (x, x.lbs, x.ubs) :: !trail

let attempt f =
  let mark = !trail in
  if f () then true
  else begin
    let rec undo l =
      if l != mark then
        match l with
        | (x, lbs, ubs) :: rest ->
            x.lbs <- lbs;
            x.ubs <- ubs;
            undo rest
        | [] -> ()
    in
    undo !trail;
    trail := mark;
    false
  end

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
  (* [env] maps recursive binders to their knot and whether we have passed
     a type constructor (function, record field) since the binder. An
     unguarded occurrence, as in [μg. h ∧ g] (which raw coalescing produces
     for variable cycles), is the neutral element of its context: ⊥ in a
     union (positive), ⊤ in an intersection (negative). This matches the
     simplifier, which drops such cycles. *)
  let guard env = List.map (fun (n, (c, _)) -> (n, (c, true))) env in
  let rec go env pol t =
    match t with
    | Top -> Inter []
    | Bot -> Union []
    | Absent -> Absn
    | Union (a, b) ->
        if not pol then raise (Not_polar "union in negative position");
        let a = go env pol a in
        Union [ a; go env pol b ]
    | Inter (a, b) ->
        if pol then raise (Not_polar "intersection in positive position");
        let a = go env pol a in
        Inter [ a; go env pol b ]
    | FunctionType (l, r) ->
        let l = go (guard env) (not pol) l in
        Fun (l, go (guard env) pol r)
    | RecordType (fs, tail) ->
        let fs = List.map (fun (n, f) -> (n, go (guard env) pol f)) fs in
        (* the tail continues the same row: not a guard *)
        Row (fs, go env pol tail)
    | PrimitiveType n -> Prim n
    | TypeVariable n -> (
        match List.assoc_opt n env with
        | Some (cell, true) -> Ref cell
        | Some (_, false) -> if pol then Union [] else Inter []
        | None -> var n)
    | RecursiveType (n, body) ->
        let cell = ref (Union []) in
        cell := go ((n, (cell, false)) :: env) pol body;
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
  | Row (fs, t), Row (gs, u) ->
      List.equal (fun (n, t) (m, u) -> String.equal n m && node_eq t u) fs gs
      && node_eq t u
  | Absn, Absn -> true
  | Union xs, Union ys | Inter xs, Inter ys -> List.equal node_eq xs ys
  | Ref c1, Ref c2 -> c1 == c2
  | _ -> false

let mem_pair a b = List.exists (fun (x, y) -> node_eq x a && node_eq y b)

(** {1 Rows} *)

let atomic_tail = function
  | Absn | Union [] | Rigid _ | Flex _ -> true
  | _ -> false

(** Normalize a row so its tail is atomic: nested rows are flattened, and
    rows distribute over non-empty unions and intersections of tails
    ([{fs | ρ₁ ∨ ρ₂} ≡ {fs | ρ₁} ∨ {fs | ρ₂}], since rows are fieldwise).
    The empty union is the bottom row and is kept: [{x: int | ⊥}] is not ⊥. *)
let rec norm_row fs tail seen =
  match tail with
  | Row (fs', t') -> norm_row (fs @ fs') t' seen
  | Union (_ :: _ as ts) -> Union (List.map (fun t -> norm_row fs t seen) ts)
  | Inter (_ :: _ as ts) -> Inter (List.map (fun t -> norm_row fs t seen) ts)
  | Inter [] -> Row (fs, Absn)
  | Ref c ->
      (* an unguarded recursive tail contributes nothing *)
      if List.memq c seen then Row (fs, Union []) else norm_row fs !c (c :: seen)
  | t -> Row (fs, t)

(** Expansion variables for flexible row variables, memoized per label set
    as in the type checker. Reset by {!subsumes}. *)
let expansions : (int * string list, node) Hashtbl.t = Hashtbl.create 16

let expansion x labels =
  let key = (x.fid, List.sort_uniq String.compare labels) in
  match Hashtbl.find_opt expansions key with
  | Some n -> n
  | None ->
      let n = Flex { fid = fresh_id (); lbs = []; ubs = [] } in
      Hashtbl.add expansions key n;
      n

(** Merge the rows of a meet ([inter]) or join, when this is exact: every
    label missing from one row must be known there (its tail is [Absn]), and
    the tails must combine into an atomic tail. *)
let merge_rows ~inter rows =
  let covers (fs, t) (gs, _) = t = Absn || List.for_all (fun (n, _) -> List.mem_assoc n fs) gs in
  let tail t0 t1 =
    if node_eq t0 t1 then Some t0
    else
      match (inter, t0, t1) with
      | true, Absn, t | true, t, Absn -> Some t (* top is neutral in a meet *)
      | true, Union [], _ | true, _, Union [] -> Some (Union [])
      | false, Union [], t | false, t, Union [] -> Some t (* bottom is neutral in a join *)
      | false, Absn, _ | false, _, Absn -> Some Absn
      | _ -> None
  in
  let field f0 f1 =
    match (inter, f0, f1) with
    | true, Absn, f | true, f, Absn -> f
    | false, Absn, _ | false, _, Absn -> Absn
    | true, f0, f1 -> Inter [ f0; f1 ]
    | false, f0, f1 -> Union [ f0; f1 ]
  in
  let merge ((fs0, t0) as r0) ((fs1, t1) as r1) =
    if not (covers r0 r1 && covers r1 r0) then None
    else
      Option.map
        (fun t ->
          let get fs n = Option.value ~default:Absn (List.assoc_opt n fs) in
          let names = List.sort_uniq String.compare (List.map fst fs0 @ List.map fst fs1) in
          (List.map (fun n -> (n, field (get fs0 n) (get fs1 n))) names, t))
        (tail t0 t1)
  in
  List.fold_left
    (fun acc r ->
      let rec ins = function
        | [] -> [ r ]
        | r0 :: rest -> (
            match merge r0 r with Some m -> m :: rest | None -> r0 :: ins rest)
      in
      ins acc)
    [] rows

(** {1 Atoms of meets and joins} *)

(** Flatten nested intersections (resp. unions), unfolding knots on the way.
    [seen] guards against unguarded cycles such as [μα. α ∧ int]. *)
let rec flatten ~inter seen n =
  match n with
  | Inter xs when inter -> List.concat_map (flatten ~inter seen) xs
  | Union xs when not inter -> List.concat_map (flatten ~inter seen) xs
  | Ref c -> if List.memq c seen then [] else flatten ~inter (c :: seen) !c
  | Row (fs, t) when not (atomic_tail t) -> flatten ~inter seen (norm_row fs t [])
  | n -> [ n ]

type atoms = {
  rigids : string list;
  prims : string list;
  funs : (node * node) list;
  rows : ((string * node) list * node) list;
  abs : bool;  (** contains the absent field / top row *)
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
      | Row (fs, t) -> { acc with rows = (fs, t) :: acc.rows }
      | Absn -> { acc with abs = true }
      | Union [] when inter -> { acc with absorbing = true }
      | Inter [] when not inter -> { acc with absorbing = true }
      | other -> { acc with others = other :: acc.others })
    (flatten ~inter [] n)
    { rigids = []; prims = []; funs = []; rows = []; abs = false; absorbing = false; others = [] }

(** Merge the function atoms of a meet ([inter]) or join. *)
let merge_funs ~inter = function
  | [] -> None
  | [ f ] -> Some f
  | fs ->
      let ps = List.map fst fs and rs = List.map snd fs in
      Some (if inter then (Union ps, Inter rs) else (Inter ps, Union rs))

(** {1 Subtyping} *)

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
    | Row (fs, t), _ when not (atomic_tail t) -> sub hyps pending (norm_row fs t []) b
    | _, Row (fs, t) when not (atomic_tail t) -> sub hyps pending a (norm_row fs t [])
    | Union xs, _ -> List.for_all (fun x -> sub hyps pending x b) xs
    | _, Inter ys -> List.for_all (fun y -> sub hyps pending a y) ys
    | _, Absn -> true (* top field / top row *)
    | Flex x, _ ->
        if List.exists (node_eq b) x.ubs then true
        else begin
          save x;
          x.ubs <- b :: x.ubs;
          List.for_all (fun lb -> sub hyps pending lb b) x.lbs
        end
    | _, Flex y ->
        if List.exists (node_eq a) y.lbs then true
        else begin
          save y;
          y.lbs <- a :: y.lbs;
          List.for_all (fun ub -> sub hyps pending a ub) y.ubs
        end
    | _ ->
        let l = atoms ~inter:true a and r = atoms ~inter:false b in
        let unlocked = pending @ hyps in
        let shares xs ys = List.exists (fun x -> List.mem x ys) xs in
        (* in a meet, Abs on its own is the top row *)
        let lrows = if l.abs && l.rows = [] then [ ([], Absn) ] else l.rows in
        let lrows = merge_rows ~inter:true lrows and rrows = merge_rows ~inter:false r.rows in
        l.absorbing || r.absorbing || r.abs
        || shares l.rigids r.rigids
        || shares l.prims r.prims
        || attempt (fun () ->
               match (merge_funs ~inter:true l.funs, merge_funs ~inter:false r.funs) with
               | Some (p0, r0), Some (p1, r1) ->
                   sub unlocked [] p1 p0 && sub unlocked [] r0 r1
               | _ -> false)
        || List.exists
             (fun r1 ->
               List.exists (fun r0 -> attempt (fun () -> row_sub unlocked r0 r1)) lrows
               || (List.length lrows > 1 && attempt (fun () -> row_meet_sub unlocked lrows r1)))
             rrows

(** A meet of rows that could not be merged, against a row with an [Abs]
    tail: compare field by field, intersecting the explicit types each left
    row gives a label. Rows that would only provide the label through their
    tail are left out of the intersection, which is sound (dropping
    conjuncts on the left only makes the check harder). A label no left row
    mentions is provided by expanding a flexible tail if there is one, by a
    bottom tail, or else must be [Abs] on the right. *)
and row_meet_sub hyps rows (fs1, t1) =
  t1 = Absn
  && List.for_all
       (fun (n, f1) ->
         match List.filter_map (fun (fs, _) -> List.assoc_opt n fs) rows with
         | [ f0 ] -> sub hyps [] f0 f1
         | _ :: _ as fs0 -> sub hyps [] (Inter fs0) f1
         | [] -> (
             let tails = List.map snd rows in
             if List.mem (Union []) tails then true
             else
               match List.find_opt (function Flex _ -> true | _ -> false) tails with
               | Some (Flex x as t0) ->
                   sub hyps [] t0 (Row ([ (n, f1) ], expansion x [ n ]))
               | _ -> sub hyps [] Absn f1))
       fs1

(** [{fs₀ | t₀} ≤ {fs₁ | t₁}] for atomic tails. Mirrors the type checker:
    labels on both sides are compared; a label only on the right must be
    provided by [t₀] (a flexible tail is expanded; [Abs] or a rigid tail can
    only satisfy an [Abs] field; the bottom row satisfies anything); what is
    left of the left row must fit in [t₁]. *)
and row_sub hyps (fs0, t0) (fs1, t1) =
  List.for_all
    (fun (n, f1) ->
      match List.assoc_opt n fs0 with Some f0 -> sub hyps [] f0 f1 | None -> true)
    fs1
  &&
  let missing = List.filter (fun (n, _) -> not (List.mem_assoc n fs0)) fs1 in
  let t0' =
    if missing = [] then Some t0
    else
      match t0 with
      | Union [] -> Some t0
      | Absn | Rigid _ ->
          if List.for_all (fun (_, f1) -> sub hyps [] Absn f1) missing then Some t0 else None
      | Flex x ->
          let x' = expansion x (List.map fst missing) in
          if sub hyps [] t0 (Row (missing, x')) then Some x' else None
      | _ -> None
  in
  match t0' with
  | None -> false
  | Some t0' ->
      let extra = List.filter (fun (n, _) -> not (List.mem_assoc n fs1)) fs0 in
      sub hyps [] (if extra = [] then t0' else Row (extra, t0')) t1

(** [subsumes s1 s2] decides [s1 ≤∀ s2] ([s1] is at least as general).
    @raise Not_polar if either type is not polar. *)
let subsumes (s1 : typ) (s2 : typ) : bool =
  Hashtbl.reset expansions;
  trail := [];
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

(** As a relation between two types: "[t1] is ... [t2]". *)
let show_relation_to = function
  | Equivalent -> "equivalent to"
  | More_general -> "strictly more general than"
  | Less_general -> "strictly less general than"
  | Incomparable -> "incomparable to"
