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
      (** record type, or row in tail position: fields ([Absn], [Missn],
          [Optn] or a type) and a tail ([Absn] = top row, [Niln] = empty
          row, [Union []] = bottom row, or a row variable; unions and
          intersections are distributed away) *)
  | Absn  (** the top field and the top row *)
  | Missn  (** the field that is definitely absent *)
  | Optn of node  (** a field: missing, or present at the type *)
  | Niln  (** the empty row: every field is [Missn] *)
  | Sign of sparam list
      (** a parameter list: the union of its argument records [Dₖ]
          ({!Types.sig_domain}), never merged with other types *)
  | Union of node list  (** [Union []] is ⊥ *)
  | Inter of node list  (** [Inter []] is ⊤ *)
  | Ref of node ref  (** recursive knot *)

and sparam = { gname : string; gkind : Types.pkind; gty : node; gopt : bool }

and flex = {
  fid : int;
  fkind : SSet.t;  (** row kind: labels this variable does not represent *)
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
(** {1 Kinds}

    The kind of a row variable (the labels it does not represent) is not
    written in types; it is inferred from how the variable is used: a
    variable that is the tail of [{L | 'a}] lacks [L]. A label in a tail's
    kind projects to [Abs] from that tail. *)

module SSet = Types.SSet

let kind_of tbl n = Option.value ~default:SSet.empty (Hashtbl.find_opt tbl n)

(** Infer kinds from the tails of a type's records. *)
let infer_kinds (t : typ) : (string, SSet.t) Hashtbl.t =
  let tbl = Hashtbl.create 8 in
  let add n labels = Hashtbl.replace tbl n (SSet.union labels (kind_of tbl n)) in
  let rec tails labels = function
    | TypeVariable n -> add n labels
    | Types.Union (a, b) | Types.Inter (a, b) -> tails labels a; tails labels b
    | RecordType (fs, t) -> tails (SSet.union labels (SSet.of_list (List.map fst fs))) t
    | _ -> ()
  in
  let rec go = function
    | Types.Union (a, b) | Types.Inter (a, b) | FunctionType (a, b) -> go a; go b
    | RecordType (fs, t) ->
        List.iter (fun (_, f) -> go f) fs;
        tails (SSet.of_list (List.map fst fs)) t;
        go t
    | RecursiveType (_, b) | Optional b -> go b
    | SigType ps -> List.iter (fun p -> go p.tty) ps
    | _ -> ()
  in
  go t;
  tbl

(** Kinds of the rigid variables of the current check. Reset by {!subsumes}. *)
let rigid_kinds : (string, SSet.t) Hashtbl.t = Hashtbl.create 8

(** The kind of a tail: of an atomic one, or of a join of rigid row
    variables ({!merge_rows}), which lacks the labels all of them lack. *)
let rec tail_kind = function
  | Flex x -> x.fkind
  | Rigid n -> kind_of rigid_kinds n
  | Union (t :: ts) -> List.fold_left (fun k t -> SSet.inter k (tail_kind t)) (tail_kind t) ts
  | _ -> SSet.empty

let to_node ~flexible (t : typ) : node =
  let kinds = infer_kinds t in
  let vars : (string, node) Hashtbl.t = Hashtbl.create 8 in
  let var n =
    match Hashtbl.find_opt vars n with
    | Some v -> v
    | None ->
        let v =
          if flexible then
            Flex { fid = fresh_id (); fkind = kind_of kinds n; lbs = []; ubs = [] }
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
    | AbsType -> Absn
    | MissingType -> Missn
    | NilType -> Niln
    | Optional t -> Optn (go env pol t)
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
    | SigType ps ->
        (* the parameters are fields of the argument records *)
        Sign
          (List.map
             (fun p -> { gname = p.tname; gkind = p.tkind; gty = go (guard env) pol p.tty; gopt = p.topt })
             ps)
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
  | Absn, Absn | Missn, Missn | Niln, Niln -> true
  | Optn a, Optn b -> node_eq a b
  | Sign ps, Sign qs ->
      List.equal
        (fun p q ->
          String.equal p.gname q.gname && p.gkind = q.gkind && p.gopt = q.gopt
          && node_eq p.gty q.gty)
        ps qs
  | Union xs, Union ys | Inter xs, Inter ys -> List.equal node_eq xs ys
  | Ref c1, Ref c2 -> c1 == c2
  | _ -> false

let mem_pair a b = List.exists (fun (x, y) -> node_eq x a && node_eq y b)

(** {1 Parameter lists}

    As in the type checker ({!Types.sig_domain}): [Dₖ] is the closed record
    of the arguments when [k] are passed by position. *)

let rec list_node = function
  | [] -> Row ([], Niln)
  | t :: ts -> Row ([ ("hd", t); ("tl", list_node ts) ], Niln)

let sig_bounds ps =
  let m = List.length (List.filter (fun p -> p.gkind = PosOnly && not p.gopt) ps) in
  (m, List.length (List.filter (fun p -> p.gkind <> KwOnly) ps))

let sig_domain ps k =
  let m, p = sig_bounds ps in
  if k < m || k > p then None
  else
    let field q = (q.gname, if q.gopt then Optn q.gty else q.gty) in
    let rec split i = function
      | q :: rest when q.gkind <> KwOnly ->
          let pos, named = split (i + 1) rest in
          if i < k then (q.gty :: pos, named)
          else if q.gkind = Either then (pos, field q :: named)
          else (pos, named)
      | rest -> ([], List.map field rest)
    in
    let pos, named = split 0 ps in
    Some (Row ((args_label, list_node pos) :: named, Niln))

let sig_domains ps =
  let m, p = sig_bounds ps in
  List.filter_map (sig_domain ps) (List.init (p - m + 1) (fun i -> m + i))

(** The elements of a list type whose spine is known. *)
let list_elems n =
  let rec go fuel n =
    if fuel = 0 then None
    else
      match n with
      | Ref c -> go (fuel - 1) !c
      | Row ([], Niln) -> Some []
      | Row (fs, Niln) when List.length fs = 2 -> (
          match (List.assoc_opt "hd" fs, List.assoc_opt "tl" fs) with
          | Some hd, Some tl -> Option.map (fun ts -> hd :: ts) (go (fuel - 1) tl)
          | _ -> None)
      | _ -> None
  in
  go 1000 n

(** {1 Rows} *)

let atomic_tail = function
  | Absn | Niln | Union [] | Rigid _ | Flex _ -> true
  | _ -> false

(** {1 Fields}

    A field is [Abs], [Missing], [Opt τ], a type [τ] (present), or a meet or
    join of fields, which the simplifier and [merge_rows] produce. A view
    normalizes it with the equations of the field lattice:
    {v
    τ ∨ Missing     = Opt τ          Opt τ ∧ σ       = τ ∧ σ
    Opt τ ∨ σ       = Opt (τ ∨ σ)    Opt τ ∧ Opt σ   = Opt (τ ∧ σ)
    θ ∨ Abs         = Abs            Opt τ ∧ Missing = Missing
    θ ∧ Abs         = θ              τ ∧ Missing     = ⊥
    v} *)
type fview = FAbs | FMis | FOpt of node | FPre of node | FBot

let view_meet a b =
  match (a, b) with
  | FAbs, v | v, FAbs -> v
  | FBot, _ | _, FBot -> FBot
  | FMis, (FMis | FOpt _) | FOpt _, FMis -> FMis
  | FMis, FPre _ | FPre _, FMis -> FBot
  | FOpt a, FOpt b -> FOpt (Inter [ a; b ])
  | FOpt a, FPre b | FPre a, FOpt b | FPre a, FPre b -> FPre (Inter [ a; b ])

let view_join a b =
  match (a, b) with
  | FAbs, _ | _, FAbs -> FAbs
  | FBot, v | v, FBot -> v
  | FMis, FMis -> FMis
  | FMis, (FOpt a | FPre a) | (FOpt a | FPre a), FMis -> FOpt a
  | FOpt a, FOpt b | FOpt a, FPre b | FPre a, FOpt b -> FOpt (Union [ a; b ])
  | FPre a, FPre b -> FPre (Union [ a; b ])

let rec field_view n =
  let combine f xs =
    let vs = List.map field_view xs in
    (* a meet or join of types is left as it is *)
    if List.for_all (function FPre _ -> true | _ -> false) vs then FPre n
    else List.fold_left f (List.hd vs) (List.tl vs)
  in
  match n with
  | Absn -> FAbs
  | Missn -> FMis
  | Optn t -> FOpt t
  | Inter (_ :: _ as xs) -> combine view_meet xs
  | Union (_ :: _ as xs) -> combine view_join xs
  | n -> FPre n

let of_view = function
  | FAbs -> Absn
  | FMis -> Missn
  | FOpt t -> Optn t
  | FPre t -> t
  | FBot -> Union []

let field_meet fs = of_view (List.fold_left view_meet FAbs (List.map field_view fs))

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
      let fkind = List.fold_left (fun k l -> SSet.add l k) x.fkind labels in
      let n = Flex { fid = fresh_id (); fkind; lbs = []; ubs = [] } in
      Hashtbl.add expansions key n;
      n

(** Merge the rows of a meet ([inter]) or join, when this is exact: every
    label missing from one row must be known there (its tail is [Absn] or
    [Niln]), and the tails must combine: into an atomic tail, or, for a
    join, into a join of rigid row variables. The simplifier merges
    [{x: σ | ρ₁} ∨ {x: τ | ρ₂}] into [{x: σ ∨ τ | ρ₁ ∨ ρ₂}] ([Simplify.add_row]),
    so the two rows have to be one row here too; only the right-hand side
    has joins of rows, and its variables are rigid. *)
let merge_rows ~inter rows =
  (* the variables of a join of rigid row variables *)
  let rec rigids = function
    | Rigid n -> Some [ n ]
    | Union (_ :: _ as ts) ->
        List.fold_left
          (fun acc t ->
            match (acc, rigids t) with Some a, Some b -> Some (a @ b) | _ -> None)
          (Some []) ts
    | _ -> None
  in
  let covers (fs, t) (gs, _) =
    t = Absn || t = Niln || List.for_all (fun (n, _) -> List.mem_assoc n fs) gs
  in
  let tail t0 t1 =
    if node_eq t0 t1 then Some t0
    else
      match (inter, t0, t1) with
      | true, Absn, t | true, t, Absn -> Some t (* top is neutral in a meet *)
      | true, Union [], _ | true, _, Union [] -> Some (Union [])
      | false, Union [], t | false, t, Union [] -> Some t (* bottom is neutral in a join *)
      | false, Absn, _ | false, _, Absn -> Some Absn
      | false, _, _ -> (
          match (rigids t0, rigids t1) with
          | Some a, Some b ->
              Some (Union (List.map (fun n -> Rigid n) (List.sort_uniq String.compare (a @ b))))
          | _ -> None)
      | _ -> None
  in
  let field f0 f1 =
    of_view ((if inter then view_meet else view_join) (field_view f0) (field_view f1))
  in
  (* argument records with different numbers of positional arguments stay
     apart, as in the simplifier ([Simplify.same_spine]) *)
  let same_spine (fs0, _) (fs1, _) =
    match (List.assoc_opt args_label fs0, List.assoc_opt args_label fs1) with
    | None, None -> true
    | Some l0, Some l1 -> (
        match (list_elems l0, list_elems l1) with
        | Some a, Some b -> List.length a = List.length b
        | _ -> false)
    | _ -> false
  in
  let merge ((fs0, t0) as r0) ((fs1, t1) as r1) =
    if not (covers r0 r1 && covers r1 r0 && same_spine r0 r1) then None
    else
      Option.map
        (fun t ->
          (* a label a row does not list: its tail tells *)
          let get (fs, t) n =
            match List.assoc_opt n fs with
            | Some f -> f
            | None -> if t = Niln then Missn else Absn
          in
          let names = List.sort_uniq String.compare (List.map fst fs0 @ List.map fst fs1) in
          (List.map (fun n -> (n, field (get r0 n) (get r1 n))) names, t))
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
  sigs : node list;
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
      | Niln -> { acc with rows = ([], Niln) :: acc.rows }
      | Sign _ -> { acc with sigs = a :: acc.sigs }
      | Absn -> { acc with abs = true }
      | Union [] when inter -> { acc with absorbing = true }
      | Inter [] when not inter -> { acc with absorbing = true }
      | other -> { acc with others = other :: acc.others })
    (flatten ~inter [] n)
    { rigids = []; prims = []; funs = []; rows = []; sigs = []; abs = false; absorbing = false; others = [] }

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
    (* a field where a type is expected: only as a field *)
    | (Optn _ | Missn), _ | _, (Optn _ | Missn) -> field_sub (pending @ hyps) a b
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
    (* the empty row *)
    | Niln, Niln -> true
    | Absn, Niln -> false
    | Row (fs, t), Niln ->
        let unlocked = pending @ hyps in
        List.for_all (fun (_, f) -> field_sub unlocked f Missn) fs && sub unlocked [] t Niln
    | Niln, Row (fs, t) ->
        let unlocked = pending @ hyps in
        List.for_all (fun (_, f) -> field_sub unlocked Missn f) fs && sub unlocked [] Niln t
    (* a signature is the union of its records; an argument record is below
       it when it is below the record its number of positional arguments
       picks *)
    | Sign ps, _ -> List.for_all (fun d -> sub hyps pending d b) (sig_domains ps)
    | Row (fs, _), Sign ps -> (
        match Option.bind (List.assoc_opt args_label fs) list_elems with
        | None -> false
        | Some ts -> (
            match sig_domain ps (List.length ts) with
            | Some d -> sub hyps pending a d
            | None -> false))
    | _ ->
        let l = atoms ~inter:true a and r = atoms ~inter:false b in
        let unlocked = pending @ hyps in
        let shares xs ys = List.exists (fun x -> List.mem x ys) xs in
        (* in a meet, Abs on its own is the top row *)
        let lrows = if l.abs && l.rows = [] then [ ([], Absn) ] else l.rows in
        let lrows = merge_rows ~inter:true lrows and rrows = merge_rows ~inter:false r.rows in
        List.exists (fun x -> attempt (fun () -> sub hyps pending x b)) l.sigs
        || List.exists
             (fun y -> List.exists (fun (fs, t) -> attempt (fun () -> sub hyps pending (Row (fs, t)) y)) lrows)
             r.sigs
        || l.absorbing || r.absorbing || r.abs
        || shares l.rigids r.rigids
        || shares l.prims r.prims
        || attempt (fun () ->
               match (merge_funs ~inter:true l.funs, merge_funs ~inter:false r.funs) with
               | Some (p0, r0), Some (p1, r1) ->
                   sub unlocked [] p1 p0 && sub unlocked [] r0 r1
               | _ -> false)
        || List.exists
             (fun r1 ->
               (* with several left rows, compare field by field first: it
                  commits the weakest bounds; picking a single left row can
                  commit a flexible tail to too much (see [row_meet_sub]) *)
               (List.length lrows > 1 && attempt (fun () -> row_meet_sub unlocked lrows r1))
               || List.exists (fun r0 -> attempt (fun () -> row_sub unlocked r0 r1)) lrows)
             rrows

(** [f0 ≤ f1] for fields: [Pre τ ≤ Opt τ], [Missing ≤ Opt τ], [θ ≤ Abs],
    and [Pre ⊥] is the bottom field. *)
and field_sub hyps f0 f1 =
  match (field_view f0, field_view f1) with
  | _, FAbs | FBot, _ -> true
  | FAbs, _ -> false
  | FMis, (FMis | FOpt _) -> true
  | FMis, (FPre _ | FBot) -> false
  | (FOpt a | FPre a), FOpt b | FPre a, FPre b -> sub hyps [] a b
  | FOpt _, (FPre _ | FBot) -> false
  | FOpt a, FMis | FPre a, (FMis | FBot) -> sub hyps [] a (Union [])

(** A meet of rows that could not be merged, against a row: compare field
    by field, intersecting the explicit types each left row gives a label.
    Rows that would only provide the label through their tail are left out of
    the intersection, which is sound (dropping conjuncts on the left only
    makes the check harder). A label no left row mentions is provided by
    expanding a flexible tail if there is one, by a bottom tail, or else must
    be [Abs] on the right (if a left tail is the empty row, [Missing] is
    also enough). The right tail then receives the *meet* of what is left of
    every left row. When the right tail is the empty row, that meet is
    compared directly: every label left over must be missing in the meet,
    and some left tail must be below the empty row.

    Choosing a single left row instead can commit a flexible right tail to
    too much: [{a: Abs | ρ₁} ∧ {a: Abs, b: Abs | ρ₁'} ≤ {a: Abs, b: Abs | φ}]
    holds through the first row with [φ ≥ ρ₁], which then conflicts with a
    later [φ ≤ ρ₁']; the meet [φ ≥ ρ₁ ∧ ρ₁'] does not. What is left of a row
    may still mention labels of the right row (through its tail), but there
    the right row's explicit fields shadow its tail, so they do not matter. *)
and row_meet_sub hyps rows (fs1, t1) =
  List.for_all
    (fun (n, f1) ->
      match List.filter_map (fun (fs, _) -> List.assoc_opt n fs) rows with
      | _ :: _ as fs0 -> field_sub hyps (field_meet fs0) f1
      | [] -> (
          let tails = List.map snd rows in
          if List.mem (Union []) tails then true
          else if List.mem Niln tails && field_sub hyps Missn f1 then true
          else
            match List.find_opt (function Flex _ -> true | _ -> false) tails with
            | Some (Flex x as t0) -> sub hyps [] t0 (Row ([ (n, f1) ], expansion x [ n ]))
            | _ -> field_sub hyps Absn f1))
    fs1
  &&
  (t1 = Absn
  ||
  if t1 = Niln then
    let left = List.concat_map (fun (fs, _) -> List.map fst fs) rows in
    let left = List.filter (fun n -> not (List.mem_assoc n fs1)) left in
    List.for_all
      (fun n ->
        List.exists (fun (fs, t) -> t = Niln && not (List.mem_assoc n fs)) rows
        || field_sub hyps
             (field_meet (List.filter_map (fun (fs, _) -> List.assoc_opt n fs) rows))
             Missn)
      (List.sort_uniq String.compare left)
    && List.exists (fun (_, t) -> attempt (fun () -> sub hyps [] t Niln)) rows
  else
  let k1 = tail_kind t1 in
  let rest (fs, t) =
    match List.filter (fun (n, _) -> not (List.mem_assoc n fs1) && not (SSet.mem n k1)) fs with
    | [] -> t
    | extra -> Row (extra, t)
  in
  sub hyps [] (Inter (List.map rest rows)) t1)

(** [{fs₀ | t₀} ≤ {fs₁ | t₁}] for atomic tails. Mirrors the type checker:
    labels on both sides are compared; a label only on the right must be
    provided by [t₀] (a flexible tail is expanded; [Abs] or a rigid tail can
    only satisfy an [Abs] field; the empty row gives [Missing]; the bottom
    row satisfies anything); what is left of the left row must fit in [t₁]. *)
and row_sub hyps (fs0, t0) (fs1, t1) =
  List.for_all
    (fun (n, f1) ->
      match List.assoc_opt n fs0 with Some f0 -> field_sub hyps f0 f1 | None -> true)
    fs1
  &&
  let missing = List.filter (fun (n, _) -> not (List.mem_assoc n fs0)) fs1 in
  let t0' =
    if missing = [] then Some t0
    else
      match t0 with
      | Union [] -> Some t0
      | Absn | Rigid _ ->
          if List.for_all (fun (_, f1) -> field_sub hyps Absn f1) missing then Some t0 else None
      | Niln ->
          if List.for_all (fun (_, f1) -> field_sub hyps Missn f1) missing then Some t0 else None
      | Flex x ->
          (* labels in the tail's kind are absent from it; expand the rest *)
          let absent, present = List.partition (fun (n, _) -> SSet.mem n x.fkind) missing in
          if not (List.for_all (fun (_, f1) -> field_sub hyps Absn f1) absent) then None
          else if present = [] then Some t0
          else
            let x' = expansion x (List.map fst present) in
            if sub hyps [] t0 (Row (present, x')) then Some x' else None
      | _ -> None
  in
  match t0' with
  | None -> false
  | Some t0' ->
      (* fields only on the left must fit the right tail, unless the tail's
         kind contains them: there the right row's field is [Abs] *)
      let k1 = tail_kind t1 in
      let extra =
        List.filter (fun (n, _) -> not (List.mem_assoc n fs1) && not (SSet.mem n k1)) fs0
      in
      sub hyps [] (if extra = [] then t0' else Row (extra, t0')) t1

(** [subsumes s1 s2] decides [s1 ≤∀ s2] ([s1] is at least as general).
    @raise Not_polar if either type is not polar. *)
let subsumes (s1 : typ) (s2 : typ) : bool =
  Hashtbl.reset expansions;
  trail := [];
  Hashtbl.reset rigid_kinds;
  Hashtbl.iter (Hashtbl.replace rigid_kinds) (infer_kinds s2);
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
