(** Type coalescing (Sec. 3.3.3): turn an internal [simple_type], whose
    variables carry bounds, into an immutable user-facing [typ] by replacing
    positive occurrences of variables with the union of their lower bounds and
    negative occurrences with the intersection of their upper bounds. Cycles
    through bounds become (polar) recursive types. No simplification is done
    here (Sec. 4 is not part of the core). *)

open Types

module PolarSet = Set.Make (struct
  type t = int * bool

  let compare = compare
end)

let var_name (vs : var_state) = "α" ^ string_of_int vs.id

let coalesce_type (ty : simple_type) : typ =
  let recursive : (int * bool, string) Hashtbl.t = Hashtbl.create 16 in
  let rec go ty polar in_process =
    match ty with
    | Primitive n -> PrimitiveType n
    | Function (l, r) ->
        let l = go l (not polar) in_process in
        FunctionType (l, go r polar in_process)
    | Record (fs, t) ->
        let fs = List.map (fun (n, f) -> (n, go f polar in_process)) fs in
        RecordType (fs, go t polar in_process)
    | Abs -> Absent
    | Variable vs -> (
        let vs_pol = (vs.id, polar) in
        if PolarSet.mem vs_pol in_process then
          TypeVariable
            (match Hashtbl.find_opt recursive vs_pol with
            | Some n -> n
            | None ->
                let n = "α" ^ string_of_int (fresh_id ()) in
                Hashtbl.add recursive vs_pol n;
                n)
        else
          let bounds = if polar then vs.lower_bounds else vs.upper_bounds in
          let in_process' = PolarSet.add vs_pol in_process in
          let bound_types = List.map (fun b -> go b polar in_process') bounds in
          let mrg a b = if polar then Union (a, b) else Inter (a, b) in
          let res = List.fold_left mrg (TypeVariable (var_name vs)) bound_types in
          match Hashtbl.find_opt recursive vs_pol with
          | Some n -> RecursiveType (n, res)
          | None -> res)
  in
  go ty true PolarSet.empty
