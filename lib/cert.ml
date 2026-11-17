(** Certificates of type inference, for the Lean checker ([lean/Main.lean],
    roadmap 6b).

    A certificate is the final bounds, the kinds, a list of accepted
    constraints, and the program annotated for a typing skeleton. The checker
    verifies that the constraints justify each other one step at a time and
    that the bounds are consistent; it then follows (Lean, [check_sound])
    that the program has the annotated type in the declarative system.

    What [constrain] accepts is most of the log. The rest is what inference
    relies on without constraining:
    - each bound, as a constraint (bounds installed by extrusion and
      instantiation are never constrained);
    - the relation of an extruded type to its original ([Typer.extrude]
      records it);
    - for each instantiation, the copies of the scheme's constraints. Every
      generalized variable has a copy ([Typer.complete_copies]);
    - for each variable, its lower bounds below its upper bounds, which
      propagation ensures for constrained bounds but not for extruded ones.

    Nothing here is trusted: a wrong certificate is rejected. *)

open Types
open Typer

type t = {
  log : (simple_type * simple_type) list;
  vars : var_state list;  (** the variables of the log *)
}

(** Complete the recorded constraints into a certificate's log. *)
let build () : t =
  let log = ref [] and seen = Cache.create 256 in
  let add (a, b) =
    if not (Types.equal a b || Cache.mem seen (a, b)) then begin
      Cache.add seen (a, b) ();
      log := (a, b) :: !log
    end
  in
  List.iter add (List.rev !accepted);
  (* instantiations, in order: an instantiation inside a [let]'s right-hand
     side comes before those of the [let] itself *)
  List.iter
    (fun inst ->
      let m = Hashtbl.create 16 in
      List.iter (fun (id, c) -> Hashtbl.replace m id c) inst.copies;
      let gen = Hashtbl.create 16 in
      List.iter (fun (a : var_state) -> Hashtbl.replace gen a.id ()) inst.gen;
      let mentions t = List.exists (fun (w : var_state) -> Hashtbl.mem gen w.id) (vars_of [] t) in
      List.iter
        (fun (a, b) -> if mentions a || mentions b then add (rename m a, rename m b))
        (List.rev !log))
    (List.rev !insts);
  (* the bounds of every variable of the log, until no new variables appear *)
  let vars = Hashtbl.create 256 in
  let rec close () =
    let added = ref [] in
    List.iter
      (fun (a, b) ->
        List.iter
          (fun (v : var_state) ->
            if not (Hashtbl.mem vars v.id) then begin
              Hashtbl.add vars v.id v;
              added := v :: !added
            end)
          (vars_of (vars_of [] a) b))
      !log;
    List.iter
      (fun (v : var_state) ->
        List.iter (fun u -> add (Variable v, u)) v.upper_bounds;
        List.iter (fun l -> add (l, Variable v)) v.lower_bounds)
      !added;
    if !added <> [] then close ()
  in
  close ();
  let vars = List.of_seq (Hashtbl.to_seq_values vars) in
  let vars = List.sort (fun (v : var_state) w -> compare v.id w.id) vars in
  List.iter
    (fun (v : var_state) ->
      List.iter (fun l -> List.iter (fun u -> add (l, u)) v.upper_bounds) v.lower_bounds)
    vars;
  { log = List.rev !log; vars }

(** {1 Printing (the format is documented in [lean/Main.lean])} *)

let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let list f xs = "[" ^ String.concat ", " (List.map f xs) ^ "]"

let rec ty = function
  | Variable vs -> Printf.sprintf "{\"var\": %d}" vs.id
  | Primitive n -> Printf.sprintf "{\"prim\": %s}" (json_string n)
  | Function (a, b) -> Printf.sprintf "{\"fun\": [%s, %s]}" (ty a) (ty b)
  | Record (fs, t) ->
      Printf.sprintf "{\"rec\": [%s, %s]}"
        (list (fun (n, f) -> Printf.sprintf "[%s, %s]" (json_string n) (ty f)) fs)
        (ty t)
  | Abs -> "\"abs\""

let gen_ids (gen : var_state list) = list (fun (v : var_state) -> string_of_int v.id) gen

let rec ann = function
  | ALit n -> Printf.sprintf "{\"lit\": %d}" n
  | AVar x -> Printf.sprintf "{\"var\": %s}" (json_string x)
  | AInst (x, inst) ->
      Printf.sprintf "{\"inst\": [%s, %s]}" (json_string x)
        (list (fun (a, (c : var_state)) -> Printf.sprintf "[%d, %d]" a c.id) inst.copies)
  | ALam (x, t, a) -> Printf.sprintf "{\"lam\": [%s, %s, %s]}" (json_string x) (ty t) (ann a)
  | AApp (f, a, t) -> Printf.sprintf "{\"app\": [%s, %s, %s]}" (ann f) (ann a) (ty t)
  | ARcd fs -> Printf.sprintf "{\"rcd\": %s}" (fields fs)
  | ASel (a, l, t) -> Printf.sprintf "{\"sel\": [%s, %s, %s]}" (ann a) (json_string l) (ty t)
  | AExt (a, fs, t) -> Printf.sprintf "{\"ext\": [%s, %s, %s]}" (ann a) (fields fs) (ty t)
  | ALet (x, gen, r, b) ->
      Printf.sprintf "{\"let\": [%s, %s, %s, %s]}" (json_string x) (gen_ids gen) (ann r) (ann b)
  | ALetRec (x, gen, t, r, b) ->
      Printf.sprintf "{\"letrec\": [%s, %s, %s, %s, %s]}" (json_string x) (gen_ids gen) (ty t)
        (ann r) (ann b)

and fields fs = list (fun (n, a) -> Printf.sprintf "[%s, %s]" (json_string n) (ann a)) fs

(** The certificate of a program, annotated as [term]. *)
let to_json (c : t) (term : ann) : string =
  let bounds =
    List.filter (fun (v : var_state) -> v.lower_bounds <> [] || v.upper_bounds <> []) c.vars
  in
  let kinds =
    Hashtbl.fold
      (fun _ (v : var_state) acc -> if SSet.is_empty v.kind then acc else v :: acc)
      all_vars []
  in
  let kinds = List.sort (fun (v : var_state) w -> compare v.id w.id) kinds in
  String.concat ""
    [
      "{\"log\": ";
      list (fun (a, b) -> Printf.sprintf "[%s, %s]" (ty a) (ty b)) c.log;
      ",\n \"bounds\": ";
      list
        (fun (v : var_state) ->
          Printf.sprintf "[%d, %s, %s]" v.id (list ty v.lower_bounds) (list ty v.upper_bounds))
        bounds;
      ",\n \"kinds\": ";
      list
        (fun (v : var_state) ->
          Printf.sprintf "[%d, %s]" v.id (list json_string (SSet.elements v.kind)))
        kinds;
      Printf.sprintf ",\n \"if\": %d,\n \"term\": %s}\n" !if_var (ann term);
    ]
