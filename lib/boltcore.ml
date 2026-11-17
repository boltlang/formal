(** Simple-sub: an OCaml port of the core algorithm from
    "The Simple Essence of Algebraic Subtyping" (Parreaux, ICFP 2020). *)

module Syntax = Syntax
module Types = Types
module Typer = Typer
module Coalesce = Coalesce
module Parser = Parser
module Simplify = Simplify
module Subsume = Subsume
module Cert = Cert

(** Turn an inferred type into a user-facing one: simplified (Sec. 4) by
    default, or merely coalesced (Sec. 3.3) with [~simplify:false]. *)
let display ?(simplify = true) ty =
  if simplify then Simplify.simplify_type ty else Coalesce.coalesce_type ty

(** Infer the type of a closed term in the built-in context. *)
let infer_term ?simplify (t : Syntax.term) : Types.typ =
  display ?simplify (Typer.type_term (Typer.builtins ()) 0 t)

type result = {
  name : string option;
  outcome : (Types.simple_type, string) Stdlib.result;
      (** the inferred internal type; see {!display} *)
}

(** An item's annotated term, for its certificate. *)
type item_ann = IDecl of string * Typer.let_ann | IExpr of Typer.ann

(** Infer every item of a program. Top-level [let]s are generalized and added
    to the context; an item that fails to type-check is reported and skipped.
    Also returns the annotated terms of the items that type-check. *)
let infer_program_ann (items : Syntax.item list) : result list * item_ann list =
  let ctx = ref (Typer.builtins ()) in
  let anns = ref [] in
  let results =
    List.map
      (fun item ->
        (* a failed item's constraints are not part of the certificate *)
        let accepted = !Typer.accepted and insts = !Typer.insts in
        let name = match item with Syntax.Decl (_, n, _) -> Some n | _ -> None in
        let failed msg =
          Typer.accepted := accepted;
          Typer.insts := insts;
          { name; outcome = Error msg }
        in
        try
          match item with
          | Syntax.Decl (isrec, name, rhs) ->
              let sch, la = Typer.type_let_rhs_ann !ctx 0 isrec name rhs in
              ctx := Typer.StringMap.add name sch !ctx;
              anns := IDecl (name, la) :: !anns;
              { name = Some name; outcome = Ok (Typer.instantiate sch 0) }
          | Syntax.Expr t ->
              let ty, a = Typer.type_term_ann !ctx 0 t in
              anns := IExpr a :: !anns;
              { name = None; outcome = Ok ty }
        with
        | Typer.Type_error msg -> failed msg
        | Typer.Kind_error msg ->
            (* a violated kind invariant is a bug in the type checker *)
            failed ("internal error, ill-kinded row: " ^ msg))
      items
  in
  (results, List.rev !anns)

let infer_program items = fst (infer_program_ann items)

(** The program as one annotated term: each item is a [let] around the rest
    (an expression is bound to [_]); the last expression, or the last
    declared name, is the body. *)
let program_ann (items : item_ann list) : Typer.ann =
  let wrap x (la : Typer.let_ann) body =
    match la.rec_ty with
    | None -> Typer.ALet (x, la.gen, la.rhs, body)
    | Some t -> Typer.ALetRec (x, la.gen, t, la.rhs, body)
  in
  let rec go = function
    | [] -> Typer.ALit 0
    | [ IExpr a ] -> a
    | [ IDecl (x, la) ] ->
        (* the name itself, at the identity instance *)
        wrap x la (Typer.AInst (x, { gen = []; copies = [] }))
    | IExpr a :: rest -> Typer.ALet ("_", [], a, go rest)
    | IDecl (x, la) :: rest -> wrap x la (go rest)
  in
  go items

(** Infer a program and print its certificate. *)
let certificate (items : Syntax.item list) : result list * string =
  Typer.recording := true;
  let results, anns = infer_program_ann items in
  Typer.recording := false;
  let c = Cert.build () in
  (results, Cert.to_json c (program_ann anns))
