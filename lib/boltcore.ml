(** Simple-sub: an OCaml port of the core algorithm from
    "The Simple Essence of Algebraic Subtyping" (Parreaux, ICFP 2020). *)

module Syntax = Syntax
module Types = Types
module Typer = Typer
module Coalesce = Coalesce
module Parser = Parser
module Simplify = Simplify
module Subsume = Subsume

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

(** Infer every item of a program. Top-level [let]s are generalized and added
    to the context; an item that fails to type-check is reported and skipped. *)
let infer_program (items : Syntax.item list) : result list =
  let ctx = ref (Typer.builtins ()) in
  List.map
    (fun item ->
      try
        match item with
        | Syntax.Decl (isrec, name, rhs) ->
            let sch = Typer.type_let_rhs !ctx 0 isrec name rhs in
            ctx := Typer.StringMap.add name sch !ctx;
            { name = Some name;
              outcome = Ok (Typer.instantiate sch 0) }
        | Syntax.Expr t ->
            { name = None;
              outcome = Ok (Typer.type_term !ctx 0 t) }
      with
      | Typer.Type_error msg ->
          let name = match item with Syntax.Decl (_, n, _) -> Some n | _ -> None in
          { name; outcome = Error msg }
      | Typer.Kind_error msg ->
          (* a violated kind invariant is a bug in the type checker *)
          let name = match item with Syntax.Decl (_, n, _) -> Some n | _ -> None in
          { name; outcome = Error ("internal error, ill-kinded row: " ^ msg) })
    items
