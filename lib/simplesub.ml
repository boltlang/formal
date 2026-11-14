(** Simple-sub: an OCaml port of the core algorithm from
    "The Simple Essence of Algebraic Subtyping" (Parreaux, ICFP 2020). *)

module Syntax = Syntax
module Types = Types
module Typer = Typer
module Coalesce = Coalesce
module Parser = Parser

(** Infer and coalesce the type of a closed term in the built-in context. *)
let infer_term (t : Syntax.term) : Types.typ =
  let ty = Typer.type_term (Typer.builtins ()) 0 t in
  Coalesce.coalesce_type ty

type result = { name : string option; outcome : (Types.typ, string) Stdlib.result }

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
              outcome = Ok (Coalesce.coalesce_type (Typer.instantiate sch 0)) }
        | Syntax.Expr t ->
            { name = None;
              outcome = Ok (Coalesce.coalesce_type (Typer.type_term !ctx 0 t)) }
      with Typer.Type_error msg ->
        let name = match item with Syntax.Decl (_, n, _) -> Some n | _ -> None in
        { name; outcome = Error msg })
    items
