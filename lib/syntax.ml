(** Term syntax (paper, Fig. 4). *)

type term =
  | Lit of int  (** [27] *)
  | Var of string  (** [x] *)
  | Lam of string * term  (** [fun x -> t] *)
  | App of term * term  (** [s t] *)
  | Rcd of (string * term) list  (** [{a = 0; b = true}] *)
  | Sel of term * string  (** [t.a] *)
  | SelOr of term * string * term
      (** [t.a ?? d]: the field if it is present, else [d] *)
  | Ext of term * (string * term) list
      (** [t with {a = s; b = u}]: extend or update fields *)
  | Let of bool * string * term * term  (** [let rec? x = s in t] *)
  | If of term * term * term
      (** [if c then a else b]: only the chosen branch is evaluated *)
  | Fn of param list * term
      (** [fn (x₁ [= d₁], …, xₙ [= dₙ]) -> t]: a function of a parameter
          list (issue #2). A default is evaluated at each call, in the scope
          of the parameters before it. Called with an argument record
          ({!Types.args_label}). *)

and param = { name : string; kind : Types.pkind; default : term option }

(** A top-level program item. *)
type item =
  | Decl of bool * string * term  (** [let rec? x = t] (generalized) *)
  | Expr of term

let rec show = function
  | Lit n -> string_of_int n
  | Var x -> x
  | Lam (x, t) -> Printf.sprintf "(fun %s -> %s)" x (show t)
  | App (f, a) -> Printf.sprintf "(%s %s)" (show f) (show a)
  | Rcd fs ->
      "{"
      ^ String.concat "; " (List.map (fun (n, t) -> n ^ " = " ^ show t) fs)
      ^ "}"
  | Sel (t, n) -> show t ^ "." ^ n
  | SelOr (t, n, d) -> Printf.sprintf "(%s.%s ?? %s)" (show t) n (show d)
  | Ext (t, fs) ->
      show t ^ " with {"
      ^ String.concat "; " (List.map (fun (n, t) -> n ^ " = " ^ show t) fs)
      ^ "}"
  | Fn (ps, t) ->
      let param p =
        p.name ^ match p.default with Some d -> " = " ^ show d | None -> ""
      in
      Printf.sprintf "(fn %s -> %s)"
        (Types.show_params (List.map (fun p -> (p.kind, param p)) ps))
        (show t)
  | If (c, a, b) -> Printf.sprintf "(if %s then %s else %s)" (show c) (show a) (show b)
  | Let (r, x, s, t) ->
      Printf.sprintf "(let %s%s = %s in %s)"
        (if r then "rec " else "")
        x (show s) (show t)
