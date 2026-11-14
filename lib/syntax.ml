(** Term syntax (paper, Fig. 4). *)

type term =
  | Lit of int  (** [27] *)
  | Var of string  (** [x] *)
  | Lam of string * term  (** [fun x -> t] *)
  | App of term * term  (** [s t] *)
  | Rcd of (string * term) list  (** [{a = 0; b = true}] *)
  | Sel of term * string  (** [t.a] *)
  | Let of bool * string * term * term  (** [let rec? x = s in t] *)

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
  | Let (r, x, s, t) ->
      Printf.sprintf "(let %s%s = %s in %s)"
        (if r then "rec " else "")
        x (show s) (show t)
