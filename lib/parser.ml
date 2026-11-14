(** Hand-written lexer and recursive-descent parser.

    {v
    program ::= { item }
    item    ::= 'let' ['rec'] ident { ident } '=' expr     -- top-level, no 'in'
              | expr
    expr    ::= 'fun' ident { ident } '->' expr
              | 'let' ['rec'] ident { ident } '=' expr 'in' expr
              | 'if' expr 'then' expr 'else' expr
              | app
    app     ::= sel { sel } [ fun-or-if-expr ]
    sel     ::= atom { '.' ident }
    atom    ::= int | ident | '(' expr ')' | '{' [ field { ';' field } [';'] ] '}'
    field   ::= ident '=' expr
    v}

    [let f x y = e] is sugar for [let f = fun x -> fun y -> e], and
    [if c then a else b] for [if c a b]. Line comments start with [//]. *)

open Syntax

exception Parse_error of string

type token =
  | INT of int
  | IDENT of string
  | FUN | LET | REC | IN | IF | THEN | ELSE
  | ARROW | EQ | SEMI | DOT
  | LPAREN | RPAREN | LBRACE | RBRACE
  | EOF

let show_token = function
  | INT n -> string_of_int n
  | IDENT s -> s
  | FUN -> "fun" | LET -> "let" | REC -> "rec" | IN -> "in"
  | IF -> "if" | THEN -> "then" | ELSE -> "else"
  | ARROW -> "->" | EQ -> "=" | SEMI -> ";" | DOT -> "."
  | LPAREN -> "(" | RPAREN -> ")" | LBRACE -> "{" | RBRACE -> "}"
  | EOF -> "end of input"

let keyword = function
  | "fun" -> Some FUN | "let" -> Some LET | "rec" -> Some REC
  | "in" -> Some IN | "if" -> Some IF | "then" -> Some THEN
  | "else" -> Some ELSE | _ -> None

(** Tokens paired with their (line, column). *)
let tokenize (src : string) : (token * (int * int)) array =
  let n = String.length src in
  let toks = ref [] in
  let line = ref 1 and bol = ref 0 in
  let pos i = (!line, i - !bol + 1) in
  let is_id_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' in
  let is_id c = is_id_start c || (c >= '0' && c <= '9') || c = '\'' in
  let is_digit c = c >= '0' && c <= '9' in
  let rec loop i =
    if i >= n then toks := (EOF, pos i) :: !toks
    else
      let c = src.[i] in
      let emit t len = toks := (t, pos i) :: !toks; loop (i + len) in
      match c with
      | '\n' -> incr line; bol := i + 1; loop (i + 1)
      | ' ' | '\t' | '\r' -> loop (i + 1)
      | '/' when i + 1 < n && src.[i + 1] = '/' ->
          let j = ref i in
          while !j < n && src.[!j] <> '\n' do incr j done;
          loop !j
      | '-' when i + 1 < n && src.[i + 1] = '>' -> emit ARROW 2
      | '=' -> emit EQ 1
      | ';' -> emit SEMI 1
      | '.' -> emit DOT 1
      | '(' -> emit LPAREN 1
      | ')' -> emit RPAREN 1
      | '{' -> emit LBRACE 1
      | '}' -> emit RBRACE 1
      | c when is_digit c ->
          let j = ref i in
          while !j < n && is_digit src.[!j] do incr j done;
          emit (INT (int_of_string (String.sub src i (!j - i)))) (!j - i)
      | c when is_id_start c ->
          let j = ref i in
          while !j < n && is_id src.[!j] do incr j done;
          let s = String.sub src i (!j - i) in
          emit (match keyword s with Some k -> k | None -> IDENT s) (!j - i)
      | c ->
          let l, col = pos i in
          raise (Parse_error (Printf.sprintf "%d:%d: unexpected character '%c'" l col c))
  in
  loop 0;
  Array.of_list (List.rev !toks)

let parse_program (src : string) : item list =
  let toks = tokenize src in
  let p = ref 0 in
  let peek () = fst toks.(!p) in
  let advance () = if !p < Array.length toks - 1 then incr p in
  let fail msg =
    let l, c = snd toks.(!p) in
    raise (Parse_error (Printf.sprintf "%d:%d: %s (at '%s')" l c msg (show_token (peek ()))))
  in
  let expect t = if peek () = t then advance () else fail ("expected '" ^ show_token t ^ "'") in
  let ident () = match peek () with IDENT s -> advance (); s | _ -> fail "expected identifier" in
  let rec idents () = match peek () with IDENT s -> advance (); s :: idents () | _ -> [] in
  let lams params body = List.fold_right (fun x b -> Lam (x, b)) params body in
  let starts_atom = function INT _ | IDENT _ | LPAREN | LBRACE -> true | _ -> false in
  let rec expr () =
    match peek () with
    | FUN ->
        advance ();
        let params = idents () in
        if params = [] then fail "expected parameter";
        expect ARROW;
        lams params (expr ())
    | LET -> (
        let isrec, name, rhs = let_head () in
        match peek () with
        | IN -> advance (); Let (isrec, name, rhs, expr ())
        | _ -> fail "expected 'in'")
    | IF ->
        advance ();
        let c = expr () in
        expect THEN;
        let a = expr () in
        expect ELSE;
        let b = expr () in
        App (App (App (Var "if", c), a), b)
    | _ -> app ()
  and let_head () =
    expect LET;
    let isrec = peek () = REC in
    if isrec then advance ();
    let name = ident () in
    let params = idents () in
    expect EQ;
    (isrec, name, lams params (expr ()))
  and app () =
    let f = ref (sel ()) in
    while starts_atom (peek ()) do f := App (!f, sel ()) done;
    (* allow a trailing lambda / let / if as the last argument *)
    (match peek () with
     | FUN | IF -> f := App (!f, expr ())
     | _ -> ());
    !f
  and sel () =
    let t = ref (atom ()) in
    while peek () = DOT do advance (); t := Sel (!t, ident ()) done;
    !t
  and atom () =
    match peek () with
    | INT n -> advance (); Lit n
    | IDENT x -> advance (); Var x
    | LPAREN -> advance (); let e = expr () in expect RPAREN; e
    | LBRACE ->
        advance ();
        let rec fields () =
          match peek () with
          | RBRACE -> advance (); []
          | _ ->
              let n = ident () in
              expect EQ;
              let e = expr () in
              (match peek () with
               | SEMI -> advance ()
               | RBRACE -> ()
               | _ -> fail "expected ';' or '}'");
              (n, e) :: fields ()
        in
        Rcd (fields ())
    | _ -> fail "expected expression"
  in
  let rec items () =
    match peek () with
    | EOF -> []
    | LET -> (
        let isrec, name, rhs = let_head () in
        match peek () with
        | IN -> advance (); let body = expr () in Expr (Let (isrec, name, rhs, body)) :: items ()
        | _ -> Decl (isrec, name, rhs) :: items ())
    | _ -> let e = expr () in Expr e :: items ()
  in
  items ()
