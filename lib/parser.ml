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
    sel     ::= atom { '.' ident | 'with' '{' [ field { ';' field } [';'] ] '}' }
    atom    ::= int | ident | '(' expr ')' | '{' [ field { ';' field } [';'] ] '}'
    field   ::= ident '=' expr
    v}

    The fields of a [with] have distinct labels.

    [let f x y = e] is sugar for [let f = fun x -> fun y -> e], and
    [if c then a else b] for [if c a b]. Line comments start with [//]. *)

open Syntax

exception Parse_error of string

type token =
  | INT of int
  | IDENT of string
  | FUN | LET | REC | IN | IF | THEN | ELSE | WITH
  | ARROW | EQ | SEMI | DOT
  | LPAREN | RPAREN | LBRACE | RBRACE
  | EOF

let show_token = function
  | INT n -> string_of_int n
  | IDENT s -> s
  | FUN -> "fun" | LET -> "let" | REC -> "rec" | IN -> "in"
  | IF -> "if" | THEN -> "then" | ELSE -> "else" | WITH -> "with"
  | ARROW -> "->" | EQ -> "=" | SEMI -> ";" | DOT -> "."
  | LPAREN -> "(" | RPAREN -> ")" | LBRACE -> "{" | RBRACE -> "}"
  | EOF -> "end of input"

let keyword = function
  | "fun" -> Some FUN | "let" -> Some LET | "rec" -> Some REC
  | "in" -> Some IN | "if" -> Some IF | "then" -> Some THEN
  | "else" -> Some ELSE | "with" -> Some WITH | _ -> None

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
    let continue = ref true in
    while !continue do
      match peek () with
      | DOT -> advance (); t := Sel (!t, ident ())
      | WITH ->
          advance ();
          (match atom () with
           | Rcd fs ->
               (* a label may be set once: which binding would win is
                  ambiguous (the Lean model takes the labels as distinct) *)
               let rec dup = function
                 | [] -> ()
                 | (n, _) :: rest ->
                     if List.mem_assoc n rest then
                       fail (Printf.sprintf "label '%s' set twice in 'with'" n);
                     dup rest
               in
               dup fs;
               t := Ext (!t, fs)
           | _ -> fail "expected '{' after 'with'")
      | _ -> continue := false
    done;
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

(** {1 Type syntax}

    Parses user-facing types in the notation printed by {!Types.show_typ}:

    {v
    ty    ::= arrow [ 'as' tyvar ]
    arrow ::= union [ '->' arrow ]
    union ::= inter { ('∨' | '|') inter }
    inter ::= atom { ('∧' | '&') atom }
    atom  ::= tyvar | ident | 'Abs' | '⊤' | 'top' | '⊥' | 'bot' | '(' ty ')'
            | '{' [ field { ',' field } ] [ '|' ty ] '}'
    field ::= ident ':' ty
    v}

    Type variables are written ['a], ['b1], ... Inside braces, ['|'] starts
    the row tail, so a union in a field type must use ['∨'] or parentheses;
    elsewhere ['|'] is an ASCII spelling of ['∨']. [Abs] is the absent field
    (or the top row in tail position). *)

type ty_token =
  | T_VAR of string
  | T_IDENT of string
  | T_ARROW | T_OR | T_BAR | T_AND | T_TOP | T_BOT | T_AS
  | T_LPAREN | T_RPAREN | T_LBRACE | T_RBRACE | T_COLON | T_COMMA
  | T_EOF

let show_ty_token = function
  | T_VAR v -> v
  | T_IDENT s -> s
  | T_ARROW -> "->" | T_OR -> "∨" | T_BAR -> "|" | T_AND -> "∧" | T_TOP -> "⊤" | T_BOT -> "⊥"
  | T_AS -> "as" | T_LPAREN -> "(" | T_RPAREN -> ")" | T_LBRACE -> "{"
  | T_RBRACE -> "}" | T_COLON -> ":" | T_COMMA -> "," | T_EOF -> "end of input"

let tokenize_type (src : string) : (ty_token * int) array =
  let n = String.length src in
  let toks = ref [] in
  let is_id_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' in
  let is_id c = is_id_start c || (c >= '0' && c <= '9') || c = '\'' in
  let has i s = i + String.length s <= n && String.sub src i (String.length s) = s in
  let rec loop i =
    if i >= n then toks := (T_EOF, i) :: !toks
    else
      let emit t len = toks := (t, i) :: !toks; loop (i + len) in
      let ident_end j = let j = ref j in while !j < n && is_id src.[!j] do incr j done; !j in
      match src.[i] with
      | ' ' | '\t' | '\n' | '\r' -> loop (i + 1)
      | '-' when has i "->" -> emit T_ARROW 2
      | '|' -> emit T_BAR 1
      | '&' -> emit T_AND 1
      | '(' -> emit T_LPAREN 1
      | ')' -> emit T_RPAREN 1
      | '{' -> emit T_LBRACE 1
      | '}' -> emit T_RBRACE 1
      | ':' -> emit T_COLON 1
      | ',' -> emit T_COMMA 1
      | _ when has i "∨" -> emit T_OR (String.length "∨")
      | _ when has i "∧" -> emit T_AND (String.length "∧")
      | _ when has i "⊤" -> emit T_TOP (String.length "⊤")
      | _ when has i "⊥" -> emit T_BOT (String.length "⊥")
      | '\'' when i + 1 < n && is_id_start src.[i + 1] ->
          let j = ident_end (i + 1) in
          emit (T_VAR (String.sub src i (j - i))) (j - i)
      | c when is_id_start c -> (
          let j = ident_end i in
          match String.sub src i (j - i) with
          | "as" -> emit T_AS 2
          | "top" -> emit T_TOP 3
          | "bot" -> emit T_BOT 3
          | s -> emit (T_IDENT s) (j - i))
      | c -> raise (Parse_error (Printf.sprintf "type, offset %d: unexpected character '%c'" i c))
  in
  loop 0;
  Array.of_list (List.rev !toks)

let parse_type (src : string) : Types.typ =
  let open Types in
  let toks = tokenize_type src in
  let p = ref 0 in
  let peek () = fst toks.(!p) in
  let advance () = if !p < Array.length toks - 1 then incr p in
  let fail msg =
    raise (Parse_error (Printf.sprintf "type, offset %d: %s (at '%s')" (snd toks.(!p)) msg (show_ty_token (peek ()))))
  in
  let expect t = if peek () = t then advance () else fail ("expected '" ^ show_ty_token t ^ "'") in
  (* [bar]: whether ASCII '|' means union here (not directly inside braces) *)
  let rec ty ?(bar = true) () =
    let t = arrow bar in
    match peek () with
    | T_AS -> (
        advance ();
        match peek () with
        | T_VAR v -> advance (); RecursiveType (v, t)
        | _ -> fail "expected type variable after 'as'")
    | _ -> t
  and arrow bar =
    let l = union bar in
    match peek () with T_ARROW -> advance (); FunctionType (l, arrow bar) | _ -> l
  and union bar =
    let t = ref (inter ()) in
    while peek () = T_OR || (bar && peek () = T_BAR) do advance (); t := Union (!t, inter ()) done;
    !t
  and inter () =
    let t = ref (atom ()) in
    while peek () = T_AND do advance (); t := Inter (!t, atom ()) done;
    !t
  and atom () =
    match peek () with
    | T_VAR v -> advance (); TypeVariable v
    | T_IDENT "Abs" -> advance (); Absent
    | T_IDENT s -> advance (); PrimitiveType s
    | T_TOP -> advance (); Top
    | T_BOT -> advance (); Bot
    | T_LPAREN -> advance (); let t = ty () in expect T_RPAREN; t
    | T_LBRACE ->
        advance ();
        let rec fields () =
          match peek () with
          | T_IDENT n ->
              advance ();
              expect T_COLON;
              let t = ty ~bar:false () in
              if peek () = T_COMMA then (advance (); (n, t) :: fields ()) else [ (n, t) ]
          | _ -> []
        in
        let fs = fields () in
        let tail = if peek () = T_BAR then (advance (); ty ()) else Absent in
        expect T_RBRACE;
        RecordType (fs, tail)
    | _ -> fail "expected type"
  in
  let t = ty () in
  if peek () <> T_EOF then fail "unexpected input after type";
  t
