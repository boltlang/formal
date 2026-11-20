(** Hand-written lexer and recursive-descent parser.

    {v
    program ::= { item }
    item    ::= 'let' ['rec'] ident [ params ] '=' expr     -- top-level, no 'in'
              | expr
    expr    ::= 'fn' params '->' expr
              | 'let' ['rec'] ident [ params ] '=' expr 'in' expr
              | 'if' expr 'then' expr 'else' expr
              | post [ '??' expr ]
    post    ::= atom { '.' ident | 'with' record | args }
    atom    ::= int | ident | '(' expr ')' | record
    record  ::= '{' [ field { ';' field } [';'] ] '}'
    field   ::= ident '=' expr
    params  ::= '(' [ param { ',' param } [','] ] ')'
    param   ::= ident [ '=' expr ] | '/' | '*'
    args    ::= '(' [ arg { ',' arg } [','] ] ')'
    arg     ::= expr | ident '=' expr
    v}

    Every function takes a parameter list and every call passes an argument
    list (issue #2); parentheses after a term are always a call. The
    parameters before a [/] are positional-only, those after a [*]
    keyword-only, the others can be passed either way. Among the parameters
    that can be passed by position, those with a default come last. In a
    call, positional arguments come first.

    [let f(ps) = e] is sugar for [let f = fn (ps) -> e], and
    [if c then a else b] for the core application [if c a b]. A call
    [f(a, b, x = c)] is the application of [f] to the argument record
    [{* = [a, b]; x = c}] (the label [*] is {!Types.args_label}; a list is
    nested records [{hd; tl}] ending in [{}]).

    The fields of a [with] have distinct labels. The left operand of [??]
    is a field selection: [r.a ?? d] is the field [a] of [r] if it is
    present, and [d] otherwise. Line comments start with [//]. *)

open Syntax

type pkind = Types.pkind = PosOnly | Either | KwOnly

exception Parse_error of string

type token =
  | INT of int
  | IDENT of string
  | FN | LET | REC | IN | IF | THEN | ELSE | WITH
  | ARROW | EQ | SEMI | DOT | QQ | COMMA | SLASH | STAR
  | LPAREN | RPAREN | LBRACE | RBRACE
  | EOF

let show_token = function
  | INT n -> string_of_int n
  | IDENT s -> s
  | FN -> "fn" | LET -> "let" | REC -> "rec" | IN -> "in"
  | IF -> "if" | THEN -> "then" | ELSE -> "else" | WITH -> "with"
  | ARROW -> "->" | EQ -> "=" | SEMI -> ";" | DOT -> "." | QQ -> "??"
  | COMMA -> "," | SLASH -> "/" | STAR -> "*"
  | LPAREN -> "(" | RPAREN -> ")" | LBRACE -> "{" | RBRACE -> "}"
  | EOF -> "end of input"

let keyword = function
  | "fn" -> Some FN | "let" -> Some LET | "rec" -> Some REC
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
      | '?' when i + 1 < n && src.[i + 1] = '?' -> emit QQ 2
      | '=' -> emit EQ 1
      | ';' -> emit SEMI 1
      | '.' -> emit DOT 1
      | ',' -> emit COMMA 1
      | '/' -> emit SLASH 1
      | '*' -> emit STAR 1
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

(** The argument record of a call. *)
let args_record (pos : term list) (named : (string * term) list) : term =
  let rec list = function
    | [] -> Rcd []
    | t :: ts -> Rcd [ ("hd", t); ("tl", list ts) ]
  in
  Rcd ((Types.args_label, list pos) :: named)

let parse_program (src : string) : item list =
  let toks = tokenize src in
  let p = ref 0 in
  let peek () = fst toks.(!p) in
  let peek2 () = if !p + 1 < Array.length toks then fst toks.(!p + 1) else EOF in
  let advance () = if !p < Array.length toks - 1 then incr p in
  let fail msg =
    let l, c = snd toks.(!p) in
    raise (Parse_error (Printf.sprintf "%d:%d: %s (at '%s')" l c msg (show_token (peek ()))))
  in
  let expect t = if peek () = t then advance () else fail ("expected '" ^ show_token t ^ "'") in
  let ident () = match peek () with IDENT s -> advance (); s | _ -> fail "expected identifier" in
  (* a comma-separated list in parentheses, with an optional trailing comma *)
  let parens item =
    expect LPAREN;
    let rec go () =
      if peek () = RPAREN then (advance (); [])
      else
        let x = item () in
        match peek () with
        | COMMA -> advance (); x :: go ()
        | RPAREN -> advance (); [ x ]
        | _ -> fail "expected ',' or ')'"
    in
    go ()
  in
  let rec expr () =
    match peek () with
    | FN ->
        advance ();
        let ps = params () in
        expect ARROW;
        Fn (ps, expr ())
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
    | _ -> (
        let t = post () in
        match (peek (), t) with
        | QQ, Sel (obj, name) ->
            advance ();
            SelOr (obj, name, expr ())
        | QQ, _ -> fail "the left operand of '??' must be a field selection"
        | _ -> t)
  and let_head () =
    expect LET;
    let isrec = peek () = REC in
    if isrec then advance ();
    let name = ident () in
    let ps = if peek () = LPAREN then Some (params ()) else None in
    expect EQ;
    let rhs = expr () in
    (isrec, name, match ps with Some ps -> Fn (ps, rhs) | None -> rhs)
  (* a parameter list, with its markers checked as in Python *)
  and params () =
    let items =
      parens (fun () ->
          match peek () with
          | SLASH -> advance (); `Slash
          | STAR -> advance (); `Star
          | _ ->
              let name = ident () in
              let default = if peek () = EQ then (advance (); Some (expr ())) else None in
              `Param (name, default))
    in
    let slash = List.mem `Slash items and star = List.mem `Star items in
    let rec go kind seen_default = function
      | [] -> []
      | `Slash :: rest ->
          if kind <> PosOnly then fail "'/' must come before '*', and only once";
          go Either seen_default rest
      | `Star :: rest ->
          if kind = KwOnly then fail "'*' may appear only once";
          if not (List.exists (function `Param _ -> true | _ -> false) rest) then
            fail "'*' must be followed by a parameter";
          go KwOnly seen_default rest
      | `Param (name, default) :: rest ->
          if kind <> KwOnly && seen_default && default = None then
            fail
              (Printf.sprintf
                 "parameter %s has no default but follows one that has" name);
          let seen_default = seen_default || (kind <> KwOnly && default <> None) in
          { name; kind; default } :: go kind seen_default rest
    in
    (match items with `Slash :: _ -> fail "'/' must follow a parameter" | _ -> ());
    ignore star;
    let ps = go (if slash then PosOnly else Either) false items in
    let rec dup = function
      | [] -> ()
      | q :: rest ->
          if List.exists (fun r -> r.name = q.name) rest then
            fail (Printf.sprintf "parameter %s is given twice" q.name);
          dup rest
    in
    dup ps;
    ps
  and args () =
    let items =
      parens (fun () ->
          match (peek (), peek2 ()) with
          | IDENT n, EQ -> advance (); advance (); `Named (n, expr ())
          | _ -> `Pos (expr ()))
    in
    let rec split = function
      | [] -> ([], [])
      | `Pos t :: rest ->
          let pos, named = split rest in
          (t :: pos, named)
      | `Named (n, t) :: rest ->
          if List.exists (function `Pos _ -> true | _ -> false) rest then
            fail "a positional argument follows a named one";
          let _, named = split rest in
          if List.mem_assoc n named then fail (Printf.sprintf "argument %s is given twice" n);
          ([], (n, t) :: named)
    in
    let pos, named = split items in
    args_record pos named
  and post () =
    let t = ref (atom ()) in
    let continue = ref true in
    while !continue do
      match peek () with
      | DOT -> advance (); t := Sel (!t, ident ())
      | LPAREN -> t := App (!t, args ())
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
  (* an item ends where the next one starts: without application by
     juxtaposition, [f x] would otherwise be the two items [f] and [x] *)
  let next () =
    match peek () with
    | LET | EOF -> ()
    | _ -> fail "expected 'let' or end of input (a call needs parentheses: f(x))"
  in
  let rec items () =
    match peek () with
    | EOF -> []
    | LET -> (
        let isrec, name, rhs = let_head () in
        match peek () with
        | IN ->
            advance ();
            let body = expr () in
            next ();
            Expr (Let (isrec, name, rhs, body)) :: items ()
        | _ ->
            next ();
            Decl (isrec, name, rhs) :: items ())
    | _ ->
        let e = expr () in
        next ();
        Expr e :: items ()
  in
  items ()

(** {1 Type syntax}

    Parses user-facing types in the notation printed by {!Types.show_typ}:

    {v
    ty    ::= arrow [ 'as' tyvar ]
    arrow ::= union [ '->' arrow ]
    union ::= inter { ('∨' | '|') inter }
    inter ::= atom { ('∧' | '&') atom }
    atom  ::= base { '?' }
    base  ::= tyvar | ident | 'Abs' | 'Missing' | '⊤' | 'top' | '⊥' | 'bot'
            | '(' ty ')'
            | '{' [ field { ',' field } ] [ [','] '..' | '|' ty ] '}'
    field ::= ident ['?'] ':' ty
    v}

    Type variables are written ['a], ['b1], ... Inside braces, ['|'] starts
    the row tail, so a union in a field type must use ['∨'] or parentheses;
    elsewhere ['|'] is an ASCII spelling of ['∨'].

    A record type is closed unless it says otherwise: [{x: int}] has no
    other fields, [{x: int, ..}] may have any, and [{x: int | 'a}] has those
    of the row ['a]. [x?: τ] is an optional field ([τ?] away from a field),
    [Missing] the field that is definitely absent, and [Abs] the top field
    (or the top row in tail position). *)

type ty_token =
  | T_VAR of string
  | T_IDENT of string
  | T_ARROW | T_OR | T_BAR | T_AND | T_TOP | T_BOT | T_AS
  | T_LPAREN | T_RPAREN | T_LBRACE | T_RBRACE | T_COLON | T_COMMA
  | T_QUESTION | T_DOTDOT | T_SLASH | T_STAR | T_LBRACK | T_RBRACK
  | T_EOF

let show_ty_token = function
  | T_VAR v -> v
  | T_IDENT s -> s
  | T_ARROW -> "->" | T_OR -> "∨" | T_BAR -> "|" | T_AND -> "∧" | T_TOP -> "⊤" | T_BOT -> "⊥"
  | T_AS -> "as" | T_LPAREN -> "(" | T_RPAREN -> ")" | T_LBRACE -> "{"
  | T_RBRACE -> "}" | T_COLON -> ":" | T_COMMA -> "," | T_QUESTION -> "?"
  | T_DOTDOT -> ".." | T_SLASH -> "/" | T_STAR -> "*" | T_LBRACK -> "[" | T_RBRACK -> "]"
  | T_EOF -> "end of input"

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
      | '?' -> emit T_QUESTION 1
      | '/' -> emit T_SLASH 1
      | '*' -> emit T_STAR 1
      | '[' -> emit T_LBRACK 1
      | ']' -> emit T_RBRACK 1
      | '.' when has i ".." -> emit T_DOTDOT 2
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
  let peek_at i = if !p + i < Array.length toks then fst toks.(!p + i) else T_EOF in
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
    let t = ref (base ()) in
    while peek () = T_QUESTION do advance (); t := Optional !t done;
    !t
  and base () =
    match peek () with
    | T_VAR v -> advance (); TypeVariable v
    | T_IDENT "Abs" -> advance (); AbsType
    | T_IDENT "Missing" -> advance (); MissingType
    | T_IDENT s -> advance (); PrimitiveType s
    | T_TOP -> advance (); Top
    | T_BOT -> advance (); Bot
    | T_LPAREN -> advance (); paren_or_sig ()
    | T_LBRACK ->
        advance ();
        let rec elems () =
          if peek () = T_RBRACK then (advance (); [])
          else
            let t = ty () in
            match peek () with
            | T_COMMA -> advance (); t :: elems ()
            | T_RBRACK -> advance (); [ t ]
            | _ -> fail "expected ',' or ']'"
        in
        List.fold_right (fun t l -> RecordType ([ ("hd", t); ("tl", l) ], NilType)) (elems ())
          (RecordType ([], NilType))
    | T_LBRACE ->
        advance ();
        let rec fields () =
          match peek () with
          | (T_IDENT _ | T_STAR) as tok ->
              advance ();
              let n = match tok with T_IDENT n -> n | _ -> args_label in
              let optional = peek () = T_QUESTION in
              if optional then advance ();
              expect T_COLON;
              let t = ty ~bar:false () in
              let f = (n, if optional then Optional t else t) in
              if peek () = T_COMMA then (advance (); f :: fields ()) else [ f ]
          | _ -> []
        in
        let fs = fields () in
        let tail =
          match peek () with
          | T_BAR -> advance (); ty ()
          | T_DOTDOT -> advance (); AbsType
          | _ -> NilType
        in
        expect T_RBRACE;
        RecordType (fs, tail)
    | _ -> fail "expected type"
  (* after '(': a parenthesized type, or a parameter list *)
  and paren_or_sig () =
    let named () =
      match (peek (), peek_at 1, peek_at 2) with
      | T_IDENT _, T_COLON, _ | T_IDENT _, T_QUESTION, T_COLON -> true
      | _ -> false
    in
    let item () =
      match peek () with
      | T_SLASH -> advance (); `Slash
      | T_STAR -> advance (); `Star
      | T_IDENT n when named () ->
          advance ();
          let opt = peek () = T_QUESTION in
          if opt then advance ();
          expect T_COLON;
          `Named (n, ty (), opt)
      | _ -> `Unnamed (ty ())
    in
    let rec items () =
      if peek () = T_RPAREN then (advance (); [])
      else
        let x = item () in
        match peek () with
        | T_COMMA -> advance (); x :: items ()
        | T_RPAREN -> advance (); [ x ]
        | _ -> fail "expected ',' or ')'"
    in
    match items () with
    | [ `Unnamed t ] -> t
    | items ->
        let slash = List.mem `Slash items in
        let rec go kind i = function
          | [] -> []
          | `Slash :: rest -> go Either i rest
          | `Star :: rest -> go KwOnly i rest
          | `Unnamed t :: rest ->
              if kind <> PosOnly then fail "a parameter without a name must be positional-only";
              let t, opt = match t with Optional t -> (t, true) | t -> (t, false) in
              { tname = "#" ^ string_of_int i; tkind = kind; tty = t; topt = opt } :: go kind (i + 1) rest
          | `Named (n, t, opt) :: rest ->
              { tname = n; tkind = kind; tty = t; topt = opt } :: go kind (i + 1) rest
        in
        SigType (go (if slash then PosOnly else Either) 0 items)
  in
  let t = ty () in
  if peek () <> T_EOF then fail "unexpected input after type";
  t
