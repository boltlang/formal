(* Usage:
     simplesub [OPTIONS] [FILE]        type-check a program file (or stdin)
     simplesub [OPTIONS] -e SOURCE     type-check a program given inline
     simplesub --compare TYPE1 TYPE2   relate two type schemes by generality

   Options:
     --raw          print coalesced types without simplification (Sec. 3.3)
     --rectypes     allow structural recursive types, as in the paper (by
                    default a type variable may not reach itself through a
                    type constructor)
     --expect TYPE  check that each inferred type is equivalent to TYPE
     --self-check   check that each simplified type is equivalent to the raw
                    coalesced type (i.e. that simplification is sound)

   Exit status: 0 on success, 1 on type errors or failed checks, 2 on usage
   or parse errors. *)

open Simplesub

let usage () =
  prerr_endline
    "usage: simplesub [--raw] [--rectypes] [--expect TYPE] [--self-check] [FILE | -e SOURCE]\n\
    \       simplesub --compare TYPE1 TYPE2";
  exit 2

let parse_type_or_exit s =
  try Parser.parse_type s
  with Parser.Parse_error msg ->
    prerr_endline ("parse error: " ^ msg);
    exit 2

let relate_or_exit t1 t2 =
  try Subsume.relate t1 t2 with
  | Subsume.Not_polar msg ->
      prerr_endline ("error: not a polar type: " ^ msg);
      exit 2
  | Subsume.Unsupported what ->
      prerr_endline ("error: subsumption does not support " ^ what ^ " yet");
      exit 2

let run ~simplify ~expect ~self_check src =
  match Parser.parse_program src with
  | exception Parser.Parse_error msg ->
      prerr_endline ("parse error: " ^ msg);
      exit 2
  | items ->
      let failed = ref false in
      let fail fmt = failed := true; Printf.printf fmt in
      List.iter
        (fun { name; outcome } ->
          let lhs = match name with Some n -> "let " ^ n | None -> "-" in
          match outcome with
          | Error msg -> fail "%s : type error: %s\n" lhs msg
          | Ok st ->
              let ty = display ~simplify st in
              Printf.printf "%s : %s\n" lhs (Types.show_typ ty);
              Option.iter
                (fun exp ->
                  match relate_or_exit ty exp with
                  | Subsume.Equivalent -> ()
                  | r ->
                      fail "  expected %s, but inferred type is %s\n"
                        (Types.show_typ exp) (Subsume.show_relation r))
                expect;
              if self_check then
                let raw = display ~simplify:false st
                and simp = display ~simplify:true st in
                match Subsume.relate simp raw with
                | Subsume.Equivalent -> ()
                | r ->
                    fail "  self-check failed: simplified %s is %s raw %s\n"
                      (Types.show_typ simp) (Subsume.show_relation_to r)
                      (Types.show_typ raw)
                | exception Subsume.Unsupported what ->
                    Printf.printf "  (self-check skipped: %s)\n" what
                | exception Subsume.Not_polar msg ->
                    fail "  self-check failed: not a polar type: %s\n" msg)
        (infer_program items);
      if !failed then exit 1

let () =
  let rec parse ((simplify, expect, self_check, src) as acc) = function
    | "--raw" :: rest -> parse (false, expect, self_check, src) rest
    | "--self-check" :: rest -> parse (simplify, expect, true, src) rest
    | "--rectypes" :: rest ->
        Typer.allow_recursive := true;
        parse acc rest
    | "--expect" :: t :: rest ->
        parse (simplify, Some (parse_type_or_exit t), self_check, src) rest
    | "-e" :: s :: rest when src = None -> parse (simplify, expect, self_check, Some s) rest
    | [ file ] when src = None && String.length file > 0 && file.[0] <> '-' ->
        (simplify, expect, self_check,
         Some (In_channel.with_open_text file In_channel.input_all))
    | [] -> acc
    | _ -> usage ()
  in
  match Array.to_list Sys.argv |> List.tl with
  | [ "--compare"; t1; t2 ] ->
      let t1 = parse_type_or_exit t1 and t2 = parse_type_or_exit t2 in
      Printf.printf "%s is %s %s\n" (Types.show_typ t1)
        (Subsume.show_relation_to (relate_or_exit t1 t2))
        (Types.show_typ t2)
  | args ->
      let simplify, expect, self_check, src = parse (true, None, false, None) args in
      let src = match src with Some s -> s | None -> In_channel.input_all stdin in
      run ~simplify ~expect ~self_check src
