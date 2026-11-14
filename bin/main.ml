(* simplesub [FILE]          type-check a program file (or stdin with no FILE)
   simplesub -e SOURCE       type-check a program given on the command line *)

open Simplesub

let run src =
  match Parser.parse_program src with
  | exception Parser.Parse_error msg ->
      prerr_endline ("parse error: " ^ msg);
      exit 2
  | items ->
      let failed = ref false in
      List.iter
        (fun { name; outcome } ->
          let lhs = match name with Some n -> "let " ^ n | None -> "-" in
          match outcome with
          | Ok ty -> Printf.printf "%s : %s\n" lhs (Types.show_typ ty)
          | Error msg ->
              failed := true;
              Printf.printf "%s : type error: %s\n" lhs msg)
        (infer_program items);
      if !failed then exit 1

let () =
  match Array.to_list Sys.argv |> List.tl with
  | [ "-e"; src ] -> run src
  | [ file ] -> run (In_channel.with_open_text file In_channel.input_all)
  | [] -> run (In_channel.input_all stdin)
  | _ ->
      prerr_endline "usage: simplesub [FILE | -e SOURCE]";
      exit 2
