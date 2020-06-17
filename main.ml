open Dtlclib
open Typecheck

exception NotDefinedError of string
exception RedefError of string

let get_lexbuf () =
  let lexbuf = Lexing.from_channel stdin in
  let () = lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with Lexing.pos_fname = "<stdin>" } in
  lexbuf

let () =
  let lexbuf = get_lexbuf () in
  let rec loop types abbrevs =
    match Parser.main Lexer.token lexbuf with
    | None -> let _ = print_endline "Done" in types, abbrevs
    | Some (Def (x, e)) ->
        begin match Syntax.Gamma.find_opt x abbrevs with
              | None -> ()
              | Some _ -> raise (RedefError ("Re-defining " ^ x))
        end;
        begin match Syntax.Gamma.find_opt x types with
              | None -> raise (NotDefinedError (Printf.sprintf "%s is not claimed yet" x))
              | Some ty -> 
                let _ = type_check abbrevs (Syntax.Gamma.remove x types) e ty in
                (* Printf.printf "%s = %s\n%!" x (Syntax.show_raw_expr e); *)
                loop types (Syntax.Gamma.add x e abbrevs)
        end
    | Some (Claim (x, t)) ->
        begin match Syntax.Gamma.find_opt x types with
              | None -> 
                  print_endline (Printf.sprintf "Claim %s : %s" x (Syntax.show_raw_expr t));
                  loop (Syntax.Gamma.add x t types) abbrevs
              | Some _ -> raise (RedefError ("Re-claiming " ^ x))
        end
    | Some (CmdNormalize e) ->
       print_endline (Printf.sprintf "Normalize %s : %s" (Syntax.show_raw_expr e) (Syntax.show_raw_expr (Typecheck.normalize abbrevs e)));
       loop types abbrevs
  in
  try
    let claimed, proved = loop Syntax.Gamma.empty Syntax.Gamma.empty in
    let not_proved = Syntax.Gamma.bindings (Syntax.Gamma.filter 
                                              (fun k -> fun _ -> 
                                                match Syntax.Gamma.find_opt k proved with
                                                | None -> true
                                                | _    -> false) claimed) in
    if List.length not_proved > 0 
    then let _ = List.map (fun e -> print_endline (Printf.sprintf "%s is claimed but not defined" (fst e))) not_proved in 
         ()
  with
  (* lexical and syntax errors are unrecoverable, so catch them outside the loop. *)
  | Lexer.Error (pos, msg) -> Printf.printf "%s: lexical error: %s\n%!" (Syntax.string_of_lex_pos pos) msg; exit 1
  | Parser.Error -> Printf.printf "%s: parse error while looking at %s\n%!" (Syntax.string_of_lex_pos (Lexing.lexeme_start_p lexbuf)) (Lexing.lexeme lexbuf); exit 1
  | Typecheck.TypeError msg -> Printf.printf "TypeError : %s\n" msg; exit 1
  | NotDefinedError msg -> print_endline ("NotDefinedError: " ^ msg); exit 1
  | RedefError msg -> print_endline ("RedefineError: " ^ msg); exit 1
    