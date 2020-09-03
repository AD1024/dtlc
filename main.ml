open Dtlclib
open Typecheck

exception NotDefinedError of string
exception RedefError of string
exception ZipError of string

let get_lexbuf () =
  let lexbuf = Lexing.from_channel stdin in
  let () = lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with Lexing.pos_fname = "<stdin>" } in
  lexbuf

let elim_name dtype = dtype ^ "_elim"

let rec num_dtype_occurence dtype expr =
  match expr with
    | Syntax.Var ty -> if ty = dtype then 0 
                       else (raise (Typecheck.TypeCheckError 
                                      (Printf.sprintf "%s is not a valid return type of a constructor"
                                          (Syntax.show_raw_expr expr))))
    | Syntax.Pi ((_, ty, _), e) -> (if ty = Var dtype then 1 else 0) + num_dtype_occurence dtype e
    | _ -> raise (Typecheck.TypeCheckError (Printf.sprintf "Oof %s seems problematic..." (Syntax.show_raw_expr expr)))

let rec get_type_decl_var_name avoid_name cnt =
  if cnt == 0 then []
  else let vname = (Syntax.fresh avoid_name "x") 
       in  vname :: (get_type_decl_var_name (Syntax.StringSet.add vname avoid_name) (cnt - 1))

let get_ih_types args =
  List.map (fun (name : string) -> Syntax.App (Var "goal", Var name)) args

let wrap_call fname args =
  List.fold_left (fun (expr : Syntax.raw_expr) -> 
                    fun (x : string) -> Syntax.App (expr, Var x)) (Var fname) args

(* let rec zip_list xs ys =
  match (xs, ys) with
    | ([], []) -> []
    | (x :: xs, y :: ys) -> (x, y) :: (zip_list xs ys)
    | _ -> (raise (ZipError "Zipping lists with different lengths")) *)

let wrap_ind_hypothesis args arg_type ih_types ret_type =
  let result = List.fold_left 
                (fun (body : Syntax.raw_expr) ->
                  fun (ih : Syntax.raw_expr) ->
                    Syntax.Pi (("_", ih, Syntax.Explicit), body)) ret_type ih_types in
  List.fold_left 
      (fun (body : Syntax.raw_expr) ->
        fun (arg : string) ->
          Syntax.Pi ((arg, Var arg_type, Syntax.Explicit), body)) result args
  

let get_ind_hypothesis dtype constructor avoid_name decl_type =
  (* let _ = Printf.printf "Going For %s : %s\n" constructor (Syntax.show_raw_expr decl_type) in *)
  let num_occ = num_dtype_occurence dtype decl_type in
  (* let _ = Printf.printf "NumOcc : %d\n" num_occ in *)
  if num_occ == 0 then Syntax.App (Var "goal", Var constructor) else
  let type_decl_names = get_type_decl_var_name avoid_name num_occ in
  let subgoal = Syntax.App (Var "goal", wrap_call constructor type_decl_names) in
  (* let _ = Printf.printf "Subgoal : %s\n" (Syntax.show_raw_expr subgoal) in  *)
  let ih_types = get_ih_types type_decl_names in
  wrap_ind_hypothesis type_decl_names dtype ih_types subgoal

let calculate_elim (dtype : string) (constrs : Syntax.binding list) : Syntax.raw_expr =
  let var_set = Syntax.StringSet.empty in
  let var_name = Syntax.fresh var_set "x" in
  let var_set = Syntax.StringSet.add var_name var_set in
  let goal = Syntax.Pi ((var_name, Var dtype, Explicit), Syntax.App (Var "goal", Var var_name)) in
  let result = List.fold_left 
                (fun (body : Syntax.raw_expr) ->
                  fun (pi : Syntax.binding) ->
                    match pi with
                      | Syntax.Claim (cname, ty) -> 
                          Syntax.Pi (("_", get_ind_hypothesis dtype cname var_set ty, Syntax.Explicit), body)
                      | _ -> raise (Typecheck.TypeCheckError 
                                      (Printf.sprintf "%s is not a valid type definition"
                                      (Syntax.show_binding pi)))) goal constrs in
  Syntax.Pi (("goal", (Syntax.Pi (("_", Var dtype, Syntax.Explicit), Syntax.Type None)), Syntax.Explicit), result)

let () =
  let lexbuf = get_lexbuf () in
  let rec loop types abbrevs elims =
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
                let _ = Typecheck.meta_variable_count := 0 in
                let _ = type_check abbrevs (Syntax.Gamma.remove x types) Syntax.Gamma.empty e ty in
                (* Printf.printf "%s = %s\n%!" x (Syntax.show_raw_expr e); *)
                loop types (Syntax.Gamma.add x e abbrevs) elims
        end
    | Some (Claim (x, t)) ->
        begin match Syntax.Gamma.find_opt x types with
              | None -> 
                  print_endline (Printf.sprintf "Claim %s : %s" x (Syntax.show_raw_expr t));
                  loop (Syntax.Gamma.add x t types) abbrevs elims
              | Some _ -> raise (RedefError ("Re-claiming " ^ x))
        end
    | Some (CmdNormalize e) ->
       print_endline (Printf.sprintf "Normalize %s : %s" (Syntax.show_raw_expr e) (Syntax.show_raw_expr (Typecheck.normalize abbrevs e)));
       loop types abbrevs elims
    | Some (TypeDecl (name, constrs)) ->
        let eliminator = elim_name name in
        let elim_impl = calculate_elim name constrs in
        print_endline (Printf.sprintf "Definied %s with eliminator %s" name (Syntax.show_raw_expr elim_impl));
        loop (Syntax.Gamma.add name (Syntax.Type None) types) abbrevs (Syntax.Gamma.add eliminator elim_impl elims)
  in
  try
    let claimed, proved = loop Syntax.Gamma.empty Syntax.Gamma.empty Syntax.Gamma.empty in
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
    