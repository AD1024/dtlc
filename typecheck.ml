open Dtlclib

exception TypeError of string
exception TypeCheckError of string
exception NormalizationError of string
exception UnificaitionError of string

let meta_variable_count = ref 0

let compute e =
    match e with
    | Syntax.App (Lambda (x, _, e1), e2) -> Syntax.subst x e2 e1
    | Fst (Pair (e1, _)) -> e1
    | Snd (Pair (_, e2)) -> e2
    | NatElim (_, e2, _, Zero) -> e2
    | NatElim (e1, e2, (Lambda (x, tx, Lambda (y, ty, e3))), (Succ e4)) -> Syntax.subst x e4 (Syntax.subst y (Syntax.NatElim (e1, e2, (Lambda (x, tx, Lambda (y, ty, e3))), e4)) e3)
    | SumElim(_, (Lambda (x, _, e3)), _, (Inl e)) -> Syntax.subst x e e3
    | SumElim(_, _, (Lambda (x, _, e3)), (Inr e)) -> Syntax.subst x e e3
    | _ -> e

let definitional_eq (e1 : Syntax.raw_expr) (e2 : Syntax.raw_expr) = e1 = compute e2 || e2 = compute e1

let rec normalize sigma (e : Syntax.raw_expr) =
  (* let _ = Printf.printf "normalizing : %s\n" (Syntax.show_raw_expr e) in *)
  match e with
  | Var x ->  begin  match Syntax.Gamma.find_opt x sigma with
                    | None -> e
                    | Some e -> normalize sigma e
              end
  | App (e1, e2) ->   begin let e1' = normalize sigma e1 in
                            let e2' = normalize sigma e2 in
                            match e1' with
                            | Lambda (x, _, e) -> normalize sigma (Syntax.subst x e2' e)
                            | _ -> App (e1', e2')
                      end
  | Lambda (x, t, e) -> Lambda (x, t, normalize sigma e)
  | Pi ((x, e1, at), e2) -> Pi ((x, normalize sigma e1, at), normalize sigma e2)
  | Sigma ((x, e1), e2) -> Sigma ((x, normalize sigma e1), normalize sigma e2)
  | Pair (e1, e2) -> Pair (normalize sigma e1, normalize sigma e2)
  | Sum (e1, e2)     -> Sum (normalize sigma e1, normalize sigma e2)
  | Fst e ->  let e' = normalize sigma e in
              compute (Fst e')
  | Snd e ->  let e' = normalize sigma e in
              compute (Snd e')
  | Inl e -> Inl (normalize sigma e)
  | Inr e -> Inr (normalize sigma e)
  | Succ e -> Succ (normalize sigma e)
  | PropEq (e1, e2) -> PropEq (normalize sigma e1, normalize sigma e2)
  | Refl (e1, e2) -> Refl (normalize sigma e1, normalize sigma e2)
  | NatElim (e1, e2, e3, e4) -> 
                  let next  = compute (NatElim (normalize sigma e1, normalize sigma e2, normalize sigma e3, normalize sigma e4)) in
                  if next = e then e else normalize sigma next
  | SumElim (e1, e2, e3, e4) -> normalize sigma (compute (SumElim (normalize sigma e1, normalize sigma e2, normalize sigma e3, normalize sigma e4)))
  | EqElim (e1, e2, e3, e4) -> EqElim (normalize sigma e1, normalize sigma e2, normalize sigma e3, normalize sigma e4)
  | Type _ | Nat | Zero | Meta _ -> e

let rec alpha_equiv sigma solutions (e1 : Syntax.raw_expr) (e2 : Syntax.raw_expr) =
    (* let e1' = normalize sigma e2 in *)
    (* let e2' = normalize sigma e2 in *)
    (* let () = Printf.printf "%s --> %s\n" (Syntax.show_raw_expr e2) (Syntax.show_raw_expr e1') in *)
    let alpha_equiv_helper sol e1 e2 = alpha_equiv sigma sol e1 e2 in
    let err e1 e2 = raise (TypeError (Printf.sprintf "Cannot unify %s and %s" (Syntax.show_raw_expr e1) (Syntax.show_raw_expr e2))) in
    let e1, e2 = normalize sigma e1, normalize sigma e2 in
    match e1, e2 with
    | Var x1, Var x2 -> if x1 = x2 then solutions else err e1 e2
    | e2, Meta m1
    | Meta m1, e2 ->
      begin match Syntax.Gamma.find_opt m1 solutions with
            | None -> Syntax.Gamma.add m1 e2 solutions
            | Some e -> alpha_equiv_helper solutions e e2
      end
    | Sum (e11, e12), Sum (e21, e22)
    | Pair (e11, e12), Pair (e21, e22)
    | App (e11, e12), App (e21, e22)                  ->  let sol = (alpha_equiv_helper solutions e11 e21) in
                                                          alpha_equiv_helper sol e12 e22
    | Lambda (x1, t1, e11), Lambda (x2, t2, e21)      ->  if t1 = t2 then
                                                          alpha_equiv_helper solutions e11 (Syntax.subst x2 (Var x1) e21)
                                                          else err e1 e2
    | Pi ((x1, e11, _), e12), Pi ((x2, e21, _), e22)
    | Sigma ((x1, e11), e12), Sigma ((x2, e21), e22)  ->  let sol = alpha_equiv_helper solutions e11 e21 in
                                                          alpha_equiv_helper sol e12 (Syntax.subst x2 (Var x1) e22)
    | Fst e1, Fst e2 | Snd e1, Snd e2
    | Succ e1, Succ e2 | Inl e1, Inl e2 | Inr e1, Inr e2  ->  alpha_equiv_helper solutions e1 e2
    | PropEq (e11, e12), PropEq (e21, e22)                ->  let sol = alpha_equiv_helper solutions e11 e21 in
                                                              alpha_equiv_helper sol e12 e22
    | NatElim (e11, e12, e13, e14), NatElim (e21, e22, e23, e24)
    | EqElim (e11, e12, e13, e14), EqElim (e21, e22, e23, e24)    -> 
        let sol = alpha_equiv_helper solutions e11 e21 in
        let sol = alpha_equiv_helper sol e12 e22 in
        let sol = alpha_equiv_helper sol e13 e23 in
        alpha_equiv_helper sol e14 e24
    | Refl (e11, e12), Refl (e21, e22)                            ->
        let sol = (alpha_equiv_helper solutions e11 e21) in
        alpha_equiv_helper sol e12 e22
    | Type i1, Type i2 ->
      begin match i1, i2 with
            | None, _
            | _, None -> solutions
            | Some i1, Some i2 -> if i1 = i2 then solutions else err e1 e2
      end
    | Zero, Zero
    | Nat, Nat   -> solutions
    | _, _       -> err e1 e2

let update_gamma sigma gamma x tau = Syntax.Gamma.add x (normalize sigma tau) gamma
let update_sigma sigma x e         = Syntax.Gamma.add x (normalize sigma e) sigma

let meta_variable_names s =
      List.fold_left  (fun res -> 
                        fun (x, _) -> Syntax.StringSet.add x res)
                      Syntax.StringSet.empty (Syntax.Gamma.bindings s)

let rec fold_meta (ty : Syntax.raw_expr) =
  let _ = meta_variable_count := !meta_variable_count + 1 in
  match ty with
  | Pi ((x, _, Syntax.Implicit), e2) -> Syntax.subst x (Meta (x ^ (string_of_int !meta_variable_count))) (fold_meta e2)
  | _ -> ty

let rec type_infer (sigma : Syntax.raw_expr Syntax.Gamma.t) (gamma : Syntax.raw_expr Syntax.Gamma.t) (meta_solutions : Syntax.raw_expr Syntax.Gamma.t) (e : Syntax.raw_expr) =
  (* let _ = Printf.printf "Inferring %s\n" (Syntax.show_raw_expr e) in *)
  match e with
  | Var x ->
      begin
        match Syntax.Gamma.find_opt x gamma with
        | None -> raise (TypeError (Printf.sprintf "%s not found in gamma" x))
        | Some e -> fold_meta e
      end
  | Lambda _ -> raise (TypeCheckError (Printf.sprintf "%s is a Lambda, which should be checkable" (Syntax.show_raw_expr e)))
  | App (e1, e2)       -> let ty_e1 = type_infer sigma gamma meta_solutions e1 in
                          begin match ty_e1 with
                                | Pi ((x, e3, Syntax.Explicit), e4) -> 
                                  let _ = type_check sigma gamma meta_solutions e2 e3 in
                                  Syntax.subst x e2 e4
                                | _ -> raise (TypeError (Printf.sprintf "Cannot apply %s to [%s : %s]" (Syntax.show_raw_expr e2) (Syntax.show_raw_expr e1) (Syntax.show_raw_expr ty_e1)))
                          end
  | Pi ((x, e1, _), e2) | Sigma ((x, e1), e2) ->
                          let sol = type_check sigma gamma meta_solutions e1 (Syntax.Type None) in
                          let _ = type_check sigma (Syntax.Gamma.add x e1 gamma) sol e2 (Syntax.Type None) in
                          Syntax.Type None
  | Sum (e1, e2)       -> let _ = type_check sigma gamma (type_check sigma gamma meta_solutions e1 (Syntax.Type None)) e2 (Syntax.Type None) in
                          Syntax.Type None
  | Inl _              -> raise (TypeCheckError "Cannot infer type of Inl")
  | Inr _              -> raise (TypeCheckError "Cannot infer type of Inr")
  | Pair (_, _)        -> raise (TypeCheckError "Cannot infer type of Product")
  | Fst e     ->  let ty_e = type_infer sigma gamma meta_solutions e in
                  begin match ty_e with
                        | Sigma ((_, e1), _) -> e1
                        | _ -> raise (TypeError (Printf.sprintf "Cannot apply %s with Fst" (Syntax.show_raw_expr e)))
                  end
  | Snd e     ->  let ty_e = type_infer sigma gamma meta_solutions e in
                  begin match ty_e with
                        | Sigma ((x, _), e2) -> Syntax.subst x (Syntax.Fst e) e2
                        | _ -> raise (TypeError (Printf.sprintf "Cannot apply %s with Snd" (Syntax.show_raw_expr e)))
                  end
  | Zero | Succ _ ->  Nat
  | Refl (e1, e2) ->  let sol = type_check sigma gamma meta_solutions e1 (Type None) in
                      let _   = type_check sigma gamma sol e2 e1 in
                      Syntax.PropEq (e2, e2)
  | PropEq (e1, e2) ->  let ty_e1 = type_infer sigma gamma meta_solutions e1 in
                        let _ = type_check sigma gamma meta_solutions e2 ty_e1 in
                        Syntax.Type None
  | NatElim (e1, e2, e3, e4) ->
                  let sol = type_check sigma gamma meta_solutions e4 Syntax.Nat in
                  begin match e1 with
                        | Lambda (z, _, goal) ->
                          let sol = type_check sigma (update_gamma sigma gamma z Syntax.Nat) sol goal (Syntax.Type None) in
                          let sol = type_check sigma gamma sol e2 (Syntax.subst z Zero goal) in
                          begin match e3 with
                                | Lambda (x, _, Lambda (y, _, e3)) ->
                                  let _ = type_check sigma (Syntax.Gamma.add y (Syntax.subst z (Syntax.Var x) goal) (Syntax.Gamma.add x Syntax.Nat gamma)) sol e3 (Syntax.subst z (Syntax.Succ (Syntax.Var x)) goal) in
                                  Syntax.subst z e4 goal
                                | _ -> raise (TypeError (Printf.sprintf "Inductive Step %s is not valid" (Syntax.show_raw_expr e3)))
                          end
                        | _ -> raise (TypeError (Printf.sprintf "Motive of NatElim should be a Lambda, but not %s" (Syntax.show_raw_expr e1)))
                  end
  | EqElim (e1, e2, e3, e4) ->
                    let sol = type_check sigma gamma meta_solutions e1 (Syntax.Type None) in
                    let ty_e4 = type_infer sigma gamma sol e4 in
                    begin match ty_e4 with
                      | PropEq (lhs, rhs) ->
                        let ty_lhs = type_infer sigma gamma sol lhs in
                        let sol = type_check sigma gamma sol rhs ty_lhs in
                        begin match e2 with
                              | Lambda (x, _, Lambda (y, _, goal)) ->
                                let sol = type_check sigma (Syntax.Gamma.add y e1 (Syntax.Gamma.add x e1 gamma)) sol goal (Syntax.Type None) in
                                begin match e3 with
                                      | Lambda (w, _, e3) ->
                                        let _ = type_check sigma (Syntax.Gamma.add w e1 gamma) sol e3 (Syntax.subst x (Syntax.Var w) (Syntax.subst y (Syntax.Var w) goal)) in
                                        Syntax.subst x lhs (Syntax.subst y rhs goal)
                                      | _ -> raise (TypeError (Printf.sprintf "Inductive Step %s is not valid" (Syntax.show_raw_expr e3)))
                                end
                              | _ -> raise (TypeError (Printf.sprintf "Motive of EqElim should be a Lambda, but got %s" (Syntax.show_raw_expr e2)))
                        end
                      | _ -> raise (TypeError (Printf.sprintf "EqElim cannot eliminate %s" (Syntax.show_raw_expr ty_e4)))
                    end
  | SumElim (e1, e2, e3, e4) ->
                    let ty = type_infer sigma gamma meta_solutions e4 in
                    begin match ty with
                          | Sum (t1, t2) -> 
                            begin match e1, e2, e3 with
                                  | Lambda (z, _, goal), Lambda (x1, _, inl_goal), Lambda (x2, _, inr_goal) ->
                                    let sol = type_check sigma (update_gamma sigma gamma x1 t1) meta_solutions inl_goal (Syntax.subst z (Var x1) goal) in
                                    let _ = type_check sigma (update_gamma sigma gamma x2 t2) sol inr_goal (Syntax.subst z (Var x2) goal) in
                                    Syntax.subst z e4 goal
                                  | _ -> raise (TypeError (Printf.sprintf "Motive of SumElim should be a Lambda, but got %s" (Syntax.show_raw_expr e2)))
                            end
                          | _ -> raise (TypeError (Printf.sprintf "SumElim cannot eliminate %s" (Syntax.show_raw_expr ty)))
                    end
  | Meta _    ->  Type None
  | Type None -> Type (Some 0)
  | Nat       -> Type None
  | Type (Some i) -> Type (Some (succ i))
and type_check (sigma : Syntax.raw_expr Syntax.Gamma.t) (gamma : Syntax.raw_expr Syntax.Gamma.t) (meta_solutions : Syntax.raw_expr Syntax.Gamma.t) (expr : Syntax.raw_expr) (tau : Syntax.raw_expr) =
  (* let _ = Printf.printf "Checking %s : %s\n" (Syntax.show_raw_expr expr) (Syntax.show_raw_expr tau) in *)
  let add_to_gamma x tau = update_gamma sigma gamma x tau in
  (* let add_to_sigma x e   = update_sigma sigma x e in *)
  let normalize_expr e = normalize sigma e in
  let check tau infer_ty = 
    (* let _ = Printf.printf "Unifying %s : %s\n" (Syntax.show_raw_expr expr) (Syntax.show_raw_expr tau) in *)
    alpha_equiv sigma meta_solutions tau infer_ty in
  match tau, expr with
  | Pi ((x1, e11, Syntax.Implicit), e21), Lambda (x2, Syntax.Implicit, e22)
  | Pi ((x1, e11, Syntax.Explicit), e21), Lambda (x2, Syntax.Explicit, e22) -> 
       type_check sigma (add_to_gamma x2 e11) meta_solutions e22 (normalize_expr (Syntax.subst x1 (Syntax.Var x2) e21))
  | Pi ((x1, _, Syntax.Implicit), e21), _ ->  
        let _ = (meta_variable_count := !meta_variable_count + 1) in
        type_check sigma gamma meta_solutions expr (Syntax.subst x1 (Meta (x1 ^ (string_of_int !meta_variable_count))) e21)
  | Sum (e1, _), Inl e                       -> type_check sigma gamma meta_solutions e e1
  | Sum (_, e2), Inr e                       -> type_check sigma gamma meta_solutions e e2
  | Sigma ((x, t1), t2), Pair(e1, e2)        -> let sol = type_check sigma gamma meta_solutions e1 t1 in
                                                type_check sigma gamma sol e2 (Syntax.subst x t1 t2)
  | _, _ -> let infer_ty = type_infer sigma gamma meta_solutions expr in
            check tau infer_ty