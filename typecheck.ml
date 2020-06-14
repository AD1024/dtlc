open Dtlclib

exception TypeError of string
exception NormalizationError of string

let compute e =
    match e with
    | Syntax.App (Lambda (x, _, e1), e2) -> Syntax.subst x e2 e1
    | Fst (Pair ((_, e1), _)) -> e1
    | Snd (Pair (_, e2)) -> e2
    | NatElim (_, e2, _, Zero) -> e2
    | NatElim (e1, e2, (Lambda (x, tx, Lambda (y, ty, e3))), (Succ e4)) -> Syntax.subst x e4 (Syntax.subst y (Syntax.NatElim (e1, e2, (Lambda (x, tx, Lambda (y, ty, e3))), e4)) e3)
    | _ -> e

let definitional_eq (e1 : Syntax.raw_expr) (e2 : Syntax.raw_expr) = e1 = compute e2 || e2 = compute e1

let rec normalize sigma (e : Syntax.raw_expr) =
  (* let _ = Printf.printf "normalizing : %s\n" (Syntax.show_raw_expr e) in *)
  match e with
  | Var x ->  begin  match Syntax.Gamma.find_opt x sigma with
                    | None -> e
                    | Some e -> e
              end
  | App (e1, e2) ->   begin let e1' = normalize sigma e1 in
                            let e2' = normalize sigma e2 in
                            match e1' with
                            | Lambda (x, _, e) -> normalize sigma (Syntax.subst x e2' e)
                            | _ -> App (e1', e2')
                      end
  | Lambda (x, t, e) -> Lambda (x, normalize sigma t, normalize sigma e)
  | Pi ((x, e1), e2) -> Pi ((x, normalize sigma e1), normalize sigma e2)
  | Sigma ((x, e1), e2) -> Sigma ((x, normalize sigma e1), normalize sigma e2)
  | Pair ((x, e1), e2) -> Pair ((x, normalize sigma e1), normalize sigma e2)
  | Fst e ->  let e' = normalize sigma e in
              compute (Fst e')
  | Snd e ->  let e' = normalize sigma e in
              compute (Snd e')
  | Succ e -> Succ (normalize sigma e)
  | PropEq (e1, e2) -> PropEq (normalize sigma e1, normalize sigma e2)
  | Refl (e1, e2) -> Refl (normalize sigma e1, normalize sigma e2)
  | NatElim (e1, e2, e3, e4) -> 
                  let next  = compute (NatElim (normalize sigma e1, normalize sigma e2, normalize sigma e3, normalize sigma e4)) in
                  if next = e then e else normalize sigma next
  | EqElim (e1, e2, e3, e4) -> EqElim (normalize sigma e1, normalize sigma e2, normalize sigma e3, normalize sigma e4)
  | Type _ | Nat | Zero -> e

let rec alpha_equiv sigma (e1 : Syntax.raw_expr) (e2 : Syntax.raw_expr) =
    (* let e1' = normalize sigma e2 in *)
    (* let e2' = normalize sigma e2 in *)
    (* let () = Printf.printf "%s --> %s\n" (Syntax.show_raw_expr e2) (Syntax.show_raw_expr e1') in *)
    match normalize sigma e1, normalize sigma e2 with
    | Var x1, Var x2 -> x1 = x2
    | App (e11, e12), App (e21, e22)                  -> alpha_equiv sigma e11 e21 && alpha_equiv sigma e12 e22
    | Lambda (x1, t1, e11), Lambda (x2, t2, e21)      -> alpha_equiv sigma t1 t2 && alpha_equiv sigma e11 (Syntax.subst x2 (Var x1) e21)
    | Pi ((x1, e11), e12), Pi ((x2, e21), e22)
    | Pair ((x1, e11), e12), Pair ((x2, e21), e22)
    | Sigma ((x1, e11), e12), Sigma ((x2, e21), e22)      -> alpha_equiv sigma e11 e21 && alpha_equiv sigma e12 (Syntax.subst x2 (Var x1) e22)
    | Fst e1, Fst e2 | Snd e1, Snd e2 | Succ e1, Succ e2  -> alpha_equiv sigma e1 e2
    | PropEq (e11, e12), PropEq (e21, e22)                -> alpha_equiv sigma e11 e21 && alpha_equiv sigma e12 e22
    | NatElim (e11, e12, e13, e14), NatElim (e21, e22, e23, e24)  -> alpha_equiv sigma e11 e21 && alpha_equiv sigma e12 e22 && alpha_equiv sigma e13 e23 && alpha_equiv sigma e14 e24
    | EqElim (e11, e12, e13, e14), EqElim (e21, e22, e23, e24)    -> alpha_equiv sigma e11 e21 && alpha_equiv sigma e12 e22 && alpha_equiv sigma e13 e23 && alpha_equiv sigma e14 e24
    | Refl (e11, e12), Refl (e21, e22)                            -> alpha_equiv sigma e11 e21 && alpha_equiv sigma e12 e22
    | Type i1, Type i2 ->
      begin match i1, i2 with
            | None, _ -> true
            | _, None -> true
            | Some i1, Some i2 -> i1 = i2
      end
    | Zero, Zero -> true
    | Nat, Nat   -> true
    | _, _       -> false

let rec type_infer (sigma : Syntax.raw_expr Syntax.Gamma.t) (gamma : Syntax.raw_expr Syntax.Gamma.t) (e : Syntax.raw_expr) =
  (* let _ = Printf.printf "Checking %s\n" (Syntax.show_raw_expr e) in *)
  match e with
  | Var x ->
      begin
        match Syntax.Gamma.find_opt x gamma with
        | None -> raise (TypeError (Printf.sprintf "%s not found in gamma" x))
        | Some e -> e
      end
  | Lambda (x, e1, e2) -> let gamma' = type_check sigma gamma e1 (Syntax.Type None) in
                          let e3 = type_infer sigma (Syntax.Gamma.add x e1 gamma') e2 in
                          Pi ((x, e1), e3)
  | App (e1, e2)       -> let ty_e1 = type_infer sigma gamma e1 in
                          begin match ty_e1 with
                                | Pi ((x, e3), e4) -> let _ = type_check sigma gamma e2 e3 in
                                                      Syntax.subst x e2 e4
                                | _ -> raise (TypeError (Printf.sprintf "Cannot apply %s to %s" (Syntax.show_raw_expr e2) (Syntax.show_raw_expr e1)))
                          end
  | Pi ((x, e1), e2) | Sigma ((x, e1), e2) ->
                          let gamma_1 = type_check sigma gamma e1 (Syntax.Type None) in
                          let _ = type_check sigma (Syntax.Gamma.add x e1 gamma_1) e2 (Syntax.Type None) in
                          Syntax.Type None
  | Pair ((x, e1), e2) -> let ty_e1 = type_infer sigma gamma e1 in
                          let ty_e2 = type_infer sigma (Syntax.Gamma.add x ty_e1 gamma) e2 in
                          Syntax.Sigma ((x, ty_e1), ty_e2)
  | Fst e     ->  let ty_e = type_infer sigma gamma e in
                  begin match ty_e with
                        | Sigma ((_, e1), _) -> e1
                        | _ -> raise (TypeError (Printf.sprintf "Cannot apply %s with Fst" (Syntax.show_raw_expr e)))
                  end
  | Snd e     ->  let ty_e = type_infer sigma gamma e in
                  begin match ty_e with
                        | Sigma ((x, _), e2) -> Syntax.subst x (Syntax.Fst e) e2
                        | _ -> raise (TypeError (Printf.sprintf "Cannot apply %s with Snd" (Syntax.show_raw_expr e)))
                  end
  | Zero | Succ _ ->  Nat
  | Refl (e1, e2) ->  let gamma' = type_check sigma gamma e1 (Type None) in
                      let _      = type_check sigma gamma' e2 e1 in
                      Syntax.PropEq (e2, e2)
  | PropEq (e1, e2) ->  let ty_e1 = type_infer sigma gamma e1 in
                        let _ = type_check sigma gamma e2 ty_e1 in
                        Syntax.Type None
  | NatElim (e1, e2, e3, e4) ->
                  let gamma_1 = type_check sigma gamma e4 Syntax.Nat in
                  begin match e1 with
                        | Lambda (z, Nat, goal) ->
                          let gamma' = type_check sigma gamma_1 e2 (Syntax.subst z Zero goal) in
                          begin match e3 with
                                | Lambda (x, _, Lambda (y, _, e3)) ->
                                  let _ = type_check sigma (Syntax.Gamma.add y (Syntax.subst z (Syntax.Var x) goal) (Syntax.Gamma.add x Syntax.Nat gamma')) e3 (Syntax.subst z (Syntax.Succ (Syntax.Var x)) goal) in
                                  Syntax.subst z e4 goal
                                | _ -> raise (TypeError (Printf.sprintf "Inductive Step %s is not valid" (Syntax.show_raw_expr e3)))
                          end
                        | _ -> raise (TypeError (Printf.sprintf "Motive of NatElim should be a Lambda, but not %s" (Syntax.show_raw_expr e1)))
                  end
  | EqElim (e1, e2, e3, e4) ->
                    let gamma' = type_check sigma gamma e1 (Syntax.Type None) in
                    let ty_e4 = type_infer sigma gamma e4 in
                    begin match ty_e4 with
                      | PropEq (lhs, rhs) ->
                        let ty_lhs = type_infer sigma gamma' lhs in
                        let gamma' = type_check sigma gamma' rhs ty_lhs in
                        begin match e2 with
                              | Lambda (x, _, Lambda (y, _, goal)) ->
                                let gamma' = type_check sigma (Syntax.Gamma.add y e1 (Syntax.Gamma.add x e1 gamma')) goal (Syntax.Type None) in
                                begin match e3 with
                                      | Lambda (w, _, e3) ->
                                        let _ = type_check sigma (Syntax.Gamma.add w e1 gamma') e3 (Syntax.subst x (Syntax.Var w) (Syntax.subst y (Syntax.Var w) goal)) in
                                        Syntax.subst x lhs (Syntax.subst y rhs goal)
                                      | _ -> raise (TypeError (Printf.sprintf "Inductive Step %s is not valid" (Syntax.show_raw_expr e3)))
                                end
                              | _ -> raise (TypeError (Printf.sprintf "Motive of EqElim should be a Lambda, but got %s" (Syntax.show_raw_expr e2)))
                        end
                      | _ -> raise (TypeError (Printf.sprintf "EqElim cannot eliminate %s" (Syntax.show_raw_expr ty_e4)))
                    end
  | Type None -> Type (Some 0)
  | Nat       -> Type None
  | Type (Some i) -> Type (Some (succ i))
and type_check (sigma : Syntax.raw_expr Syntax.Gamma.t) (gamma : Syntax.raw_expr Syntax.Gamma.t) (e : Syntax.raw_expr) (tau : Syntax.raw_expr) =
  (* let _ = Printf.printf "Checking %s\n" (Syntax.show_raw_expr e) in *)
  let infer_ty = type_infer sigma gamma e in
  if alpha_equiv sigma tau infer_ty then
    begin match e with
          | Var x -> if infer_ty = Type None then Syntax.Gamma.add x tau gamma else gamma
          | _     -> gamma
    end
  else raise (TypeError (Printf.sprintf "Cannot unify %s and %s" (Syntax.show_raw_expr tau) (Syntax.show_raw_expr infer_ty)))
