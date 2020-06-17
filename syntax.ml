module EnvKey = 
  struct
    type t = string
    let compare = Stdlib.compare
  end

module Gamma = Map.Make (EnvKey)
module StringSet = Set.Make(String)

let line_col_of_lex_pos =
  let open Lexing in
  function {pos_fname = _; pos_lnum; pos_bol; pos_cnum } ->
    Printf.sprintf "%d:%d" pos_lnum (pos_cnum - pos_bol)

let string_of_lex_pos =
  let open Lexing in
  function {pos_fname; pos_lnum = _; pos_bol = _; pos_cnum = _} as pos ->
    Printf.sprintf "%s:%s" pos_fname (line_col_of_lex_pos pos)

type arg_type =
  | Implicit 
  | Explicit
  [@@deriving show]

type raw_expr =
  | Var of string
  | Lambda of string * arg_type * raw_expr
  | App of raw_expr * raw_expr
  | Pi of (string * raw_expr * arg_type) * raw_expr
  | Pair of raw_expr * raw_expr
  | Sum of raw_expr * raw_expr
  | Fst of raw_expr
  | Snd of raw_expr
  | Inl of raw_expr
  | Inr of raw_expr
  | Sigma of (string * raw_expr) * raw_expr

  | Nat
  | Zero
  | Succ of raw_expr
  | NatElim of raw_expr * raw_expr * raw_expr * raw_expr

  | Refl of raw_expr * raw_expr
  | EqElim of raw_expr * raw_expr * raw_expr * raw_expr
  | SumElim of raw_expr * raw_expr * raw_expr * raw_expr
  | PropEq of raw_expr * raw_expr
  | Meta of string

  | Type of int option
  [@@deriving show]

type binding =
  | CmdNormalize of raw_expr
  | Def of string * raw_expr
  | Claim of string * raw_expr

let (+++) s1 s2 = StringSet.union s1 s2

let fresh avoid varname =
  let rec fresh_impl dep avoid varname old =
    if not (StringSet.mem varname avoid) then varname
    else fresh_impl (dep + 1) avoid (old ^ (string_of_int dep)) old in
  fresh_impl 0 avoid varname varname

let rec free_vars e =
  match e with
  | Var x                                   -> StringSet.singleton x
  | Lambda (x, _, e1)                       -> StringSet.remove x (free_vars e1)
  | App (e1, e2) 
  | Refl (e1, e2)
  | Pair (e1, e2)                           -> StringSet.union (free_vars e1) (free_vars e2)
  | Pi ((x, e1, _), e2) 
  | Sigma ((x, e1), e2)                     -> StringSet.union (free_vars e1) (StringSet.remove x (free_vars e2))
  | Fst e | Snd e
  | Succ e | Inl e | Inr e                  -> free_vars e
  | Nat | Zero | Type _ | Meta _            -> StringSet.empty
  | Sum (e1, e2)
  | PropEq (e1, e2)                         -> StringSet.union (free_vars e1) (free_vars e2)
  | NatElim (e1, e2, e3, e4)
  | SumElim (e1, e2, e3, e4)
  | EqElim (e1, e2, e3, e4)                 ->  let s1 = free_vars e1 in
                                                let s2 = StringSet.union (free_vars e2) s1 in
                                                let s3 = StringSet.union (free_vars e3) s2 in
                                                StringSet.union (free_vars e4) s3                   

let rec subst (from_ : string) (to_ : raw_expr) (in_ : raw_expr) =
  let subst_helper e = subst from_ to_ e in
  match in_ with
  | Var x           -> if String.equal x from_ then to_ else in_
  | Lambda (x, t, e2)  -> if from_ = x then in_
                       else if StringSet.mem x (free_vars to_)
                            then let fresh_name = fresh ((StringSet.singleton from_) +++ (free_vars in_) +++ (free_vars to_)) x in
                                 let e2' = subst x (Var fresh_name) e2 in
                                 Lambda (fresh_name, t, subst_helper e2')
                            else Lambda (x, t, subst_helper e2)
  | App (e1, e2)    -> App (subst_helper e1, subst_helper e2)
  | Pi ((x, e1, arg_ty), e2) -> if x = from_ then in_
                        else let e1' = subst from_ to_ e1 in
                             if StringSet.mem x (free_vars to_)
                             then let fresh_name = fresh ((StringSet.singleton from_) +++ (free_vars in_) +++ (free_vars to_)) x in
                                  let e2' = subst x (Var fresh_name) e2 in
                                  Pi ((fresh_name, e1', arg_ty), subst_helper e2')
                             else Pi ((x, e1', arg_ty), subst_helper e2)
  | Sigma ((x, e1), e2) ->  if x = from_ then in_
                            else let e1' = subst from_ to_ e1 in
                                 if StringSet.mem x (free_vars to_)
                                 then let fresh_name = fresh ((StringSet.singleton from_) +++ (free_vars in_) +++ (free_vars to_)) x in
                                      let e2' = subst x (Var fresh_name) e2 in
                                      Sigma ((fresh_name, e1'), subst_helper e2')
                                 else Sigma ((x, e1'), subst_helper e2)
  | Pair (e1, e2)       -> Pair (subst_helper e1, subst_helper e2)
  | Sum (e1, e2)        -> Sum (subst_helper e1, subst_helper e2)
  | Refl (e1, e2)       -> Refl (subst_helper e1, subst_helper e2)
  | Fst e               -> Fst  (subst_helper e)
  | Snd e               -> Snd  (subst_helper e)
  | Inl e               -> Inl (subst_helper e)
  | Inr e               -> Inr (subst_helper e)
  | Succ e              -> Succ (subst_helper e)
  | PropEq (e1, e2)     -> PropEq (subst_helper e1, subst_helper e2)
  | NatElim (e1, e2, e3, e4) -> NatElim (subst_helper e1, subst_helper e2, subst_helper e3, subst_helper e4)
  | EqElim (e1, e2, e3, e4) -> EqElim (subst_helper e1, subst_helper e2, subst_helper e3, subst_helper e4)
  | SumElim (e1, e2, e3, e4) -> SumElim (subst_helper e1, subst_helper e2, subst_helper e3, subst_helper e4)
  | Nat | Zero | Type _ | Meta _ -> in_