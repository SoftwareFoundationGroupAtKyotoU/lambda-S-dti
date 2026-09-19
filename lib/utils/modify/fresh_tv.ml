open Syntax
open Type_utils

let pick_tv u = match u with
  | TyVar tv -> tv
  | _ -> raise @@ Failure "not_tv"

let rec tv_renew_ty u env = match u with
  | TyVar (i, _) -> 
    begin 
    try TyVar (Environment.find (string_of_int i) env), env with
    Not_found -> let tv = pick_tv (fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    TyVar tv, env
    end
  | TyDyn | TyInt | TyBool | TyUnit | TyFloat | TyChar | TyString -> u, env
  | TyFun (u1, u2) -> 
    let u1, env = tv_renew_ty u1 env in
    let u2, env = tv_renew_ty u2 env in
    TyFun (u1, u2), env
  | TyList u -> 
    let u, env = tv_renew_ty u env in
    TyList u, env
  | TyTuple us ->
    let rec iter env l r = match l with
    | h :: t ->
      let u, env = tv_renew_ty h env in
      iter env t (u :: r)
    | [] -> 
      TyTuple (List.rev r), env
    in
    iter env us []
  | TyRef u ->
    let u, env = tv_renew_ty u env in
    TyRef u, env
  | TyArray u ->
    let u, env = tv_renew_ty u env in
    TyArray u, env
  | TyCoercion (u1, u2) ->
    let u1, env = tv_renew_ty u1 env in
    let u2, env = tv_renew_ty u2 env in
    TyCoercion (u1, u2), env

let rec tv_renew_coercion c env = match c with
  | CInj _ | CProj _ | CFail _ -> c, env
  | CTvInj ((i, _), p) -> 
    begin
    try CTvInj ((Environment.find (string_of_int i) env), p), env with
    Not_found -> let tv = pick_tv (fresh_tyvar ())in
    let env = Environment.add (string_of_int i) tv env in
    CTvInj (tv, p), env
    end
  | CTvProj ((i, _), p) -> 
    begin
    try CTvProj ((Environment.find (string_of_int i) env), p), env with
    Not_found -> let tv = pick_tv (fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    CTvProj (tv, p), env
    end
  | CTvProjInj ((i, _), p, q) -> 
    begin
    try CTvProjInj ((Environment.find (string_of_int i) env), p, q), env with
    Not_found -> let tv = pick_tv (fresh_tyvar ()) in
    let env = Environment.add (string_of_int i) tv env in
    CTvProjInj (tv, p, q), env
    end
  | CId u ->
    let u, env = tv_renew_ty u env in
    CId u, env
  | CFun (c1, c2) ->
    let c1, env = tv_renew_coercion c1 env in
    let c2, env = tv_renew_coercion c2 env in
    CFun (c1, c2), env 
  | CList c ->
    let c, env = tv_renew_coercion c env in
    CList c, env
  | CTuple cs ->
    let rec iter env l r = match l with
    | h :: t ->
      let c, env = tv_renew_coercion h env in
      iter env t (c :: r)
    | [] -> 
      CTuple (List.rev r), env
    in
    iter env cs []
  | CSeq (c1, c2) ->
    let c1, env = tv_renew_coercion c1 env in
    let c2, env = tv_renew_coercion c2 env in
    CSeq (c1, c2), env 
  | CRef (c1, c2) ->
    let c1, env = tv_renew_coercion c1 env in
    let c2, env = tv_renew_coercion c2 env in
    CRef (c1, c2), env
  | CMRef (u1, u2) ->
    let u1, env = tv_renew_ty u1 env in
    let u2, env = tv_renew_ty u2 env in
    CMRef (u1, u2), env
  | CArray (c1, c2) ->
    let c1, env = tv_renew_coercion c1 env in
    let c2, env = tv_renew_coercion c2 env in
    CArray (c1, c2), env
  | CMArray (u1, u2) ->
    let u1, env = tv_renew_ty u1 env in
    let u2, env = tv_renew_ty u2 env in
    CMArray (u1, u2), env

let rec tv_renew_mf mf env = match mf with
  | MatchILit _ | MatchBLit _ | MatchULit | MatchNil | MatchWild | MatchVar _ -> mf, env
  | MatchCons (mf1, mf2) ->
    let mf1, env = tv_renew_mf mf1 env in
    let mf2, env = tv_renew_mf mf2 env in
    MatchCons (mf1, mf2), env
  | MatchTuple mfs ->
    let rec iter env l r = match l with
    | h :: t ->
      let mf, env = tv_renew_mf h env in
      iter env t (mf :: r)
    | [] -> 
      MatchTuple (List.rev r), env
    in
    iter env mfs []

module ITGL = struct
  open Syntax.ITGL

  let rec tv_renew_exp e env = match e with
    | Var (r, x, us) ->
      let env = List.fold_left (fun env -> fun u -> snd (tv_renew_ty u env)) env !us in
      let us = ref @@ List.map (fun u -> fst @@ (tv_renew_ty u env)) !us in
      Var (r, x, us), env
    | IConst _ | BConst _ | UConst _ | FConst _ | CConst _ | SConst _ -> e, env
    | BinOp (r, op, e1, e2) -> 
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      BinOp (r, op, e1, e2), env
    | AscExp (r, e, u) ->
      let e, env = tv_renew_exp e env in
      let u, env = tv_renew_ty u env in
      AscExp (r, e, u), env
    | IfExp (r, e1, e2, e3) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      let e3, env = tv_renew_exp e3 env in
      IfExp (r, e1, e2, e3), env
    | ForExp (r, i, e1, e2, tag, e3) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      let e3, env = tv_renew_exp e3 env in
      ForExp (r, i, e1, e2, tag, e3), env
    | WhileExp (r, e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      WhileExp (r, e1, e2), env
    | FunExp (r, (x, anot, u), e) ->
      let u, env = tv_renew_ty u env in
      let e, env = tv_renew_exp e env in
      FunExp (r, (x, anot, u), e), env
    | FixExp (r, x, (y, anot, u), (anot_ret, uret), e) ->
      let u, env = tv_renew_ty u env in
      let uret, env = tv_renew_ty uret env in
      let e, env = tv_renew_exp e env in
      FixExp (r, x, (y, anot, u), (anot_ret, uret), e), env
    | AppExp (r, e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      AppExp (r, e1, e2), env
    | MatchExp (r, e, ms) ->
      let e, env = tv_renew_exp e env in
      let ms, env = tv_renew_ms ms env in
      MatchExp (r, e, ms), env
    | LetExp (r, x, e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      LetExp (r, x, e1, e2), env
    | NilExp (r, u) -> 
      let u, env = tv_renew_ty u env in
      NilExp (r, u), env
    | ConsExp (r, e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      ConsExp (r, e1, e2), env
    | TupleExp (r, es) ->
      let rec iter env l res = match l with
      | h :: t ->
        let e, env = tv_renew_exp h env in
        iter env t (e :: res)
      | [] -> 
        TupleExp (r, List.rev res), env
      in
      iter env es []
    | RefExp (r, e) ->
      let e, env = tv_renew_exp e env in
      RefExp (r, e), env
    | DerefExp (r, e) ->
      let e, env = tv_renew_exp e env in
      DerefExp (r, e), env
    | SubstExp (r, e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      SubstExp (r, e1, e2), env
    | MakeArrayExp (r, e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      MakeArrayExp (r, e1, e2), env
    | GetExp (r, e1, e2) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      GetExp (r, e1, e2), env
    | PutExp (r, e1, e2, e3) ->
      let e1, env = tv_renew_exp e1 env in
      let e2, env = tv_renew_exp e2 env in
      let e3, env = tv_renew_exp e3 env in
      PutExp (r, e1, e2, e3), env
    | LengthExp (r, e) ->
      let e, env = tv_renew_exp e env in
      LengthExp (r, e), env
  and tv_renew_ms ms env = match ms with
    | (mf, e) :: ms ->
      let mf, env = tv_renew_mf mf env in
      let e, env = tv_renew_exp e env in
      let ms, env = tv_renew_ms ms env in
      (mf, e) :: ms, env
    | [] -> [], env

  let tv_renew p = match p with
  | Exp e ->
    let e, _ = tv_renew_exp e Syntax.Environment.empty in
    Exp e
  | LetDecl (id, e) ->
    let e, _ = tv_renew_exp e Syntax.Environment.empty in
    LetDecl (id, e)
  | TypeDecl (id, u) -> TypeDecl (id, u)
end