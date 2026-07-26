open Format
open Pp
open Syntax
open Subst
open Ftv
open Type_utils
open Unify

exception Type_error of string

(* Bug in this implementation *)
exception Type_bug of string

let type_of_binop = function
  | Plus | Minus | Mult | Div | Mod -> TyInt, TyInt, TyInt
  | Eq | Neq | Lt | Lte | Gt | Gte -> TyInt, TyInt, TyBool

let rec type_of_mf mf ids = match mf with
  | MatchILit _ -> TyInt, ids
  | MatchBLit _ -> TyBool, ids
  | MatchULit -> TyUnit, ids
  | MatchVar id ->
    if List.mem id ids then raise @@ Type_error "match: same var appeared";
    TyDyn, id :: ids
  | MatchNil -> TyList TyDyn, ids
  | MatchCons (mf1, mf2) ->
    let u2, ids = type_of_mf mf2 ids in
    let u1, ids = type_of_mf mf1 ids in
    unify @@ CConsistent (TyList u1, u2);
    unify_meet (TyList u1) u2, ids
  | MatchTuple mfs ->
    let rec iter ids l r = match l with
      | h :: t ->
        let u, ids = type_of_mf h ids in
        iter ids t (u :: r)
      | [] -> TyTuple (List.rev r), ids
    in
    iter ids mfs []
  (* | MatchAsc (mf, u) ->
    let u', env, ids = type_of_matchform env mf ids in
    unify @@ CConsistent (u', u);
    u, env, ids *)
  | MatchWild -> TyDyn, ids

let rec env_of_mf env u_match = function
  | MatchILit _ | MatchBLit _ | MatchULit | MatchNil | MatchWild -> env
  | MatchVar id -> Environment.add id (tysc_of_ty u_match) env
  | MatchCons (mf1, mf2) ->
    let env = env_of_mf env u_match mf2 in
    let env = env_of_mf env (unify_lelm u_match) mf1 in
    env
  | MatchTuple mfs ->
    let us = unify_telm (List.length mfs) u_match in
    let env = List.fold_left2 (fun env u mf -> env_of_mf env u mf) env us mfs in
    env
  (* | MatchAsc (mf, u) ->
    let u', env, ids = type_of_matchform env mf ids in
    unify @@ CConsistent (u', u);
    u, env, ids *)

module ITGL = struct
  open Pp.ITGL
  open Syntax.ITGL
  open Ftv.ITGL

  (* Utility functions for let polymorpism *)
  let closure_tyvars1 u1 env v1 =
    TV.elements @@ TV.diff (ftv_ty u1) @@ TV.union (ftv_tyenv env) (ftv_exp v1)

  (** Returns true if a given expression is a "value" under the given environment.
   * The definition of "value" slightly differs that in the paper
   * to allow more type variables are generalized by let. *)
  let rec is_pure_value env e = 
    let rec is_base_value env u e = match e, u with 
      | _, (TyVar _ | TyDyn | TyFun _ | TyList _ | TyTuple _) -> 
        raise @@ Type_bug (asprintf "invalid base value: %a" pp_exp e)
      | Var (_, x, ys), u ->
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          subst_type s u' = u
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      | IConst _, TyInt -> true
      | BConst _, TyBool -> true
      | UConst _, TyUnit -> true
      | AscExp (r, e, TyVar (_, { contents = Some u' })), u ->
        is_base_value env u @@ AscExp (r, e, u')
      | AscExp (_, e, u'), u when u = u' -> is_base_value env u e
      | _ -> false
    in let rec is_fun_value env = function
      | Var (_, x, ys) ->
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          begin match subst_type s u' with
          | TyFun _ -> true
          | _ -> false
          end
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      | FunExp _ | FixExp _ -> true
      | AscExp (_, e, TyFun _) -> is_fun_value env e
      | AscExp (r, e, TyVar (_, { contents = Some u })) -> is_fun_value env @@ AscExp (r, e, u)
      | _ -> false
    in let rec is_list_value env = function
      | Var (_, x, ys) ->  
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          begin match subst_type s u' with
          | TyList _ -> true
          | _ -> false
          end
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      | NilExp _ -> true
      | ConsExp (_, e1, e2) -> is_pure_value env e1 && is_list_value env e2
      | AscExp (_, e, TyList _) -> is_list_value env e
      | AscExp (r, e, TyVar (_, { contents = Some u })) -> is_list_value env @@ AscExp (r, e, u)
      | _ -> false
    in let rec is_tuple_value env = function
      | Var (_, x, ys) ->  
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          begin match subst_type s u' with
          | TyTuple _ -> true
          | _ -> false
          end
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      (* | NilExp _ -> true
      | ConsExp (_, e1, e2) -> is_value env e1 && is_list_value env e2 *)
      | TupleExp (_, es) -> List.fold_left (fun b e -> b && is_pure_value env e) true es
      | AscExp (_, e, TyTuple _) -> is_tuple_value env e
      | AscExp (r, e, TyVar (_, { contents = Some u })) -> is_tuple_value env @@ AscExp (r, e, u)
      | _ -> false
    in let rec is_tyvar_value env a = function
      | Var (_, x, ys) ->
        begin try
          let TyScheme (xs, u') = Environment.find x env in
          let s = Utils.List.zip xs !ys in
          begin match subst_type s u' with
          | TyVar (a', _) when a = a' -> true
          | _ -> false
          end 
        with Not_found ->
          raise @@ Type_bug (asprintf "variable '%s' not found in the environment" x)
        end
      | AscExp (r, e, TyVar (_, { contents = Some u })) ->
          is_tyvar_value env a @@ AscExp (r, e, u)
      | AscExp (_, e, TyVar (a', { contents = None })) when a = a' ->
          is_tyvar_value env a e
      | _ -> false 
    in match e with
    | Var _
    | IConst _
    | BConst _
    | UConst _
    | FunExp _
    | FixExp _
    | NilExp _ -> true
    | ConsExp (_, e1, e2) -> is_pure_value env e1 && is_list_value env e2
    | TupleExp (_, es) -> List.fold_left (fun b e -> b && is_pure_value env e) true es
    | AscExp (_, e, (TyInt | TyBool | TyUnit as u)) -> is_base_value env u e
    | AscExp (_, e, TyFun _) -> is_fun_value env e
    | AscExp (_, e, TyList _) -> is_list_value env e
    | AscExp (_, e, TyTuple _) -> is_tuple_value env e
    | AscExp (_, e, TyDyn) -> is_pure_value env e
    | AscExp (r, e, TyVar (_, { contents = Some u })) -> is_pure_value env @@ AscExp (r, e, u)
    | AscExp (_, e, TyVar (a, { contents = None })) -> is_tyvar_value env a e
    | _ -> false

  let rec type_of_exp env = function
    | Var (_, x, ys) ->
      begin try
        let TyScheme (xs, u) = Environment.find x env in
        (* Replace type variables with fresh ones *)
        ys := List.map (fun _ -> fresh_tyvar ()) xs;
        let s = Utils.List.zip xs !ys in
        subst_type s u 
      with Not_found ->
        raise @@ Type_error (asprintf "variable '%s' not found in the environment" x)
      end
    | IConst _ -> TyInt
    | BConst _ -> TyBool
    | UConst _ -> TyUnit
    | BinOp (_, op, e1, e2) ->
      let ui1, ui2, ui = type_of_binop op in
      let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      unify @@ CConsistent (u1, ui1);
      unify @@ CConsistent (u2, ui2);
      ui
    | AscExp (_, e, u1) ->
      let u = type_of_exp env e in
      unify @@ CConsistent (u, u1);
      u1
    | IfExp (_, e1, e2, e3) ->
      let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      let u3 = type_of_exp env e3 in
      unify @@ CConsistent (u1, TyBool);
      unify_meet u2 u3
    | FunExp (_, (x, _, u1), e) ->
      let u2 = type_of_exp (Environment.add x (tysc_of_ty u1) env) e in
      TyFun (u1, u2)
    | FixExp (_, x, (y, _, u1), u2, e) ->
      let env = Environment.add x (tysc_of_ty (TyFun (u1, u2))) env in
      let env = Environment.add y (tysc_of_ty u1) env in
      let u2' = type_of_exp env e in
      unify @@ CConsistent (u2, u2');
      TyFun (u1, u2)
    | AppExp (_, e1, e2) ->
      let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      let dom_u1, cod_u1 = unify_dom u1, unify_cod u1 in
      unify @@ CConsistent (dom_u1, u2);
      cod_u1
    | MatchExp (_, e, ms) ->
      let u_match = type_of_exp env e in
      let us, _ = List.split @@ List.map (fun (mf, _) -> type_of_mf mf []) ms in
      let u_match = List.fold_left (fun u1 u2 -> unify_meet u1 u2) u_match us in
      let us = List.map (fun (mf, e) ->
        let env' = env_of_mf env u_match mf in
        type_of_exp env' e
      ) ms in
      List.fold_left (fun u1 u2 -> unify_meet u1 u2) TyDyn us (* dummy for meet *)
    | LetExp (r, x, e1, e2) ->
      let u1 = type_of_exp env e1 in
      if is_pure_value env e1 then
        let xs = closure_tyvars1 u1 env e1 in
        let us1 = TyScheme (xs, u1) in
        type_of_exp (Environment.add x us1 env) e2
      else
        type_of_exp env @@ AppExp (r, FunExp (r, (x, Impl, u1), e2), e1)
    | NilExp (_, u) -> TyList u
    | ConsExp (_, e1, e2) -> 
      let u2 = type_of_exp env e2 in
      let u1 = type_of_exp env e1 in
      unify @@ CConsistent (TyList u1, u2);
      unify_meet (TyList u1) u2
    | TupleExp (_, es) ->
      TyTuple (List.map (fun e -> type_of_exp env e) es)
    | RefExp (_, e) -> TyRef (type_of_exp env e)
    | DerefExp (_, e) ->
      let u = type_of_exp env e in
      unify_cont u
    | SubstExp (_, e1, e2) ->
      let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      let cont = unify_cont u1 in
      unify @@ CConsistent (cont, u2);
      TyUnit
    | MakeArrayExp (_, e1, e2) ->
      let u1 = type_of_exp env e1 in
      unify @@ CConsistent (u1, TyInt);
      TyArray (type_of_exp env e2)
    | GetExp (_, e1, e2) ->
      let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      unify @@ CConsistent (u2, TyInt);
      unify_cont_array u1
    | PutExp (_, e1, e2, e3) ->
      let u1 = type_of_exp env e1 in
      let u2 = type_of_exp env e2 in
      let u3 = type_of_exp env e3 in
      unify @@ CConsistent (u2, TyInt);
      let cont = unify_cont_array u1 in
      unify @@ CConsistent (cont, u3);
      TyUnit

  let type_of_program env p =
    try match p with
    | Exp e ->
      Exp e, type_of_exp env e
    | LetDecl (x, e) ->
      let u = type_of_exp env e in
      LetDecl (x, e), u
    with Unify_error msg -> raise @@ Type_error msg
end

let type_of_coercion c =
  let rec coerce_pair = function
    | CInj t -> type_of_tag t, TyDyn
    | CProj (t, _) -> TyDyn, type_of_tag t
    | CTvInj (tv, _) -> TyVar tv, TyDyn
    | CTvProj (tv, _) -> TyDyn, TyVar tv
    | CTvProjInj _ -> TyDyn, TyDyn
    | CFun (c1, c2) ->
      let u11, u12 = coerce_pair c1 in
      let u21, u22 = coerce_pair c2 in
      TyFun (u12, u21), TyFun (u11, u22)
    | CList c ->
      let u1, u2 = coerce_pair c in
      TyList u1, TyList u2
    | CTuple cs ->
      let pairs = List.map (fun c -> coerce_pair c) cs in
      let us1, us2 = List.split pairs in
      TyTuple us1, TyTuple us2
    | CRef (c1, _) ->
      let u1, u2 = coerce_pair c1 in
      TyRef u1, TyRef u2
    | CMRef (u1, u2) -> TyRef u1, TyRef u2
    | CArray (c1, _) ->
      let u1, u2 = coerce_pair c1 in
      TyArray u1, TyArray u2
    | CMArray (u1, u2) -> TyArray u1, TyArray u2
    | CId u -> u, u
    | CSeq (c1, c2) ->
      let u11, u12 = coerce_pair c1 in
      let u21, u22 = coerce_pair c2 in
      if u12 = u21 then u11, u22
      else raise @@ Type_bug (asprintf "type mismatch in coercion sequence: %a, %a" pp_ty u12 pp_ty u21)
    | CFail _ -> assert false
  in
  let c1, c2 = coerce_pair c in
  TyCoercion (c1, c2)

module CC = struct
  open Syntax.CC

  let rec type_of_exp env = function
    | Var (x, ys) -> begin
        try
          let TyScheme (xs, u) = Environment.find x env in
          if List.length xs = List.length ys then
            let ftvs = ftv_ty u in
            let s = Utils.List.zip xs ys in
            let s = List.filter (fun (x, _) -> TV.mem x ftvs) s in
            let s = List.map (fun (x, u) -> x, tyarg_to_ty u) s in
            subst_type s u
          else
            raise @@ Type_bug "invalid type application"
        with Not_found ->
          raise @@ Type_bug "variable not found"
      end
    | IConst _ -> TyInt
    | BConst _ -> TyBool
    | UConst -> TyUnit
    | BinOp (op, f1, f2) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      let ui1, ui2, ui = type_of_binop op in
      if (u1, u2) = (ui1, ui2) then
        ui
      else
        raise @@ Type_bug "binop"
    | IfExp (f1, f2, f3) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      let u3 = type_of_exp env f3 in
      if u1 = TyBool && u2 = u3 then
        u2
      else
        raise @@ Type_bug "if"
    | FunExp (tvs, fund) ->
      let TyScheme (_, u) = type_of_fund env tvs fund in u
    | FixExp (tvs, fixd) ->
      let TyScheme (_, u) = type_of_fixd env tvs fixd in u
    | AppMExp (f1, f2) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      begin match u1, u2 with
        | TyFun (u11, u12), u2 when u11 = u2 ->
          u12
        | _ -> raise @@ Type_bug (Format.asprintf "app::: u1:%a, u2:%a" Pp.pp_ty u1 Pp.pp_ty u2)
      end
    | AppDExp (f1, (f2, f3)) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      let u3 = type_of_exp env f3 in
      begin match u1, u3 with
      | TyFun (u11, u12), TyCoercion (u31, u32) when u11 = u2 && u12 = u31 -> u32
      | _ -> raise @@ Type_bug (Format.asprintf "AppDExp")
      end
    | MatchExp (f, ms) ->
      let u_match = type_of_exp env f in
      let us = List.map (fun (mf, f) ->
        let env = env_of_mf env u_match mf in
        type_of_exp env f
      ) ms in
      let u_exp = List.hd us in
      if List.for_all (fun u' -> u_exp = u') us then u_exp else raise @@ Type_bug (Format.asprintf "MatchExp")
    | LetExp (x, f1, f2) ->
      let us1 = match f1 with
        | FunExp (xs, fd) -> type_of_fund env xs fd
        | FixExp (tvs, fixd) -> type_of_fixd env tvs fixd
        | f1 -> tysc_of_ty (type_of_exp env f1)
      in
      type_of_exp (Environment.add x us1 env) f2
    | NilExp u -> TyList u
    | ConsExp (f1, f2) ->
      let u2 = type_of_exp env f2 in
      let u1 = type_of_exp env f1 in
      if (TyList u1) = u2 then u2
      else raise @@ Type_bug (asprintf "cons: %a=%a" pp_ty (TyList u1) pp_ty u2)
    | TupleExp fs -> TyTuple (List.map (fun f -> type_of_exp env f) fs)
    | RefExp (f, u) ->
      let u' = type_of_exp env f in
      assert (u = u');
      TyRef u
    | DerefExp (f, ou) ->
      let u = type_of_exp env f in
      begin match u, ou with
      | TyRef u, None -> u
      | TyRef u, Some u' when u = u' -> u
      | _ -> raise @@ Type_bug "deref"
      end
    | SubstExp (f1, f2, ou) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      assert (u1 = TyRef u2);
      begin match ou with
      | None -> TyUnit
      | Some u when u2 = u -> TyUnit
      | _ -> raise @@ Type_bug "subst"
      end
    | MakeArrayExp (f1, f2, u) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      assert (u1 = TyInt);
      assert (u2 = u);
      TyArray u
    | GetExp (f1, f2, ou) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      assert (u2 = TyInt);
      begin match u1, ou with
      | TyArray u, None -> u
      | TyArray u, Some u' when u = u' -> u
      | _ -> raise @@ Type_bug "get"
      end
    | PutExp (f1, f2, f3, ou) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      let u3 = type_of_exp env f3 in
      assert (u2 = TyInt);
      assert (u1 = TyArray u3);
      begin match ou with
      | None -> TyUnit
      | Some u when u3 = u -> TyUnit
      | _ -> raise @@ Type_bug "subst"
      end
    | CoercionExp c -> type_of_coercion c
    | CAppExp (f1, f2) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      begin match u2 with
      | TyCoercion (u21, u22) when u1 = u21 -> u22
      | _ -> raise @@ Type_bug (asprintf "CAppExp")
      end
    | CCompExp (f1, f2) ->
      let u1 = type_of_exp env f1 in
      let u2 = type_of_exp env f2 in
      begin match u1, u2 with
      | TyCoercion (u11, u12), TyCoercion (u21, u22) when u12 = u21 -> TyCoercion (u11, u22)
      | _ -> raise @@ Type_bug (asprintf "CCompExp: %a, %a" pp_ty u1 pp_ty u2)
      end
    | CastExp (f, u1, u2, _) ->
      let u = type_of_exp env f in
      if u = u1 then
        if is_consistent u1 u2 then u2
        else raise @@ Type_bug "not consistent"
      else raise @@ Type_bug "invalid source type"
  and type_of_fund env tvs fd = match fd with
    | FunB ((x, u1), f) ->
      let u2 = type_of_exp (Environment.add x (tysc_of_ty u1) env) f in
      TyScheme (tvs, TyFun (u1, u2))
    | FunS ((x, u1), (k, uk), f) ->
      begin match uk with
      | TyCoercion (uk1, uk2) ->
        let env = Environment.add k (tysc_of_ty uk) (Environment.add x (tysc_of_ty u1) env) in
        let u2' = type_of_exp env f in
        assert (u2' = uk2);
        TyScheme (tvs, TyFun (u1, uk1))
      | _ -> raise @@ Type_bug "FunS uk"
      end
    | FunDual ((x, u1), (k, uk), (f1, f2)) ->
      begin match uk with
      | TyCoercion (uk1, uk2) ->
        let env = Environment.add x (tysc_of_ty u1) env in
        let u2 = type_of_exp env f1 in
        assert (u2 = uk1);
        let env = Environment.add k (tysc_of_ty uk) env in
        let u2' = type_of_exp env f2 in
        assert (u2' = uk2);
        TyScheme (tvs, TyFun (u1, u2))
      | _ -> raise @@ Type_bug "FunDual uk"
      end
    | FunTy f ->
      TyScheme (tvs, type_of_exp env f)
  and type_of_fixd env tvs fixd = match fixd with
    | FixB (x, (y, u1), u2, f) ->
      let env = Environment.add y (tysc_of_ty u1) @@ Environment.add x (tysc_of_ty (TyFun (u1, u2))) env in
      let u2' = type_of_exp env f in
      assert (u2' = u2);
      TyScheme (tvs, TyFun (u1, u2))
    | FixS (x, (y, u1), u2, (k, uk), f) ->
      begin match uk with
      | TyCoercion (uk1, uk2) ->
        assert (uk1 = u2);
        let env = Environment.add k (tysc_of_ty uk) @@ Environment.add y (tysc_of_ty u1) @@ Environment.add x (tysc_of_ty (TyFun (u1, u2))) env in
        let u2' = type_of_exp env f in
        assert (u2' = uk2);
        TyScheme (tvs, TyFun (u1, u2))
      | _ -> raise @@ Type_bug "FixS uk"
      end
    | FixDual (x, (y, u1), u2, (k, uk), (f1, f2)) ->
      begin match uk with
      | TyCoercion (uk1, uk2) ->
        assert (uk1 = u2);
        let env = Environment.add y (tysc_of_ty u1) @@ Environment.add x (tysc_of_ty (TyFun (u1, u2))) env in
        let u2 = type_of_exp env f1 in
        assert (uk1 = u2);
        let u2' = type_of_exp (Environment.add k (tysc_of_ty uk) env) f2 in
        assert (u2' = uk2);
        TyScheme (tvs, TyFun (u1, u2))
      | _ -> raise @@ Type_bug "FixDual uk"
      end

  let type_of_program env = function
    | Exp e -> type_of_exp env e
    | LetDecl (_, f) ->
      let TyScheme (_, u) = match f with
        | FunExp (tvs, fund) -> type_of_fund env tvs fund
        | FixExp (tvs, fixd) -> type_of_fixd env tvs fixd
        | f -> tysc_of_ty (type_of_exp env f)
      in
      u
end
