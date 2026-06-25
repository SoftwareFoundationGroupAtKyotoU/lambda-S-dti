open Pp
open Ftv
open Syntax
open Format
open Type_utils

exception Translation_bug of string

(* These functions (dom, cod, elm, cont, meet) only can be used for normalized types *)
let dom = function
  | TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "dom: instantiated tyvar is given"
  | TyFun (u1, _) -> u1
  | TyDyn -> TyDyn
  | _ as u ->
    raise @@ Translation_bug (asprintf "failed to match: dom(%a)" pp_ty u)

let cod = function
  | TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "cod: instantiated tyvar is given"
  | TyFun (_, u2) -> u2
  | TyDyn -> TyDyn
  | _ as u ->
    raise @@ Translation_bug (asprintf "failed to match: cod(%a)" pp_ty u)

let elm = function
  | TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "elm: instantiated tyvar is given"
  | TyList u -> u
  | TyDyn -> TyDyn
  | _ as u -> raise @@ Translation_bug (asprintf "failed to match: elm(%a)" pp_ty u)

let cont = function
  | TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "cont: instantiated tyvar is given"
  | TyRef u -> u
  | TyDyn -> TyDyn
  | _ as u ->
    raise @@ Translation_bug (asprintf "failed to match: cont(%a)" pp_ty u)

let rec meet u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some _ }), _
  | _, TyVar (_, { contents = Some _ }) ->
    raise @@ Translation_bug "meet: instantiated tyvar is given"
  | TyBool, TyBool -> TyBool
  | TyInt, TyInt -> TyInt
  | TyUnit, TyUnit -> TyUnit
  | TyVar (a1, _ as tv), TyVar (a2, _) when a1 = a2 -> TyVar tv
  | TyDyn, u | u, TyDyn -> u
  | TyFun (u11, u12), TyFun (u21, u22) -> TyFun (meet u11 u21, meet u12 u22)
  | TyList u1, TyList u2 -> TyList (meet u1 u2)
  | TyTuple us1, TyTuple us2 -> TyTuple (List.map2 (fun u1 u2 -> meet u1 u2) us1 us2)
  | TyRef u1, TyRef u2 -> TyRef (meet u1 u2)
  | _ ->
    raise @@ Translation_bug (asprintf "failed to match: meet(%a, %a)" pp_ty u1 pp_ty u2)

module ITGL = struct
  open Syntax.ITGL
  open Tv.ITGL
  open Ftv.ITGL

  let closure_tyvars_let_decl1 e u1 env =
    TV.elements @@ TV.diff (TV.union (tv_exp e) (ftv_ty u1)) (ftv_tyenv env)

  let closure_tyvars2 w1 env u1 v1 =
    let ftvs = TV.big_union [ftv_tyenv env; ftv_ty u1; ftv_exp v1] in
    TV.elements @@ TV.diff (Ftv.CC.ftv_exp w1) ftvs
  
  let closure_tyvars_let_decl2 w1 env u1 v1 =
    let ftvs = TV.big_union [ftv_tyenv env; ftv_ty u1; tv_exp v1] in
    TV.elements @@ TV.diff (Ftv.CC.ftv_exp w1) ftvs

  let cast f r u1 u2 =
    if u1 = u2 then f  (* Omit identity cast for better performance *)
    else CC.CastExp (f, u1, u2, (r, Pos))

  let coerce ~monotonic f r u1 u2 = (* this is not same as ldti about blame label r *)
    if u1 = u2 then f (* Omit identity coercion for better performance *)
    else CC.CAppExp (f, CC.CoercionExp (Coercion.make_s_coercion ~monotonic u1 (r, Pos) u2))
  
  let rec translate_mf env mf = match mf with 
    | MatchILit _ -> env, mf, TyInt
    | MatchBLit _ -> env, mf, TyBool
    | MatchULit -> env, mf, TyUnit
    | MatchWild u -> env, mf, u
    | MatchNil u -> env, mf, TyList u
    | MatchVar (x, u) as mf -> Environment.add x (tysc_of_ty u) env, mf, u
    | MatchCons (mf1, mf2) -> 
      let env, mf2, u2 = translate_mf env mf2 in
      let env, mf1, u1 = translate_mf env mf1 in
      env, MatchCons (mf1, mf2), meet (TyList u1) u2
    | MatchTuple mfs ->
      let rec iter env l r = match l with
      | h :: t ->
        let env, mf, u = translate_mf env h in
        iter env t ((mf, u) :: r)
      | [] -> 
        let mfs, us = List.split (List.rev r) in
        env, MatchTuple mfs, TyTuple us
      in
      iter env mfs []

  let rec translate_exp ~(config:Config.t) env f =
    let c = if config.intoB then cast else coerce ~monotonic:config.monotonic in
    match f with
    | Var (_, x, ys) ->
      begin try
        let TyScheme (xs, u) = Environment.find x env in
        let ftvs = ftv_ty u in
        let s = Utils.List.zip xs !ys in
        let ys = List.map (fun (x, u) -> if TV.mem x ftvs then Ty u else TyNu) s in
        let ys = ys @ Utils.List.repeat TyNu (List.length xs - List.length ys) in
        let u = Subst.subst_type (List.filter (fun (x, _) -> TV.mem x ftvs) s) u in
        CC.Var (x, ys), u
      with Not_found ->
        raise @@ Translation_bug "variable not found during cast-inserting translation"
      end
    | IConst (_, i) -> CC.IConst i, TyInt
    | BConst (_, b) -> CC.BConst b, TyBool
    | UConst _ -> CC.UConst, TyUnit
    | BinOp (_, op, e1, e2) ->
      let ui1, ui2, ui = Typing.type_of_binop op in
      let f1, u1 = translate_exp ~config env e1 in
      let f2, u2 = translate_exp ~config env e2 in
      let r1, r2 = range_of_exp e1, range_of_exp e2 in
      CC.BinOp (op, c f1 r1 u1 ui1, c f2 r2 u2 ui2), ui
    | AscExp (_, e, u1) ->
      let f, u = translate_exp ~config env e in
      let r = range_of_exp e in
      if is_consistent u u1 then
        c f r u u1, u1
      else
        raise @@ Translation_bug "type ascription"
    | IfExp (_, e1, e2, e3) ->
      let f1, u1 = translate_exp ~config env e1 in
      let f2, u2 = translate_exp ~config env e2 in
      let f3, u3 = translate_exp ~config env e3 in
      let r1, r2, r3 = range_of_exp e1, range_of_exp e2, range_of_exp e3 in
      let u = meet u2 u3 in
      CC.IfExp (c f1 r1 u1 TyBool, c f2 r2 u2 u, c f3 r3 u3 u), u
    | FunExp (_, (x, _, u1), e) ->
      let f, u2 = translate_exp ~config (Environment.add x (tysc_of_ty u1) env) e in
      CC.FunExp ([], CC.FunB ((x, u1), f)), TyFun (u1, u2)
    | FixExp (_, x, (y, _, u1), u2, e) ->
      (* NOTE: Disallow to use x polymorphically in e *)
      let env = Environment.add x (tysc_of_ty (TyFun (u1, u2))) env in
      let env = Environment.add y (tysc_of_ty u1) env in
      let f, u2' = translate_exp ~config env e in
      let r = range_of_exp e in
      CC.FixExp ([], CC.FixB (x, (y, u1), u2, c f r u2' u2)), TyFun (u1, u2)
    | AppExp (_, e1, e2) ->
      let f1, u1 = translate_exp ~config env e1 in
      let f2, u2 = translate_exp ~config env e2 in
      let r1, r2 = range_of_exp e1, range_of_exp e2 in
      (* Format.fprintf std_formatter "u1: %a, u2: %a\n" Pp.pp_ty u1 Pp.pp_ty u2; *)
      CC.AppMExp (c f1 r1 u1 (TyFun (dom u1, cod u1)), c f2 r2 u2 (dom u1)), cod u1
    | MatchExp (r, e, ms) -> 
      let f, u = translate_exp ~config env e in
      let msu, (u_match, u_exp) = translate_ms ~config env ms in
      CC.MatchExp (c f r u u_match, List.map (fun (mf, f, u) -> mf, c f r u u_exp) msu), u_exp
    | LetExp (_, x, e1, e2) when Typing.ITGL.is_pure_value env e1 ->
      let f1, u1 = translate_exp ~config env e1 in
      let xs = Typing.ITGL.closure_tyvars1 u1 env e1 in
      let ys = closure_tyvars2 f1 env u1 e1 in
      let xys = xs @ ys in
      let us1 = TyScheme (xys, u1) in
      let f2, u2 = translate_exp ~config (Environment.add x us1 env) e2 in
      begin match f1 with
      | CC.FunExp (_, CC.FunB ((y, u1), f)) ->
        CC.LetExp (x, CC.FunExp (xys, CC.FunB ((y, u1), f)), f2), u2
      | CC.FixExp (_, fixd) ->
        CC.LetExp (x, CC.FixExp (xys, fixd), f2), u2
      | _ ->
        if xys <> [] then CC.LetExp (x, CC.FunExp (xys, CC.FunTy f1), f2), u2
        else CC.LetExp (x, f1, f2), u2
      end
    | LetExp (_, x, e1, e2) ->
      let f1, u1 = translate_exp ~config env e1 in
      let f2, u2 = translate_exp ~config (Environment.add x (tysc_of_ty u1) env) e2 in
      CC.LetExp (x, f1, f2), u2
    | NilExp (_, u) -> CC.NilExp u, TyList u
    | ConsExp (r, e1, e2) ->
      let f1, u1 = translate_exp ~config env e1 in
      let f2, u2 = translate_exp ~config env e2 in
      let u_elm = meet u1 (elm u2) in (* TyDyn であれば TyList TyDyn にする *)
      let u_list = TyList u_elm in
      CC.ConsExp (c f1 r u1 u_elm, c f2 r u2 u_list), u_list
    | TupleExp (_, es) ->
      let fs, us = List.split (List.map (fun e -> translate_exp ~config env e) es) in
      CC.TupleExp fs, TyTuple us
    | RefExp (_, e) ->
      let f, u = translate_exp ~config env e in
      CC.RefExp (f, u), TyRef u
    | DerefExp (r, e) ->
      let f, u = translate_exp ~config env e in
      let u' = cont u in
      if Type_utils.is_static_type u then CC.DerefExp (f, None), u'
      else CC.DerefExp (c f r u (TyRef u'), Some u'), u'
    | SubstExp (r, e1, e2) ->
      let f1, u1 = translate_exp ~config env e1 in
      let f2, u2 = translate_exp ~config env e2 in
      let u1' = cont u1 in
      if Type_utils.is_static_type u1 && u1' = u2 then CC.SubstExp (f1, f2, None), TyUnit
      else CC.SubstExp (c f1 r u1 (TyRef u1'), c f2 r u2 u1', Some u1'), TyUnit
    (* | _ -> raise @@ Translation_bug "yet" *)
  and translate_ms ~config env = function
    | (mf, e) :: t ->
      if t = [] then
        let env', mf, u_match = translate_mf env mf in
        let f, u_exp = translate_exp ~config env' e in
        [mf, f, u_exp], (u_match, u_exp)
      else
        let env', mf, u_match = translate_mf env mf in
        let f, u_exp = translate_exp ~config env' e in
        let t, (u_match', u_exp') = translate_ms ~config env t in
        (mf, f, u_exp) :: t, (meet u_match u_match', meet u_exp u_exp')
    | [] -> raise @@ Translation_bug "translate_ms: empty match"

  let translate ~config env = function
    | Exp e ->
      let f, u = translate_exp ~config env e in
      env, CC.Exp f, u
    | LetDecl (x, e) ->
      let f, u = translate_exp ~config env e in
      let tvs =
        if Typing.ITGL.is_pure_value env e then
          let xs = closure_tyvars_let_decl1 e u env in
          let ys = closure_tyvars_let_decl2 f env u e in
          xs @ ys
        else
          []
      in
      let env = Environment.add x (TyScheme (tvs, u)) env in
      begin match f with
      | CC.FunExp (_, fund) ->
        env, CC.LetDecl (x, CC.FunExp (tvs, fund)), u
      | CC.FixExp (_, fixd) ->
        env, CC.LetDecl (x, CC.FixExp (tvs, fixd)), u
      | _ ->
        if tvs <> [] then env, CC.LetDecl (x, CC.FunExp (tvs, CC.FunTy f)), u
        else env, CC.LetDecl (x, f), u
      end
end

module CC = struct
  open Syntax.CC

  let fresh_CVar =
    let counter = ref 0 in
    fun () -> incr counter; "k" ^ string_of_int !counter

  let rec translate_mf env = function
    | MatchILit _ | MatchBLit _ | MatchULit | MatchWild _ | MatchNil _ as mf -> env, mf
    | MatchVar (x, u) as mf -> Environment.add x (tysc_of_ty u) env, mf
    | MatchCons (mf1, mf2) ->
      let env, mf1 = translate_mf env mf1 in
      let env, mf2 = translate_mf env mf2 in
      env, MatchCons (mf1, mf2)
    | MatchTuple mfs ->
      let rec iter env l r = match l with
      | h :: t ->
        let env, mf = translate_mf env h in
        iter env t (mf :: r)
      | [] ->
        env, MatchTuple (List.rev r)
      in
      iter env mfs []

  let rec translate_exp ~(config: Config.t) env = function
    | Var (x, ys) ->
      let TyScheme (xs, u) = Environment.find x env in
      let ftvs = ftv_ty u in
      let s = Utils.List.zip xs ys in
      let s = List.filter (fun (x, _) -> TV.mem x ftvs) s in
      let s = List.map (fun (x, u) -> x, Type_utils.tyarg_to_ty u) s in
      let u = Subst.subst_type s u in
      Var (x, ys), u
    | IConst i -> IConst i, TyInt
    | BConst b -> BConst b, TyBool
    | UConst -> UConst, TyUnit
    | NilExp u -> NilExp u, TyList u
    | BinOp (op, f1, f2) ->
      let f1, u1 = translate_exp ~config env f1 in
      let f2, u2 = translate_exp ~config env f2 in
      let ui1, ui2, ui = Typing.type_of_binop op in
      assert (u1 = ui1);
      assert (u2 = ui2);
      BinOp (op, f1, f2), ui
    | ConsExp (f1, f2) ->
      let f1, u1 = translate_exp ~config env f1 in
      let f2, u2 = translate_exp ~config env f2 in
      assert (u2 = TyList u1);
      ConsExp (f1, f2), u2
    | TupleExp fs ->
      let pairs = List.map (translate_exp ~config env) fs in
      let fs, us = List.split pairs in
      TupleExp fs, TyTuple us
    | RefExp (f, u) ->
      let f, u' = translate_exp ~config env f in
      assert (u' = u);
      RefExp (f, u), TyRef u
    | DerefExp (f, u_opt) ->
      let f, u = translate_exp ~config env f in
      begin match u with
      | TyRef u ->
        (match u_opt with Some u' -> assert (u = u') | None -> ());
        DerefExp (f, u_opt), u
      | _ -> raise @@ Translation_bug "DerefExp"
      end
    | SubstExp (f1, f2, u_opt) ->
      let f1, u1 = translate_exp ~config env f1 in
      let f2, u2 = translate_exp ~config env f2 in
      assert (u1 = TyRef u2);
      (match u_opt with Some u -> assert (u = u2) | None -> ());
      SubstExp (f1, f2, u_opt), TyUnit
    | IfExp (f1, f2, f3) ->
      let f1, u1 = translate_exp ~config env f1 in
      let f2, u2 = translate_exp ~config env f2 in
      let f3, u3 = translate_exp ~config env f3 in
      assert (u1 = TyBool);
      assert (u2 = u3);
      IfExp (f1, f2, f3), u2
    | LetExp (x, f1, f2) ->
      let f1, u1 = translate_exp ~config env f1 in
      let tvs = match f1 with FunExp (tvs, _) | FixExp (tvs, _) -> tvs | _ -> [] in
      let env = Environment.add x (TyScheme (tvs, u1)) env in
      let f2, u2 = translate_exp ~config env f2 in
      LetExp (x, f1, f2), u2
    | MatchExp (f, ms) ->
      let f, _ = translate_exp ~config env f in
      let msu = List.map (fun (mf, f) ->
        let env, mf = translate_mf env mf in
        let f, u = translate_exp ~config env f in
        ((mf, f), u)
      ) ms in
      let ms, us = List.split msu in
      let u = List.hd us in
      List.iter (fun u' -> assert (u = u')) us;
      MatchExp (f, ms), u
    | FunExp (tvs, FunB ((x, u1), f)) ->
      let env = Environment.add x (tysc_of_ty u1) env in
      let f_direct, u2 = translate_exp ~config env f in
      let fund = 
        if config.intoB then FunB ((x, u1), f_direct)
        else
          let id = fresh_CVar () in
          let u_ans = Type_utils.fresh_tyvar () in
          let uk = TyCoercion (u2, u_ans) in
          let env = Environment.add id (tysc_of_ty uk) env in
          let k = Var (id, []) in
          let f_cps, u2' = translate_exp_k ~config env k u2 u_ans f in
          assert (u2' = u_ans);
          if config.alt && not config.compile then FunDual ((x, u1), (id, uk), (f_direct, f_cps))
            (* NOTE: when generating C, alternative translation is done in closure conversion *)
          else FunS ((x, u1), (id, uk), f_cps)
      in
      FunExp (tvs, fund), TyFun (u1, u2)
    | FunExp (tvs, FunTy f) ->
      let f, u = translate_exp ~config env f in
      FunExp (tvs, FunTy f), u
    | FixExp (tvs, FixB (x, (y, u1), u2, f)) ->
      let env = Environment.add x (tysc_of_ty (TyFun (u1, u2))) @@ Environment.add y (tysc_of_ty u1) env in
      let f_direct, u2' = translate_exp ~config env f in
      assert (u2 = u2');
      let fixd =
        if config.intoB then FixB (x, (y, u1), u2, f_direct)
        else
          let id = fresh_CVar () in
          let u_ans = Type_utils.fresh_tyvar () in
          let uk = TyCoercion (u2, u_ans) in
          let env = Environment.add id (tysc_of_ty uk) env in
          let k = Var (id, []) in
          let f_cps, u2' = translate_exp_k ~config env k u2 u_ans f in
          assert (u2' = u_ans);
          if config.alt && not config.compile then FixDual (x, (y, u1), u2, (id, uk), (f_direct, f_cps))
            (* NOTE: when generating C, alternative translation is done in closure conversion *)
          else FixS (x, (y, u1), u2, (id, uk), f_cps)
      in
      FixExp (tvs, fixd), TyFun (u1, u2)
    | AppMExp (f1, f2) ->
      let f1, u1 = translate_exp ~config env f1 in
      let f2, u2 = translate_exp ~config env f2 in
      begin match u1 with
      | TyFun (u_dom, u_ret) -> 
        assert (u_dom = u2);
        if config.intoB || config.alt then AppMExp (f1, f2), u_ret
        else AppDExp (f1, (f2, CoercionExp (CId u_ret))), u_ret
      | _ -> raise @@ Translation_bug "AppMExp"
      end
    | CAppExp (f1, (CoercionExp c as f2)) ->
      let u = Typing.type_of_coercion c in
      begin match u with
      | TyCoercion (u_src, u_tgt) -> translate_exp_k ~config env f2 u_src u_tgt f1
      | _ -> raise @@ Translation_bug "CAppExp"
      end
    | CastExp (f, u1, u2, r_p) ->
      let f, u = translate_exp ~config env f in
      assert (u = u1);
      CastExp (f, u1, u2, r_p), u2
    | AppDExp _ | CSeqExp _ | CoercionExp _ | FunExp _ | FixExp _ | CAppExp _ as f ->
      raise @@ Occur_LS1 (Format.asprintf "CC.translate_exp: already CPS:: %a" Pp.CC.pp_exp f)
  and translate_exp_k ~config env k uk1 uk2 = function
    | Var _ | IConst _ | BConst _ | UConst | NilExp _ | BinOp _ | FunExp _ | FixExp _
    | ConsExp _ | TupleExp _ | RefExp _ | DerefExp _ | SubstExp _ as f ->
      let f, u = translate_exp ~config env f in
      assert (u = uk1);
      CAppExp (f, k), uk2
    | IfExp (f1, f2, f3) ->
      let f1, u1 = translate_exp ~config env f1 in
      assert (u1 = TyBool);
      let f2, u2 = translate_exp_k ~config env k uk1 uk2 f2 in
      let f3, u3 = translate_exp_k ~config env k uk1 uk2 f3 in
      assert (u2 = u3);
      IfExp (f1, f2, f3), uk2
    | LetExp (x, f1, f2) ->
      let f1, u1 = translate_exp ~config env f1 in
      let tvs = match f1 with FunExp (tvs, _) | FixExp (tvs, _) -> tvs | _ -> [] in
      let env = Environment.add x (TyScheme (tvs, u1)) env in
      let f2, u2 = translate_exp_k ~config env k uk1 uk2 f2 in
      assert (u2 = uk2);
      LetExp (x, f1, f2), uk2
    | MatchExp (f, ms) ->
      let f, _ = translate_exp ~config env f in
      let msu = List.map (fun (mf, f) ->
        let env, mf = translate_mf env mf in
        let f, u = translate_exp_k ~config env k uk1 uk2 f in
        ((mf, f), u)
      ) ms in
      let ms, us = List.split msu in
      let u = List.hd us in
      assert (u = uk2);
      List.iter (fun u' -> assert (u = u')) us;
      MatchExp (f, ms), uk2
    | AppMExp (f1, f2) ->
      let f1, u1 = translate_exp ~config env f1 in
      let f2, u2 = translate_exp ~config env f2 in
      assert (u1 = TyFun (u2, uk1));
      AppDExp (f1, (f2, k)), uk2
    | CAppExp (f1, (CoercionExp c as f2)) ->
      let u = Typing.type_of_coercion c in
      begin match u with
      | TyCoercion (u_src_c, u_mid) ->
        assert (u_mid = uk1);
        let id = fresh_CVar () in
        let u_composed = TyCoercion (u_src_c, uk2) in
        let env = Environment.add id (tysc_of_ty u_composed) env in
        let k' = Var (id, []) in
        let f, u = translate_exp_k ~config env k' u_src_c uk2 f1 in
        assert (u = uk2);
        LetExp (id, CSeqExp (f2, k), f), uk2
      | _ -> raise @@ Translation_bug "CAppExp"
      end
    | CastExp _ -> raise @@ Translation_bug "translate_exp_k CastExp"
    | AppDExp _ | CSeqExp _ | CoercionExp _ | CAppExp _ as f ->
      raise @@ Occur_LS1 (Format.asprintf "CC.translate_exp: already CPS:: %a" Pp.CC.pp_exp f)

  let translate ~config env = function
    | Exp f ->
      let f, u = translate_exp ~config env f in
      Exp f, u
    | LetDecl (x, f) ->
      let f, u = translate_exp ~config env f in
      LetDecl (x, f), u
end