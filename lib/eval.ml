open Format
open Syntax

exception Eval_bug of string

let subst_type = Typing.subst_type

let fresh_tyvar = Typing.fresh_tyvar

let type_of_tag = Typing.type_of_tag

let tag_of_ty = Typing.tag_of_ty

let nu_to_fresh = function
| Ty u -> u
| TyNu -> Typing.fresh_tyvar ()

let rec subst_mf s = function
  | MatchILit _ | MatchBLit _ | MatchULit as mf -> mf
  | MatchWild u -> MatchWild (subst_type s u)
  | MatchVar (x, u) -> MatchVar (x, subst_type s u)
  | MatchNil u -> MatchNil (subst_type s u)
  | MatchCons (mf1, mf2) -> MatchCons (subst_mf s mf1, subst_mf s mf2)

let rec normalize_coercion c = match c with
  | CId TyDyn -> c
  | CSeq (CProj _ as c1, c2) -> CSeq (c1, normalize_coercion c2)
  | CTvProj ((_, {contents = Some u}), p) when is_base_type u ->
    normalize_coercion (CSeq (CProj (tag_of_ty u, p), CId u))
  | CTvProj ((_, {contents = Some (TyVar tv)}), p) ->
    normalize_coercion (CTvProj (tv, p))
  | CTvProj ((_, {contents = Some (TyFun (TyVar tv1, TyVar tv2))}), p) ->
    normalize_coercion (CSeq (CProj (Ar, p), CFun (CTvInj tv1, CTvProj (tv2, p))))
  | CTvProj ((_, {contents = Some (TyList (TyVar tv))}), p) ->
    normalize_coercion (CSeq (CProj (Li, p), CList (CTvProj (tv, p))))
  | CTvProj ((_, {contents = None}), _) -> c
  | CTvInj (_, {contents = Some u }) when is_base_type u ->
    normalize_coercion (CSeq (CId u, CInj (tag_of_ty u)))
  | CTvInj (_, {contents = Some (TyVar tv)}) ->
    normalize_coercion (CTvInj tv)
  | CTvInj (_, {contents = Some (TyFun (TyVar tv1, TyVar tv2))}) ->
    normalize_coercion (CSeq (CFun (CTvProj (tv1, (Utils.Error.dummy_range, Pos)), CTvInj tv2), CInj Ar))
  | CTvInj (_, {contents = Some (TyList (TyVar tv))}) ->
    normalize_coercion (CSeq (CList (CTvInj tv), CInj Li))
  | CTvInj (_, {contents = None}) -> c
  | CTvProjInj ((_, {contents = Some u}), p) when is_base_type u ->
    normalize_coercion (CSeq (CProj (tag_of_ty u, p), CSeq (CId u, CInj (tag_of_ty u))))
  | CTvProjInj ((_, {contents = Some (TyVar tv)}), p) ->
    normalize_coercion (CTvProjInj (tv, p))
  | CTvProjInj ((_, {contents = Some (TyFun (TyVar tv1, TyVar tv2))}), p) ->
    normalize_coercion (CSeq (CProj (Ar, p), CSeq (CFun (CTvProjInj (tv1, (Utils.Error.dummy_range, Pos)), CTvProjInj (tv2, p)), CInj Ar)))
  | CTvProjInj ((_, {contents = Some (TyList (TyVar tv))}), p) ->
    normalize_coercion (CSeq (CProj (Li, p), CSeq (CList (CTvProjInj (tv, p)), CInj Li)))
  | CTvProjInj ((_, {contents = None}), _) -> c
  | CSeq (c1, (CInj _ as c2)) -> CSeq (normalize_coercion c1, c2)
  | CFail _ as c -> c
  | CId (TyVar (_, {contents = Some u})) -> normalize_coercion (CId u)
  | CId _ as c -> c
  | CFun (s, t) -> 
    let s' = normalize_coercion s in
    let t' = normalize_coercion t in
    begin match s', t' with
      | CId u1, CId u2 -> CId (TyFun (u1, u2))
      | _ -> CFun (s', t')
    end
  | CList s -> 
    let s' = normalize_coercion s in
    begin match s' with
      | CId u -> CId (TyList u)
      | _ -> CList s'
    end
  | CTvProj ((i, {contents = Some (TyFun (u1, u2))}), p) -> 
    normalize_coercion (CSeq (CProj (Ar, p), CFun (CTvInj (i, ref (Some u1)), CTvProj ((i, ref (Some u2)), p))))
  | CTvInj (i, {contents = Some (TyFun (u1, u2))}) -> 
    normalize_coercion (CSeq (CFun (CTvProj ((i, ref (Some u1)), (Utils.Error.dummy_range, Pos)), CTvInj (i, ref (Some u2))), CInj Ar))
  | CTvProjInj ((i, {contents = Some (TyFun (u1, u2))}), p) ->
    normalize_coercion (CSeq (CProj (Ar, p), CSeq (CFun (CTvProjInj ((i, ref (Some u1)), (Utils.Error.dummy_range, Pos)), CTvProjInj ((i, ref (Some u2)), p)), CInj Ar)))
  | c -> raise @@ Eval_bug (Format.asprintf "cannot normalize coercion: %a" Pp.pp_coercion c)

let rec subst_coercion s = function
| CInj _ | CProj _ as c -> c
| CTvInj (a, _ as tv) -> 
  let u = subst_type s (TyVar tv) in
  normalize_coercion (CTvInj (a, {contents = Some u}))
| CTvProj ((a, _ as tv), p) ->
  let u = subst_type s (TyVar tv) in
  normalize_coercion (CTvProj ((a, {contents = Some u}), p))
| CTvProjInj ((a, _ as tv), p) -> 
  let u = subst_type s (TyVar tv) in
  normalize_coercion (CTvProjInj ((a, {contents = Some u}), p))
| CFun (c1, c2) -> CFun (subst_coercion s c1, subst_coercion s c2)
| CList c -> CList (subst_coercion s c)
| CId u -> CId (subst_type s u)
| CSeq (c1, c2) -> CSeq (subst_coercion s c1, subst_coercion s c2)
| CFail _ as c -> c

let rec compose ?(debug=false) c1 c2 = (* TODO : blame *)
  if debug then fprintf err_formatter "compose <-- %a；%a\n" Pp.pp_coercion c1 Pp.pp_coercion c2;
  let compose = compose ~debug:debug in
  match normalize_coercion c1, normalize_coercion c2 with
  (* id{star} ;;; t *)
  | CId TyDyn, c2 -> c2
  (* G?p;i ;;; t *)
  | CSeq (CProj (t, p), c1), c2 -> CSeq (CProj (t, p), compose c1 c2)
  (* X?p ;;; t *)
  | CTvProj ((a1, _ as tv), p), CId (TyVar (a2, _)) when a1 = a2 -> CTvProj (tv, p)
  | CTvProj ((a1, _ as tv), p), CTvInj (a2, _) when a1 = a2 -> CTvProjInj (tv, p)
  (* X! ;;; t *)
  | CTvInj tv, CId TyDyn -> CTvInj tv
  | CTvInj (_, uref as tv), CSeq (CProj (Ar, (r, p)), c2) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n" Pp.pp_ty (TyVar tv) Pp.pp_ty (TyFun (x1, x2));
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose (CFun (CTvProj (tv1, (r, neg p)), (CTvInj tv2))) c2
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CTvInj (_, uref as tv), CSeq (CProj (Li, _), c2) ->
    let x1 = fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n" Pp.pp_ty (TyVar tv) Pp.pp_ty (TyList x1);
    uref := Some (TyList x1);
    begin match x1 with
      | TyVar tv1 ->
        compose (CList (CTvInj tv1)) c2
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CTvInj (_, uref as tv), CSeq (CProj (t, _), c2) -> 
    let u = type_of_tag t in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n" Pp.pp_ty (TyVar tv) Pp.pp_ty u;
    uref := Some u;
    compose (CId u) c2
  | CTvInj (a1, uref as tv1), CTvProj ((a2, _ as tv2), _) -> 
    if a1 = a2 then CId (TyVar tv1)
    else begin 
      if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n" Pp.pp_ty (TyVar tv1) Pp.pp_ty (TyVar tv2);
      uref := Some (TyVar tv2); 
      CId (TyVar tv2)
    end
  | CTvInj tv1, CTvProjInj (tv2, p) ->
    compose (compose (CTvInj tv1) (CTvProj (tv2, p))) (CTvInj tv2)
    (* if a1 = a2 then CTvInj tv1
    else (uref := Some (TyVar tv2); CTvInj tv2) *)
  (* ?pX! ;;; t *)
  | CTvProjInj (tv, p), c2 ->
    compose (CTvProj (tv, p)) (compose (CTvInj tv) c2)
  (* | CTvProjInj (tv, p), CId TyDyn -> CTvProjInj (tv, p)
  | CTvProjInj ((_, uref), p), CSeq (CProj (Ar, (r', q)), c2) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
    | TyVar tv1, TyVar tv2 ->
      compose (CSeq (CProj (Ar, p), CFun (CTvProjInj (tv1, (r', neg q)), CTvProjInj (tv2, p)))) c2
    | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CTvProjInj ((_, uref), p), CSeq (CProj (t, _), c2) -> 
    uref := Some (type_of_tag t);
    compose (CSeq (CProj (t, p), CId (type_of_tag t))) c2
  | CTvProjInj ((a1, uref as tv1), p), CTvProj ((a2, _ as tv2), _) -> 
    if a1 = a2 then CTvProj (tv1, p)
    else (uref := Some (TyVar tv2); CTvProj (tv2, p))
  | CTvProjInj ((a1, uref as tv1), p), CTvProjInj ((a2, _ as tv2), _) ->
    if a1 = a2 then CTvProjInj (tv1, p)
    else (uref := Some (TyVar tv2); CTvProjInj (tv2, p)) *)
  (* i ;;; t *)
  | CSeq (_, CInj _) as c1, CId TyDyn -> c1
  | CSeq (c1, CInj t), CSeq (CProj (t', p), c2) ->
    if t = t' then compose c1 c2 
    else CFail (t, p, t')
  | CSeq (c1, CInj Ar), CTvProj ((_, uref as tv), p) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n" Pp.pp_ty (TyVar tv) Pp.pp_ty (TyFun (x1, x2));
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose c1 (CFun (CTvInj tv1, CTvProj (tv2, p)))
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj Li), CTvProj ((_, uref as tv), p) ->
    let x1 = fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n" Pp.pp_ty (TyVar tv) Pp.pp_ty (TyList x1);
    uref := Some (TyList x1);
    begin match x1 with
      | TyVar tv1 ->
        compose c1 (CList (CTvProj (tv1, p)))
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj t), CTvProj ((_, uref as tv), _) ->
    let u = type_of_tag t in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n" Pp.pp_ty (TyVar tv) Pp.pp_ty u;
    uref := Some u;
    compose c1 (CId u)
  | CSeq (_, (CInj _)) as c1, CTvProjInj (tv, p) ->
    compose (compose c1 (CTvProj (tv, p))) (CTvInj tv)
  (* | CSeq (c1, CInj Ar), CTvProjInj ((_, uref), (r, p)) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose c1 (CSeq (CFun (CTvProjInj (tv1, (r, neg p)), CTvProjInj (tv2, (r, p))), CInj Ar))
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj t), CTvProjInj ((_, uref), _) ->
    uref := Some (type_of_tag t);
    compose c1 (CSeq (CId (type_of_tag t), CInj t)) *)
  | CFail _ as c1, _ -> c1
  (* g ;;; i *)
  | _, (CFail _ as c2) (*when is_g c1*) -> c2
  | c1, CSeq (c2, CInj t) (*when is_g c1*) -> CSeq (compose c1 c2, CInj t)
  (* g ;;; g *)
  | CId _, c2 -> c2
  | c1, CId _ -> c1
  | CFun (s, t), CFun (s', t') ->
    let c1 = compose s' s in
    let c2 = compose t t' in
    begin match c1, c2 with
      | CId u1, CId u2 -> CId (TyFun (u1, u2))
      | _ -> CFun (c1, c2) 
    end
  | CList s, CList s' ->
    let c = compose s s' in
    begin match c with
      | CId u -> CId (TyList u)
      | _ -> CList c
    end
  | _ -> raise @@ Eval_bug "cannot compose coercions"

module LS1 = struct
  open Syntax.LS1

  let rec subst_exp s = function
    | Var (x, ys) ->
      let subst_type = function
        | Ty u -> Ty (subst_type s u)
        | TyNu -> TyNu
      in
      Var (x, List.map subst_type ys)
    | IConst _
    | BConst _
    | UConst as f -> f
    | BinOp (op, f1, f2) -> BinOp (op, subst_exp s f1, subst_exp s f2)
    | IfExp (f1, f2, f3) -> IfExp (subst_exp s f1, subst_exp s f2, subst_exp s f3)
    | FunExp ((x1, u1), k, f) -> FunExp ((x1, subst_type s u1), k, subst_exp s f)
    | FixExp ((x, y, u1, u2), k, f) ->
      FixExp ((x, y, subst_type s u1, subst_type s u2), k, subst_exp s f)
    | AppExp (f1, f2, f3) -> AppExp (subst_exp s f1, subst_exp s f2, subst_exp s f3)
    | CAppExp (f1, f2) -> CAppExp (subst_exp s f1, subst_exp s f2)
    | CSeqExp (f1, f2) -> CSeqExp (subst_exp s f1, subst_exp s f2)
    | MatchExp (f, ms) -> 
      MatchExp (subst_exp s f, List.map (fun (mf, f) -> subst_mf s mf, subst_exp s f) ms)
    | LetExp (y, ys, f1, f2) ->
      (* Remove substitutions captured by let exp s *)
      let s = List.filter (fun (x, _) -> not @@ List.memq x ys) s in
      LetExp (y, ys, subst_exp s f1, subst_exp s f2)
    | CoercionExp c -> CoercionExp (subst_coercion s c)
    | NilExp u -> NilExp (subst_type s u)
    | ConsExp (f1, f2) -> ConsExp (subst_exp s f1, subst_exp s f2)
    | FunExp_alt ((x1, u1), k, (f1, f2)) -> FunExp_alt ((x1, subst_type s u1), k, (subst_exp s f1, subst_exp s f2))
    | FixExp_alt ((x, y, u1, u2), k, (f1, f2)) ->
      FixExp_alt ((x, y, subst_type s u1, subst_type s u2), k, (subst_exp s f1, subst_exp s f2))
    | AppExp_alt (f1, f2) -> AppExp_alt (subst_exp s f1, subst_exp s f2)

  let eval_binop op v1 v2 =
    begin match op, v1, v2 with
      | Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
      | Minus, IntV i1, IntV i2 -> IntV (i1 - i2)
      | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
      | Div, IntV i1, IntV i2 -> IntV (i1 / i2)
      | Mod, IntV i1, IntV i2 -> IntV (i1 mod i2)
      | Eq, IntV i1, IntV i2 -> BoolV (i1 = i2)
      | Neq, IntV i1, IntV i2 -> BoolV (i1 <> i2)
      | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
      | Lte, IntV i1, IntV i2 -> BoolV (i1 <= i2)
      | Gt, IntV i1, IntV i2 -> BoolV (i1 > i2)
      | Gte, IntV i1, IntV i2 -> BoolV (i1 >= i2)
      | _ -> raise @@ Eval_bug "binop: unexpected type of argument"
    end

  let rec eval ?(debug=false) (env: (tyvar list * value) Environment.t) f =
    if debug then fprintf err_formatter "eval <-- %a\n" Pp.LS1.pp_exp f;
    let eval = eval ~debug:debug in
    match f with
    | Var (x, us) ->
      let xs, v = Environment.find x env in
      let us = List.map nu_to_fresh us in
      begin match v with
        | FunV proc -> FunV (fun _ -> proc (xs, us))
        | FunV_alt proc -> FunV_alt (fun _ -> proc (xs, us))
        | _ -> v
      end
    | IConst i -> IntV i
    | BConst b -> BoolV b
    | UConst -> UnitV
    | BinOp (op, f1, f2) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      eval_binop op v1 v2
    | FunExp ((x, _), k, f') ->
      FunV (
        fun (xs, ys) -> fun (v, w) ->
          eval (Environment.add x ([], v) (Environment.add k ([], w) env)) @@ subst_exp (Utils.List.zip xs ys) f'
      )
    | FixExp ((x, y, _, _), k, f') ->
      let f (xs, ys) (v, w) =
        let f' = subst_exp (Utils.List.zip xs ys) f' in
        let rec f _ (v, w) =
          let env = Environment.add x (xs, FunV f) env in
          let env = Environment.add y ([], v) env in
          let env = Environment.add k ([], w) env in
          eval env f'
        in f ([], []) (v, w)
      in FunV f
    | AppExp (f1, f2, f3) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      let v3 = eval env f3 in
      eval_app_val env v1 v2 v3 ~debug:debug
    | IfExp (f1, f2, f3) ->
      let v1 = eval env f1 in
      begin match v1 with
        | BoolV true -> eval env f2
        | BoolV false -> eval env f3
        | _ -> raise @@ Eval_bug "if: non boolean value"
      end
    | LetExp (x, xs, f1, f2) ->
      let v1 = eval env f1 in
      eval (Environment.add x (xs, v1) env) f2
    | CAppExp (f1, f2) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      begin match v2 with
        | CoercionV c -> coerce ~debug:debug v1 c
        | _ -> raise @@ Eval_bug "capp: application of non coercion value"
      end
    | CSeqExp (f1, f2) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      begin match v1, v2 with
        | CoercionV c1, CoercionV c2 -> CoercionV (compose c1 c2 ~debug:debug)
        | _ -> raise @@ Eval_bug "cseq: sequence of non coercion value"
      end
    | CoercionExp c -> CoercionV c
    | MatchExp (f, ms) ->
      let v = eval env f in
      eval_next ~debug:debug env v ms
    | NilExp _ -> NilV
    | ConsExp (f1, f2) ->
      let v2 = eval env f2 in
      let v1 = eval env f1 in
      ConsV (v1, v2)
    | AppExp_alt (f1, f2) ->
      let v1 = eval env f1 in
      let v2 = eval env f2 in
      eval_app_val_alt env v1 v2 ~debug:debug
    | FunExp_alt ((x, _), k, (f', f'')) ->
      FunV_alt (
        fun (xs, ys) -> 
          (fun v -> eval (Environment.add x ([], v) env) @@ subst_exp (Utils.List.zip xs ys) f'),
          (fun (v, w) -> eval (Environment.add x ([], v) (Environment.add k ([], w) env)) @@ subst_exp (Utils.List.zip xs ys) f'')
      )
    | FixExp_alt ((x, y, _, _), k, (f', f'')) ->
      let f (xs, ys) =
        let f' = subst_exp (Utils.List.zip xs ys) f' in
        let f'' = subst_exp (Utils.List.zip xs ys) f'' in
        let rec f1' v =
          let env = Environment.add x (xs, FunV_alt (fun _ -> (f1', f2'))) env in
          let env = Environment.add y ([], v) env in
          eval env f'
        and f2' (v, w) =
          let env = Environment.add x (xs, FunV_alt (fun _ -> (f1', f2'))) env in
          let env = Environment.add y ([], v) env in
          let env = Environment.add k ([], w) env in
          eval env f''
        in (f1', f2')
      in FunV_alt f
  and match_mf ?(debug=false) env v mf = match v, mf with
    | _, MatchVar (id, _) ->
      let env = Environment.add id ([], v) env in
      true, env
    | ConsV (v1, v2), MatchCons (mf1, mf2) ->
      let b1, env = match_mf ~debug:debug env v1 mf1 in
      let b2, env = match_mf ~debug:debug env v2 mf2 in
      b1&&b2, env 
    | NilV, MatchNil _ -> true, env
    | IntV i1, MatchILit i2 -> if i1 = i2 then (true, env) else (false, env)
    | BoolV b1, MatchBLit b2 -> if b1 = b2 then (true, env) else (false, env)
    | UnitV, MatchULit -> true, env
    (* | arg, MatchAsc (mf, _) -> match_mf env arg mf *)
    | _, MatchWild _ -> true, env
    | CoerceV (ConsV (v1, v2), CList s), MatchCons _ -> 
      match_mf ~debug:debug env (ConsV (coerce ~debug:debug v1 s, coerce ~debug:debug v2 (CList s))) mf (* lazy *)
    | _ -> false, env 
  and eval_next ?(debug=false) env v ms = match ms with
    | (mf, f) :: ms ->
      let b, env' = match_mf ~debug:debug env v mf in
      if b then eval ~debug:debug env' f
      else eval_next ~debug:debug env v ms
    | [] -> raise @@ Eval_bug "Didn't match"
  and coerce ?(debug=false) v c =
    let print_debug f = Utils.Format.make_print_debug debug f in
    print_debug "coerce <-- %a<%a>\n" Pp.LS1.pp_value v Pp.pp_coercion c;
    let coerce = coerce ~debug:debug in
    match v with
    | CoerceV (v, c') -> coerce v (compose c' c ~debug:debug)
    | v -> match normalize_coercion c with
      | CId _ -> v
      | CFail (_, (r, p), _) -> raise @@ Blame (r, p)
      (* | CTvInj (_, {contents=None}) -> raise @@ Eval_bug "coerce: coercion with uninstantiated type variable" *)
      | c when is_d c -> CoerceV (v, c)
      | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a <%a>" Pp.LS1.pp_value v Pp.pp_coercion c)
  and eval_app_val ?(debug=false) env v1 v2 v3 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunV proc -> proc ([], []) (v2, v3) 
    | FunV_alt proc -> snd (proc ([], [])) (v2, v3)
    | CoerceV (v1, CFun (s, t)) -> 
      begin match v3 with
        | CoercionV c -> 
          let k = CoercionV (compose t c ~debug:debug) in
          eval_app_val env v1 (coerce v2 s ~debug:debug) k ~debug:debug
        | _ -> raise @@ Eval_bug "app: application of non coercion value"
      end
    | _ -> raise @@ Eval_bug "app: application of non procedure value"
  and eval_app_val_alt ?(debug=false) env v1 v2 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunV_alt proc -> fst (proc ([], [])) v2
    | CoerceV (v1, CFun (s, t)) -> eval_app_val env v1 (coerce v2 s ~debug:debug) (CoercionV t) ~debug:debug
    | _ -> raise @@ Eval_bug (asprintf "app: application of non procedure value: %a" Pp.LS1.pp_value v1)

  let eval_program ?(debug=false) env p =
    match p with
    | Exp f ->
      let v = eval env f ~debug:debug in
      env, "-", v
    | LetDecl (x, xs, f) ->
      let v = eval env f ~debug:debug in
      let env = Environment.add x (xs, v) env in
      env, x, v
end

module KNorm = struct
  open Syntax.KNorm

  let rec subst_exp s = 
    let subst_type_k s = function
      | Ty u -> Ty (subst_type s u)
      | TyNu -> TyNu
    in function
    | Var _ | IConst _ | Nil as f -> f
    | Add _ | Sub _ | Mul _ | Div _ | Mod _ | Cons _ | Hd _ | Tl _ as f -> f
    | IfEqExp (x, y, f1, f2) -> IfEqExp (x, y, subst_exp s f1, subst_exp s f2)
    | IfLteExp (x, y, f1, f2) -> IfLteExp (x, y, subst_exp s f1, subst_exp s f2)
    | MatchExp (x, ms) -> MatchExp (x, List.map (fun (mf, f) -> subst_mf s mf, subst_exp s f) ms)
    | AppExp _ | CAppExp _ | CSeqExp _ as f -> f
    | AppTy (x, tvs, tas) -> AppTy (x, tvs, List.map (subst_type_k s) tas)
    (* | CastExp (r, x, u1, u2, p) -> CastExp (r, x, subst_type s u1, subst_type s u2, p) *)
    | LetExp (x, f1, f2) ->
      LetExp (x, subst_exp s f1, subst_exp s f2)
    | LetRecExp (x, tvs, arg, f1, f2) ->
      LetRecExp (x, tvs, arg, subst_exp s f1, subst_exp s f2)
    | CoercionExp c -> CoercionExp (subst_coercion s c)
    | AppExp_alt _ as f -> f
    | LetRecExp_alt (x, tvs, arg, (f1, f1'), f2) ->
      LetRecExp_alt (x, tvs, arg, (subst_exp s f1, subst_exp s f1'), subst_exp s f2)

  let rec eval_exp ?(debug=false) kenv f = 
    if debug then fprintf err_formatter "keval <-- %a\n" Pp.KNorm.pp_exp f;
    let eval_exp = eval_exp ~debug:debug in
    match f with
    | Var x -> 
      Environment.find x kenv
    | IConst i -> IntV i
    (* | UConst -> UnitV *)
    | Nil -> NilV
    | Add (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 + i2)
        | _ -> raise @@ Eval_bug "Add: unexpected type of argument"
      end
    | Sub (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 - i2)
        | _ -> raise @@ Eval_bug "Sub: unexpected type of argument"
      end
    | Mul (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 * i2)
        | _ -> raise @@ Eval_bug "Mul: unexpected type of argument"
      end
    | Div (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 / i2)
        | _ -> raise @@ Eval_bug "Div: unexpected type of argument"
      end
    | Mod (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> IntV (i1 mod i2)
        | _ -> raise @@ Eval_bug "Mod: unexpected type of argument"
      end
    | Cons (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      ConsV (v1, v2)
    | Hd x ->
      let v = Environment.find x kenv in
      begin match v with
      | ConsV (v1, _) -> v1
      | CoerceV (ConsV (v1, _), CList s) -> coerce ~debug:debug v1 s
      | _ -> raise @@ Eval_bug "hd: not list value"
      end
    | Tl x ->
      let v = Environment.find x kenv in
      begin match v with
      | ConsV (_, v2) -> v2
      | CoerceV (ConsV (_, v2), s) -> coerce ~debug:debug v2 s
      | _ -> raise @@ Eval_bug "hd: not list value"
      end
    | IfEqExp (x1, x2, f1, f2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> if i1 = i2 then eval_exp kenv f1 else eval_exp kenv f2
        | _ -> raise @@ Eval_bug "IfEqExp: not int value"
      end
    | IfLteExp (x1, x2, f1, f2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> if i1 <= i2 then eval_exp kenv f1 else eval_exp kenv f2
        | _ -> raise @@ Eval_bug "IfLteExp: not int value"
      end
    | MatchExp (x, ms) ->
      let v = Environment.find x kenv in
      eval_next ~debug:debug kenv v ms
    | AppExp (x1, (x2, x3)) -> 
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      let v3 = Environment.find x3 kenv in
      eval_app_val kenv v1 v2 v3 ~debug:debug
    | CAppExp (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v2 with
      | CoercionV c -> coerce ~debug:debug v1 c
      | _ -> raise @@ Eval_bug "capp: application of non coercion value"
      end
    | CSeqExp (x1, x2) -> 
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | CoercionV c1, CoercionV c2 -> CoercionV (compose c1 c2 ~debug:debug)
        | _ -> raise @@ Eval_bug "cseq: sequence of non coercion value"
      end
    | AppTy (x, tvs, tas) ->
      let v1 = Environment.find x kenv in
      let us = List.map nu_to_fresh tas in
      begin match v1 with
        | FunV proc -> FunV (fun _ -> proc (tvs, us))
        | FunV_alt proc -> FunV_alt (fun _ -> proc (tvs, us))
        | _ -> raise @@ Eval_bug "AppTy: not fun value"
      end
    | LetExp (x, f1, f2) -> 
      let v1 = eval_exp kenv f1 in
      eval_exp (Environment.add x v1 kenv) f2
    | LetRecExp (x, _, (y, k), f1, f2) -> 
      let v1 = 
        FunV (
          fun (tvs, us) -> fun (v1, v2) ->
          let f1 = subst_exp (Utils.List.zip tvs us) f1 in
          let rec f _ (v1, v2) =
            let kenv = Environment.add x (FunV f) kenv in
            let kenv = Environment.add y v1 kenv in
            let kenv = Environment.add k v2 kenv in
            eval_exp kenv f1
          in f ([], []) (v1, v2)
        )
      in eval_exp (Environment.add x v1 kenv) f2
    | CoercionExp c -> CoercionV c
    | AppExp_alt (x, y) -> 
      let v1 = Environment.find x kenv in
      let v2 = Environment.find y kenv in
      eval_app_val_alt kenv v1 v2 ~debug:debug
    | LetRecExp_alt (x, _, (y, k), (f1, f1'), f2) -> 
      let v1 = 
        FunV_alt (
          fun (xs, ys) -> 
          let f1 = subst_exp (Utils.List.zip xs ys) f1 in
          let f1' = subst_exp (Utils.List.zip xs ys) f1' in
          let rec f1_ v =
            let kenv = Environment.add x (FunV_alt (fun _ -> (f1_, f1'_))) kenv in
            let kenv = Environment.add y v kenv in
            eval_exp kenv f1
          and f1'_ (v, w) =
            let kenv = Environment.add x (FunV_alt (fun _ -> (f1_, f1'_))) kenv in
            let kenv = Environment.add y v kenv in
            let kenv = Environment.add k w kenv in
            eval_exp kenv f1'
          in (f1_, f1'_)
        )
      in eval_exp (Environment.add x v1 kenv) f2
  and coerce ?(debug=false) v c =
    let print_debug f = Utils.Format.make_print_debug debug f in
    print_debug "coerce <-- %a<%a>\n" Pp.KNorm.pp_value v Pp.pp_coercion c;
    let coerce = coerce ~debug:debug in
    match v with
    | CoerceV (v, c') -> coerce v (compose c' c ~debug:debug)
    | v -> match normalize_coercion c with
      | CId _ -> v
      | CFail (_, (r, p), _) -> raise @@ KBlame (r, p)
      | c when is_d c -> CoerceV (v, (*Typing.ITGL.normalize_coercion*) c)
      | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a" Pp.KNorm.pp_value v)
  and match_mf ?(debug=false) kenv v mf = match v, mf with
    (* | _, MatchVar (id, _) ->
      let kenv = Environment.add id v kenv in
      true, kenv *)
    | ConsV (v1, v2), MatchCons (mf1, mf2) ->
      let b1, kenv = match_mf ~debug:debug kenv v1 mf1 in
      let b2, kenv = match_mf ~debug:debug kenv v2 mf2 in
      b1&&b2, kenv 
    | NilV, MatchNil _ -> true, kenv
    | IntV i1, MatchILit i2 -> if i1 = i2 then (true, kenv) else (false, kenv)
    (* | IntV i, MatchBLit b -> if i = 1 && b then (true, kenv) else if i = 0 && not b then (false, kenv) else raise @@ Eval_bug "MatchBLit didn't match"
    | IntV 0, MatchULit -> true, kenv *)
    (* | arg, MatchAsc (mf, _) -> match_mf env arg mf *)
    | _, MatchWild _ -> true, kenv
    | CoerceV (ConsV (v1, v2), CList s), MatchCons _ -> 
      match_mf ~debug:debug kenv (ConsV (coerce ~debug:debug v1 s, coerce ~debug:debug v2 (CList s))) mf (* lazy *)
    | _, (MatchVar _ | MatchBLit _ | MatchULit) -> raise @@ Eval_bug "MatchVar, MatchBLit, MatchULit  does not appear in KNormal form"
    | _ -> false, kenv 
  and eval_next ?(debug=false) kenv v ms = match ms with
    | (mf, f) :: ms ->
      let b, kenv' = match_mf ~debug:debug kenv v mf in
      if b then eval_exp ~debug:debug kenv' f
      else eval_next ~debug:debug kenv v ms
    | [] -> raise @@ Eval_bug "Didn't match"
  and eval_app_val ?(debug=false) kenv v1 v2 v3 = match v1 with
    | FunV proc -> proc ([], []) (v2, v3)
    | FunV_alt proc -> snd (proc ([], [])) (v2, v3)
    | CoerceV (v1, CFun (s, t)) -> 
      begin match v3 with
        | CoercionV c -> 
          let k = CoercionV (compose t c ~debug:debug) in
          eval_app_val kenv v1 (coerce v2 s ~debug:debug) k
        | _ -> raise @@ Eval_bug "app: application of non coercion value"
      end
    | _ -> raise @@ Eval_bug "app: application of non procedure value"
  and eval_app_val_alt ?(debug=false) env v1 v2 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunV_alt proc -> fst (proc ([], [])) v2
    | CoerceV (v1, CFun (s, t)) -> eval_app_val env v1 (coerce v2 s ~debug:debug) (CoercionV t) ~debug:debug
    | _ -> raise @@ Eval_bug "app: application of non procedure value"

  let eval_program ?(debug=false) kenv = function
    | Exp f -> let v = eval_exp kenv f ~debug:debug in kenv, "-", v
    | LetDecl (x, f) ->
      let v = eval_exp kenv f ~debug:debug in
      let kenv = Environment.add x v kenv in
      kenv, x, v
    | LetRecDecl (x, _, (y, k), f') -> 
      let v = 
        FunV (
          fun (tvs, us) -> fun (v1, v2) ->
          let f' = subst_exp (Utils.List.zip tvs us) f' in
          let rec f _ (v1, v2) =
            let kenv = Environment.add x (FunV f) kenv in
            let kenv = Environment.add y v1 kenv in
            let kenv = Environment.add k v2 kenv in
            eval_exp kenv f'
          in f ([], []) (v1, v2)
        )
      in let kenv = Environment.add x v kenv in
      kenv, x, v
    | LetRecDecl_alt (x, _, (y, k), (f1, f1')) -> 
      let v = 
        FunV_alt (
          fun (xs, ys) -> 
          let f1 = subst_exp (Utils.List.zip xs ys) f1 in
          let f1' = subst_exp (Utils.List.zip xs ys) f1' in
          let rec f1_ v =
            let kenv = Environment.add x (FunV_alt (fun _ -> (f1_, f1'_))) kenv in
            let kenv = Environment.add y v kenv in
            eval_exp kenv f1
          and f1'_ (v, w) =
            let kenv = Environment.add x (FunV_alt (fun _ -> (f1_, f1'_))) kenv in
            let kenv = Environment.add y v kenv in
            let kenv = Environment.add k w kenv in
            eval_exp kenv f1'
          in (f1_, f1'_)
        )
      in let kenv = Environment.add x v kenv in
      kenv, x, v
end