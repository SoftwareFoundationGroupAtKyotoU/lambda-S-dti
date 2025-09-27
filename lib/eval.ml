open Format
open Syntax
open Utils.Error

exception Blame of range * Syntax.polarity

exception KBlame of Utils.Error.range * Syntax.polarity

exception Eval_bug of string

let subst_type = Typing.subst_type

let fresh_tyvar = Typing.fresh_tyvar

let type_of_tag = Typing.type_of_tag

let tag_of_ty = Typing.tag_of_ty

let nu_to_fresh = function
| Ty u -> u
| TyNu -> Typing.fresh_tyvar ()
  
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
    | LetExp (y, ys, f1, f2) ->
      (* Remove substitutions captured by let exp s *)
      let s = List.filter (fun (x, _) -> not @@ List.memq x ys) s in
      LetExp (y, ys, subst_exp s f1, subst_exp s f2)
    | CoercionExp c -> CoercionExp (subst_coercion s c)
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
    | _ -> raise @@ Eval_bug "app: application of non procedure value"

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
    | Var _ | IConst _ | UConst as f -> f
    | Add _ | Sub _ | Mul _ | Div _ | Mod _ as f -> f
    | IfEqExp (x, y, f1, f2) -> IfEqExp (x, y, subst_exp s f1, subst_exp s f2)
    | IfLteExp (x, y, f1, f2) -> IfLteExp (x, y, subst_exp s f1, subst_exp s f2)
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
    | UConst -> UnitV
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
      | CFail (_, (r, p), _) -> raise @@ Blame (r, p)
      | c when is_d c -> CoerceV (v, (*Typing.ITGL.normalize_coercion*) c)
      | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a" Pp.KNorm.pp_value v)
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