open Pp
open Syntax
open Format

exception Translation_bug of string

(* let type_of_tag = Typing.type_of_tag *)

let tag_of_ty = Typing.tag_of_ty

(* These functions (dom, cod, meet) only can be used for normalized types *)
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
  | _ ->
    raise @@ Translation_bug (asprintf "failed to match: meet(%a, %a)" pp_ty u1 pp_ty u2)

module ITGL = struct
  open Syntax.ITGL

  let closure_tyvars_let_decl1 e u1 env =
    TV.elements @@ TV.diff (TV.union (tv_exp e) (ftv_ty u1)) (ftv_tyenv env)

  let closure_tyvars2 w1 env u1 v1 =
    let ftvs = TV.big_union [ftv_tyenv env; ftv_ty u1; ftv_exp v1] in
    TV.elements @@ TV.diff (Syntax.LS.ftv_exp w1) ftvs
  
  let closure_tyvars_let_decl2 w1 env u1 v1 =
    let ftvs = TV.big_union [ftv_tyenv env; ftv_ty u1; tv_exp v1] in
    TV.elements @@ TV.diff (Syntax.LS.ftv_exp w1) ftvs

  (* Cast insertion translation *)
  let rec make_s_coercion (r, p) u1 u2 = match u1, u2 with
    | i1, i2 when is_base_type i1 && is_base_type i2 && i1 = i2 -> CId i1
    | TyVar (i1, {contents = None}) as t, TyVar (i2, {contents = None}) when i1 = i2 -> CId t
    | TyFun (u11, u12), TyFun (u21, u22) -> CFun (make_s_coercion (r, neg p) u21 u11, make_s_coercion (r, p) u12 u22) 
    | TyDyn, TyDyn -> CId TyDyn
    | g, TyDyn when is_ground g -> CSeq (CId g, CInj (tag_of_ty g))
    | TyFun _ as u, TyDyn -> CSeq (make_s_coercion (r, p) u (TyFun (TyDyn, TyDyn)), CInj Ar)
    | TyVar tv, TyDyn -> CTvInj tv
    | TyDyn, g when is_ground g -> CSeq (CProj (tag_of_ty g, (r, p)), CId g)
    | TyDyn, (TyFun _ as u) -> CSeq (CProj (Ar, (r, p)), make_s_coercion (r, p) (TyFun (TyDyn, TyDyn)) u)
    | TyDyn, TyVar tv -> CTvProj (tv, (r, p))
    | _ -> Pp.pp_ty err_formatter u1; Pp.pp_ty err_formatter u1; raise @@ Translation_bug "cannot exist such coercion"

  let coerce f r u1 u2 = 
    if u1 = u2 then f (* Omit identity cast for better performance *)
    else LS.CAppExp (f, make_s_coercion (r, Pos) u1 u2)

  let rec translate_exp env = function
    | Var (_, x, ys) ->
      begin try
        let TyScheme (xs, u) = Environment.find x env in
        let ftvs = ftv_ty u in
        let s = Utils.List.zip xs !ys in
        let ys = List.map (fun (x, u) -> if TV.mem x ftvs then Ty u else TyNu) s in
        let ys = ys @ Utils.List.repeat TyNu (List.length xs - List.length ys) in
        let u = Typing.subst_type (List.filter (fun (x, _) -> TV.mem x ftvs) s) u in
        LS.Var (x, ys), u
      with Not_found ->
        raise @@ Translation_bug "variable not found during cast-inserting translation"
      end
    | IConst (_, i) -> LS.IConst i, TyInt
    | BConst (_, b) -> LS.BConst b, TyBool
    | UConst _ -> LS.UConst, TyUnit
    | BinOp (_, op, e1, e2) ->
      let ui1, ui2, ui = Typing.type_of_binop op in
      let f1, u1 = translate_exp env e1 in
      let f2, u2 = translate_exp env e2 in
      let r1, r2 = range_of_exp e1, range_of_exp e2 in
      LS.BinOp (op, coerce f1 r1 u1 ui1, coerce f2 r2 u2 ui2), ui
    | AscExp (_, e, u1) ->
      let f, u = translate_exp env e in
      let r = range_of_exp e in
      if is_consistent u u1 then
        coerce f r u u1, u1
      else
        raise @@ Translation_bug "type ascription"
    | IfExp (_, e1, e2, e3) ->
      let f1, u1 = translate_exp env e1 in
      let f2, u2 = translate_exp env e2 in
      let f3, u3 = translate_exp env e3 in
      let r1, r2, r3 = range_of_exp e1, range_of_exp e2, range_of_exp e3 in
      let u = meet u2 u3 in
      LS.IfExp (coerce f1 r1 u1 TyBool, coerce f2 r2 u2 u, coerce f3 r3 u3 u), u
    | FunEExp (_, x, u1, e)
    | FunIExp (_, x, u1, e) ->
      let f, u2 = translate_exp (Environment.add x (tysc_of_ty u1) env) e in
      LS.FunExp (x, u1, f), TyFun (u1, u2)
    | FixEExp (_, x, y, u1, u2, e)
    | FixIExp (_, x, y, u1, u2, e) ->
      (* NOTE: Disallow to use x polymorphically in e *)
      let env = Environment.add x (tysc_of_ty (TyFun (u1, u2))) env in
      let env = Environment.add y (tysc_of_ty u1) env in
      let f, u2' = translate_exp env e in
      let r = range_of_exp e in
      LS.FixExp (x, y, u1, u2, coerce f r u2' u2), TyFun (u1, u2)
    | AppExp (_, e1, e2) ->
      let f1, u1 = translate_exp env e1 in
      let f2, u2 = translate_exp env e2 in
      let r1, r2 = range_of_exp e1, range_of_exp e2 in
      LS.AppExp (coerce f1 r1 u1 (TyFun (dom u1, cod u1)), coerce f2 r2 u2 (dom u1)), cod u1
    | LetExp (_, x, e1, e2) when Typing.ITGL.is_value env e1 ->
      let f1, u1 = translate_exp env e1 in
      let xs = Typing.ITGL.closure_tyvars1 u1 env e1 in
      let ys = closure_tyvars2 f1 env u1 e1 in
      let xys = xs @ ys in
      let us1 = TyScheme (xys, u1) in
      let f2, u2 = translate_exp (Environment.add x us1 env) e2 in
      LS.LetExp (x, xys, f1, f2), u2
    | LetExp (r, x, e1, e2) ->
      let _, u1 = translate_exp env e1 in
      let e = AppExp (r, FunIExp (r, x, u1, e2), e1) in
      translate_exp env e

  let translate env = function
    | Exp e ->
      let f, u = translate_exp env e in
      env, LS.Exp f, u
    | LetDecl (x, e) ->
      let f, u = translate_exp env e in
      let tvs = 
        if Typing.ITGL.is_value env e then
          let xs = closure_tyvars_let_decl1 e u env in
          let ys = closure_tyvars_let_decl2 f env u e in
          xs @ ys
        else 
          []
      in let env = Environment.add x (TyScheme (tvs, u)) env in
      env, LS.LetDecl (x, tvs, f), u
end

module LS = struct
  open Syntax.LS

  let fresh_CVar =
    let counter = ref 0 in
    let body () =
      let v = !counter in
      counter := v + 1;
      let id = "k"^string_of_int !counter in
      id, LS1.Var (id, [])
    in body

  let rec translate_exp env = function
    | Var (x, ys) -> LS1.Var (x, ys)
    | IConst i -> LS1.IConst i(*, TyInt*)
    | BConst b -> LS1.BConst b(*, TyBool*)
    | UConst -> LS1.UConst
    | FunExp (x, u, f) ->
      let env = Environment.add x (tysc_of_ty u) env in
      let id, k = fresh_CVar () in 
      LS1.FunExp ((x, u), id, translate_exp_k env k f)
    | FixExp (x, y, u1, u, f) -> 
      let env = Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env) in
      let id, k = fresh_CVar () in 
      LS1.FixExp ((x, y, u1, u), id, translate_exp_k env k f)
    | CAppExp (f, c) -> translate_exp_k env (LS1.CoercionExp c) f
    | AppExp (f1, f2) as f -> (*new*)
      let u = Typing.LS.type_of_program env (Exp f) in
      LS1.AppExp (translate_exp env f1, translate_exp env f2, (LS1.CoercionExp (CId u)))
    | BinOp (op, f1, f2) -> LS1.BinOp (op, translate_exp env f1, translate_exp env f2) (*new*)
    | IfExp (f1, f2, f3) -> LS1.IfExp (translate_exp env f1, translate_exp env f2, translate_exp env f3) (*new*)
    | LetExp (x, ys, f1, f2) -> (*new*)
      let u = Typing.LS.type_of_program env (Exp f1) in
      LS1.LetExp (x, ys, translate_exp env f1, translate_exp (Environment.add x (TyScheme (ys, u)) env) f2)
  and translate_exp_k env k = function
    | Var (x, ys) -> LS1.CAppExp (LS1.Var (x, ys), k)
    | IConst i -> LS1.CAppExp (LS1.IConst i, k)
    | BConst b -> LS1.CAppExp (LS1.BConst b, k)
    | UConst -> LS1.CAppExp (LS1.UConst, k)
    | FunExp (x, u, f) -> 
      let env = Environment.add x (tysc_of_ty u) env in
      let id, k' = fresh_CVar () in 
      LS1.CAppExp (LS1.FunExp ((x, u), id, translate_exp_k env k' f), k)
    | FixExp (x, y, u1, u, f) -> 
      let env = Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env) in
      let id, k' = fresh_CVar () in 
      LS1.CAppExp (LS1.FixExp ((x, y, u1, u), id, translate_exp_k env k' f), k)
    | BinOp (op, f1, f2) -> LS1.CAppExp (LS1.BinOp (op, translate_exp env f1, translate_exp env f2), k)
    | IfExp (f1, f2, f3) -> LS1.IfExp (translate_exp env f1, translate_exp_k env k f2, translate_exp_k env k f3)
    | AppExp (f1, f2) -> LS1.AppExp (translate_exp env f1, translate_exp env f2, k)
    | CAppExp (f, c) -> let id, k' = fresh_CVar () in LS1.LetExp (id, [], LS1.CSeqExp (LS1.CoercionExp c, k), translate_exp_k env k' f)
    | LetExp (x, ys, f1, f2) -> 
      let u = Typing.LS.type_of_program env (Exp f1) in
      LS1.LetExp (x, ys, translate_exp env f1, translate_exp_k (Environment.add x (TyScheme (ys, u)) env) k f2)

  let translate env = function
    | Exp f -> LS1.Exp (translate_exp env f)
    | LetDecl (x, ys, f) -> LS1.LetDecl (x, ys, translate_exp env f)

  let rec translate_exp_alt env = function
    | Var (x, ys) -> LS1.Var (x, ys)
    | IConst i -> LS1.IConst i(*, TyInt*)
    | BConst b -> LS1.BConst b(*, TyBool*)
    | UConst -> LS1.UConst
    | FunExp (x, u, f) ->
      let env = Environment.add x (tysc_of_ty u) env in
      let id, k = fresh_CVar () in 
      LS1.FunExp_alt ((x, u), id, (translate_exp_alt env f, translate_exp_k_alt env k f))
    | FixExp (x, y, u1, u, f) -> 
      let env = Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env) in
      let id, k = fresh_CVar () in 
      LS1.FixExp_alt ((x, y, u1, u), id, (translate_exp_alt env f, translate_exp_k_alt env k f))
    | CAppExp (f, c) -> translate_exp_k_alt env (LS1.CoercionExp c) f
    | AppExp (f1, f2) -> (*new*)
      LS1.AppExp_alt (translate_exp_alt env f1, translate_exp_alt env f2)
    | BinOp (op, f1, f2) -> LS1.BinOp (op, translate_exp_alt env f1, translate_exp_alt env f2) (*new*)
    | IfExp (f1, f2, f3) -> LS1.IfExp (translate_exp_alt env f1, translate_exp_alt env f2, translate_exp_alt env f3) (*new*)
    | LetExp (x, ys, f1, f2) -> (*new*)
      let u = Typing.LS.type_of_program env (Exp f1) in
      LS1.LetExp (x, ys, translate_exp_alt env f1, translate_exp_alt (Environment.add x (TyScheme (ys, u)) env) f2)
  and translate_exp_k_alt env k = function
    | Var (x, ys) -> LS1.CAppExp (LS1.Var (x, ys), k)
    | IConst i -> LS1.CAppExp (LS1.IConst i, k)
    | BConst b -> LS1.CAppExp (LS1.BConst b, k)
    | UConst -> LS1.CAppExp (LS1.UConst, k)
    | FunExp (x, u, f) -> 
      let env = Environment.add x (tysc_of_ty u) env in
      let id, k' = fresh_CVar () in 
      LS1.CAppExp (LS1.FunExp_alt ((x, u), id, (translate_exp_alt env f, translate_exp_k_alt env k' f)), k)
    | FixExp (x, y, u1, u, f) -> 
      let env = Environment.add y (tysc_of_ty u1) (Environment.add x (tysc_of_ty (TyFun (u1, u))) env) in
      let id, k' = fresh_CVar () in 
      LS1.CAppExp (LS1.FixExp_alt ((x, y, u1, u), id, (translate_exp_alt env f, translate_exp_k_alt env k' f)), k)
    | BinOp (op, f1, f2) -> LS1.CAppExp (LS1.BinOp (op, translate_exp_alt env f1, translate_exp_alt env f2), k)
    | IfExp (f1, f2, f3) -> LS1.IfExp (translate_exp_alt env f1, translate_exp_k_alt env k f2, translate_exp_k_alt env k f3)
    | AppExp (f1, f2) -> LS1.AppExp (translate_exp_alt env f1, translate_exp_alt env f2, k)
    | CAppExp (f, c) -> let id, k' = fresh_CVar () in LS1.LetExp (id, [], LS1.CSeqExp (LS1.CoercionExp c, k), translate_exp_k_alt env k' f)
    | LetExp (x, ys, f1, f2) -> 
      let u = Typing.LS.type_of_program env (Exp f1) in
      LS1.LetExp (x, ys, translate_exp_alt env f1, translate_exp_k_alt (Environment.add x (TyScheme (ys, u)) env) k f2)

  let translate_alt env = function
    | Exp f -> LS1.Exp (translate_exp_alt env f)
    | LetDecl (x, ys, f) -> LS1.LetDecl (x, ys, translate_exp_alt env f)
end