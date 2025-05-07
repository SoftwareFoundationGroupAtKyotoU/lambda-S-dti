open Format
open Syntax
open Utils.Error

exception Blame of range * Syntax.polarity

exception KBlame of Utils.Error.range * Syntax.polarity

exception Eval_bug of string

let subst_type = Typing.subst_type

let nu_to_fresh = function
| Ty u -> u
| TyNu -> Typing.fresh_tyvar ()

let rec subst_coercion s = function
| CInj u -> CInj (subst_type s u)
| CProj (u, rp) -> CProj (subst_type s u, rp)
| CFun (c1, c2) -> CFun (subst_coercion s c1, subst_coercion s c2)
| CId u -> CId (subst_type s u)
| CSeq (c1, c2) -> CSeq (subst_coercion s c1, subst_coercion s c2)
| CFail (u1, rp, u2) -> CFail (subst_type s u1, rp, subst_type s u2)

let rec compose ?(debug=false) c1 c2 = 
  if debug then fprintf err_formatter "compose <-- %a；%a\n" Pp.pp_coercion c1 Pp.pp_coercion c2;
  let compose = compose ~debug:debug in
  match c1, c2 with
  | CId TyDyn, c2 -> c2
  | CSeq (CProj (g, p), c1), c2 -> CSeq (CProj (g, p), compose c1 c2)
  | CSeq (_, CInj _) as c1, CId TyDyn -> c1
  | CFail _ as c1, _ -> c1
  | CSeq (c1, CInj g), CSeq (CProj (g', p), c2) ->
    begin match g, g' with
    | g, g' when g = g' -> compose c1 c2
    | TyFun (TyDyn, TyDyn), (TyVar (_, ({contents = None} as x)) as u') ->
      let u1 = Typing.fresh_tyvar () in
      let u2 = Typing.fresh_tyvar () in
      let u = TyFun (u1, u2) in
      if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n"
        Pp.pp_ty u'
        Pp.pp_ty u;
      x := Some g;
      (* compose ( *) 
      compose c1 (CFun (CSeq (CId u1, CInj u1), CSeq (CProj (u2, p), CId u2)))
      (* ) c2*)
    | TyVar (_, ({contents = None} as x)) as u', TyFun (TyDyn, TyDyn) ->
      let u1 = Typing.fresh_tyvar () in
      let u2 = Typing.fresh_tyvar () in
      let u = TyFun (u1, u2) in
      if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n"
        Pp.pp_ty u'
        Pp.pp_ty u;
      x := Some g';
      (* compose c1 ( *) 
      compose (CFun (CSeq (CId u1, CInj u1), CSeq (CProj (u2, p), CId u2))) c2
      (* )*)
    | TyVar (_, ({contents = None} as x)) as u', g | g, (TyVar (_, ({contents = None} as x)) as u') ->
      if debug then fprintf err_formatter "DTI: %a is instantiated to %a\n"
        Pp.pp_ty u'
        Pp.pp_ty g;
      x := Some g;
      compose c1 c2
    | TyVar (_, {contents = Some u}), g' ->
      compose (CSeq (c1, CInj u)) (CSeq (CProj (g', p), c2))
    | g, TyVar (_, {contents = Some u}) ->
      compose (CSeq (c1, CInj g)) (CSeq (CProj (u, p), c2))
    | _ ->  CFail (g, p, g')
    end
  | _, (CFail _ as c2) (*when is_g c1*) -> c2
  | c1, CSeq (c2, CInj g) (*when is_g c1*) -> CSeq (compose c1 c2, CInj g)
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
      let rec eval_app_val env v1 v2 v3 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
        | FunV proc -> proc ([], []) (v2, v3)
        | CoerceV (v1, CFun (s, t)) -> 
          begin match v3 with
            | CoercionV c -> 
              let k = CoercionV (compose t c ~debug:debug) in
              eval_app_val env v1 (coerce v2 s ~debug:debug) k
            | _ -> raise @@ Eval_bug "app: application of non coercion value"
          end
        | _ -> raise @@ Eval_bug "app: application of non procedure value"
      in eval_app_val env v1 v2 v3
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
  and coerce ?(debug=false) v c =
    let print_debug f = Utils.Format.make_print_debug debug f in
    print_debug "coerce <-- %a<%a>\n" Pp.LS1.pp_value v Pp.pp_coercion c;
    let coerce = coerce ~debug:debug in
    match v with
    | CoerceV (v, c') -> coerce v (compose c' c ~debug:debug)
    | v -> match c with
      | CId _ -> v
      | CFail (_, (r, p), _) -> raise @@ Blame (r, p)
      | c when is_d c -> CoerceV (v, Typing.ITGL.normalize_coercion c)
      | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a" Pp.LS1.pp_value v)

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
      let rec eval_app_val kenv v1 v2 v3 = match v1 with
        | FunV proc -> proc ([], []) (v2, v3)
        | CoerceV (v1, CFun (s, t)) -> 
          begin match v3 with
            | CoercionV c -> 
              let k = CoercionV (compose t c ~debug:debug) in
              eval_app_val kenv v1 (coerce v2 s ~debug:debug) k
            | _ -> raise @@ Eval_bug "app: application of non coercion value"
          end
        | _ -> raise @@ Eval_bug "app: application of non procedure value"
      in eval_app_val kenv v1 v2 v3
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
        | _ -> raise @@ Eval_bug "AppTy: not fun value"
      end
    (* | CastExp (r, x, u1, u2, p) ->
      let v = Environment.find x kenv in
      cast ~debug:debug v u1 u2 r p *)
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
  and coerce ?(debug=false) v c =
    let print_debug f = Utils.Format.make_print_debug debug f in
    print_debug "coerce <-- %a<%a>\n" Pp.KNorm.pp_value v Pp.pp_coercion c;
    let coerce = coerce ~debug:debug in
    match v with
    | CoerceV (v, c') -> coerce v (compose c' c ~debug:debug)
    | v -> match c with
      | CId _ -> v
      | CFail (_, (r, p), _) -> raise @@ Blame (r, p)
      | c when is_d c -> CoerceV (v, Typing.ITGL.normalize_coercion c)
      | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a" Pp.KNorm.pp_value v)

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
end

(* (fun ((f: ?), k6) -> (f<(? -> ?)?p;id{? -> ?}>) (2<id{int};int!>, k6)) 
((fun ((x: 'x2), k5) -> x<k5>) 
  ((fun ((y: ?), k4) -> y<k4>) 
    ((fun ((z: int), k3) -> z + 1<k3>)<(int?p;id{int})->(id{int};int!);(? -> ?)!>
    , 'x2?p;id{'x2})
  , id{'x2};'x2!)
, id{?})

eval <-- (fun ((f: ?), k4) -> (f<(? -> ?)?p;id{? -> ?}>) (2<id{int};int!>, k4)) ((fun ((x: 'x1), k3) -> x<k3>) ((fun ((y: ?), k2) -> y<k2>) ((fun ((z: int), k1) -> z + 1<k1>)<(int?p;id{int})->(id{int};int!);(? -> ?)!>, 'x1?p;id{'x1}), id{'x1};'x1!), id{?})
eval <-- fun ((f: ?), k4) -> (f<(? -> ?)?p;id{? -> ?}>) (2<id{int};int!>, k4)
eval <-- (fun ((x: 'x1), k3) -> x<k3>) ((fun ((y: ?), k2) -> y<k2>) ((fun ((z: int), k1) -> z + 1<k1>)<(int?p;id{int})->(id{int};int!);(? -> ?)!>, 'x1?p;id{'x1}), id{'x1};'x1!)
eval <-- fun ((x: 'x1), k3) -> x<k3>
eval <-- (fun ((y: ?), k2) -> y<k2>) ((fun ((z: int), k1) -> z + 1<k1>)<(int?p;id{int})->(id{int};int!);(? -> ?)!>, 'x1?p;id{'x1})
eval <-- fun ((y: ?), k2) -> y<k2>

eval <-- (fun ((z: int), k1) -> z + 1<k1>)<(int?p;id{int})->(id{int};int!);(? -> ?)!>
eval <-- fun ((z: int), k1) -> z + 1<k1>
eval <-- (int?p;id{int})->(id{int};int!);(? -> ?)!
coerce <-- <fun><(int?p;id{int})->(id{int};int!);(? -> ?)!>

eval <-- 'x1?p;id{'x1}

eval <-- y<k2>
eval <-- y
eval <-- k2
coerce <-- <fun><<(int?p;id{int})->(id{int};int!);(? -> ?)!>><'x1?p;id{'x1}>
compose <-- (int?p;id{int})->(id{int};int!);(? -> ?)!；'x1?p;id{'x1}
DTI: 'x1 is instantiated to 'x3 -> 'x4
compose <-- (int?p;id{int})->(id{int};int!)；(id{'x3};'x3!)->('x4?p;id{'x4})
compose <-- id{'x3};'x3!；int?p;id{int}
DTI: 'x3 is instantiated to int
compose <-- id{int}；id{int}
compose <-- id{int};int!；'x4?p;id{'x4}
DTI: 'x4 is instantiated to int
compose <-- id{int}；id{int}
coerce <-- <fun><id{int -> int}>

eval <-- id{? -> ?};? -> ?!

eval <-- x<k3>
eval <-- x
eval <-- k3
coerce <-- <fun><id{? -> ?};? -> ?!>
eval <-- id{?}
eval <-- (f<(? -> ?)?p;id{? -> ?}>) (2<id{int};int!>, k4)
eval <-- f<(? -> ?)?p;id{? -> ?}>
eval <-- f
eval <-- (? -> ?)?p;id{? -> ?}
coerce <-- <fun><<id{? -> ?};(? -> ?)!>><(? -> ?)?p;id{? -> ?}>
compose <-- id{? -> ?};(? -> ?)!；(? -> ?)?p;id{? -> ?}
compose <-- id{? -> ?}；id{? -> ?}
coerce <-- <fun><id{? -> ?}>
eval <-- 2<id{int};int!>
eval <-- 2
eval <-- id{int};int!
coerce <-- 2<id{int};int!>
eval <-- k4
eval <-- z + 1<k1>
eval <-- z + 1
eval <-- z
eval <-- 1 *)