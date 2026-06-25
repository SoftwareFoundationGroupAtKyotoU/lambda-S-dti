open Format
open Syntax
open Type_utils
open Coercion
open Normalize

exception Eval_bug of string

let nu_to_fresh = function
| Ty u -> u
| TyNu -> fresh_tyvar ()

module CC = struct
  open Syntax.CC
  open Subst.CC

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

  let rec eval ~(config: Config.t) (env: value Environment.t) f =
    let debug = config.debug in
    let monotonic = config.monotonic in
    if debug then fprintf err_formatter "eval <-- %a@." Pp.CC.pp_exp f;
    match f with
    | Var (x, us) ->
      let v = Environment.find x env in
      let us = List.map nu_to_fresh us in
      begin match v with
        | FunBV proc -> FunBV (fun _ -> proc us)
        | FunSV proc -> FunSV (fun _ -> proc us)
        | FunDualV proc -> FunDualV (fun _ -> proc us)
        | FunTyV proc -> proc us
        | _ -> v
      end
    | IConst i -> IntV i
    | BConst b -> BoolV b
    | UConst -> UnitV
    | BinOp (op, f1, f2) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      eval_binop op v1 v2
    | FunExp (tvs, fd) ->
      begin match fd with
      | FunB ((x, _), f') ->
        FunBV (
          fun ys -> fun v ->
            eval ~config (Environment.add x v env) @@ subst_exp ~monotonic (Utils.List.zip tvs ys) f'
        )
      | FunS ((x, _), (k, _), f') ->
        FunSV (
          fun ys -> fun (v, w) ->
            eval ~config (Environment.add x v (Environment.add k w env)) @@ subst_exp ~monotonic (Utils.List.zip tvs ys) f'
        )
      | FunDual ((x, _), (k, _), (f', f'')) ->
        FunDualV (
          fun ys ->
            (fun v -> eval ~config (Environment.add x v env) @@ subst_exp ~monotonic (Utils.List.zip tvs ys) f'),
            (fun (v, w) -> eval ~config (Environment.add x v (Environment.add k w env)) @@ subst_exp ~monotonic (Utils.List.zip tvs ys) f'')
        )
      | FunTy f' ->
        FunTyV (
          fun ys -> eval ~config env @@ subst_exp ~monotonic (Utils.List.zip tvs ys) f'
        )
      end
    | FixExp (tvs, fixd) ->
      begin match fixd with
      | FixB (x, (y, _), _, f') ->
        FunBV (
          fun ys ->
            let f' = subst_exp ~monotonic (Utils.List.zip tvs ys) f' in
            let rec f _ v =
              let env = Environment.add x (FunBV f) env in
              let env = Environment.add y v env in
              eval ~config env f'
            in f []
        )
      | FixS (x, (y, _), _, (k, _), f') ->
        FunSV (
          fun ys ->
            let f' = subst_exp ~monotonic (Utils.List.zip tvs ys) f' in
            let rec f _ (v, w) =
              let env = Environment.add x (FunSV f) env in
              let env = Environment.add y v env in
              let env = Environment.add k w env in
              eval ~config env f'
            in f []
        )
      | FixDual (x, (y, _), _, (k, _), (f', f'')) ->
        FunDualV (
          fun ys ->
            let f' = subst_exp ~monotonic (Utils.List.zip tvs ys) f' in
            let f'' = subst_exp ~monotonic (Utils.List.zip tvs ys) f'' in
            let rec f1_ v =
              let env = Environment.add x (FunDualV (fun _ -> (f1_, f2_))) env in
              let env = Environment.add y v env in
              eval ~config env f'
            and f2_ (v, w) =
              let env = Environment.add x (FunDualV (fun _ -> (f1_, f2_))) env in
              let env = Environment.add y v env in
              let env = Environment.add k w env in
              eval ~config env f''
            in (f1_, f2_)
        )
      end
    | AppMExp (f1, f2) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      eval_app_valM ~config env v1 v2
    | AppDExp (f1, (f2, f3)) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      let v3 = eval ~config env f3 in
      eval_app_valD ~config env v1 v2 v3
    | IfExp (f1, f2, f3) ->
      let v1 = eval ~config env f1 in
      begin match v1 with
        | BoolV true -> eval ~config env f2
        | BoolV false -> eval ~config env f3
        | _ -> raise @@ Eval_bug "if: non boolean value"
      end
    | LetExp (x, f1, f2) ->
      let v1 = eval ~config env f1 in
      eval ~config (Environment.add x v1 env) f2
    | MatchExp (f, ms) ->
      let v = eval ~config env f in
      eval_next ~config env v ms
    | NilExp _ -> NilV
    | ConsExp (f1, f2) ->
      let v2 = eval ~config env f2 in
      let v1 = eval ~config env f1 in
      ConsV (v1, v2)
    | TupleExp fs -> TupleV (List.map (fun f -> eval ~config env f) fs)
    | RefExp (f, u) ->
      let v = eval ~config env f in
      RefV (ref (v, u))
    | DerefExp (f, ou) ->
      let v = eval ~config env f in
      if monotonic then
        match v, ou with
        | RefV { contents = (v, _) }, None -> v
        | RefV { contents = (v, u) }, Some u' ->
          let s = make_s_coercion ~monotonic (normalize_type u) (Utils.Error.dummy_range, Pos) (normalize_type u') in (* TODO *)
          let v, psi = coerce ~config v s [] in
          consume ~config psi;
          v
        | _ -> raise @@ Eval_bug "eval: not refV deref"
      else
        begin match v with
        | RefV { contents = (v, _) } -> v
        | _ -> raise @@ Eval_bug "eval: not refV deref"
        end
    | SubstExp (f1, f2, ou) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      if monotonic then
        match v1, ou with
        | RefV ({ contents = (_, u) } as rv), None -> rv := v2, u; UnitV
        | RefV ({ contents = (_, u) } as rv), Some u' ->
          let s = make_s_coercion ~monotonic (normalize_type u') (Utils.Error.dummy_range, Pos) (normalize_type u) in (* TODO *)
          let v, psi = coerce ~config v2 s [] in
          rv := v, u;
          consume ~config psi;
          UnitV
        | _ -> raise @@ Eval_bug "eval: not refV subst"
      else begin match v1 with
      | RefV ({ contents = _, u } as rv) -> rv := (v2, u); UnitV
      | _ -> raise @@ Eval_bug "eval: not refV subst"
      end
    | CastExp (f, u1, u2, r_p) ->
      let v = eval ~config env f in
      cast ~config v u1 u2 r_p
    | CAppExp (f1, f2) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      begin match v2 with
        | CoercionV c -> 
          let v, psi = coerce ~config v1 c [] in
          consume ~config psi;
          v
        | _ -> raise @@ Eval_bug "capp: application of non coercion value"
      end
    | CSeqExp (f1, f2) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      begin match v1, v2 with
        | CoercionV c1, CoercionV c2 -> CoercionV (compose ~config c1 c2)
        | _ -> raise @@ Eval_bug "cseq: sequence of non coercion value"
      end
    | CoercionExp c -> CoercionV c
  and match_mf ~config env v mf = match v, mf with
    | _, MatchVar (id, _) ->
      let env = Environment.add id v env in
      true, env
    | ConsV (v1, v2), MatchCons (mf1, mf2) ->
      let b1, env = match_mf ~config env v1 mf1 in
      let b2, env = match_mf ~config env v2 mf2 in
      b1&&b2, env
    | NilV, MatchNil _ -> true, env
    | IntV i1, MatchILit i2 -> if i1 = i2 then (true, env) else (false, env)
    | BoolV b1, MatchBLit b2 -> if b1 = b2 then (true, env) else (false, env)
    | UnitV, MatchULit -> true, env
    | TupleV vs, MatchTuple mfs ->
      let rec iter env vs mfs b = match vs, mfs with
      | v :: vs, mf :: mfs ->
        let b', env = match_mf ~config env v mf in
        iter env vs mfs (b && b')
      | _ :: _, [] | [], _ :: _ -> false, env
      | [], [] -> b, env
      in
      iter env vs mfs true
    (* | arg, MatchAsc (mf, _) -> match_mf env arg mf *)
    | _, MatchWild _ -> true, env
    | CoerceV (ConsV (v1, v2), CList s), MatchCons _ ->
      let v1, psi = coerce ~config v1 s [] in
      let v2, psi = coerce ~config v2 (CList s) psi in
      consume ~config psi;
      match_mf ~config env (ConsV (v1, v2)) mf
    | CoerceV (TupleV vs, CTuple ss), MatchTuple _ ->
      let rec tp_c vs ss psi res = match vs, ss with
        | v :: vs, s :: ss ->
          let v, psi = coerce ~config v s psi in
          tp_c vs ss psi (v :: res)
        | _ -> TupleV (List.rev res), psi
      in
      let v, psi = tp_c vs ss [] [] in
      consume ~config psi;
      match_mf ~config env v mf
    | _ -> false, env
  and eval_next ~config env v ms = match ms with
    | (mf, f) :: ms ->
      let b, env' = match_mf ~config env v mf in
      if b then eval ~config env' f
      else eval_next ~config env v ms
    | [] -> raise @@ Eval_bug "Didn't match"
  and cast ~config v u1 u2 (r, p) =
    let print_debug f = Utils.Format.make_print_debug config.debug f in
    print_debug "cast <-- %a: %a => %a@." Pp.CC.pp_value v Pp.pp_ty u1 Pp.pp_ty u2;
    match u1, u2 with
    (* When type variables are instantiated *)
    | TyVar (_, { contents = Some u1 }), u2
    | u1, TyVar (_, { contents = Some u2 }) ->
      cast ~config v u1 u2 (r, p)
    (* IdBase *)
    | TyBool, TyBool
    | TyInt, TyInt
    | TyUnit, TyUnit -> v
    (* IdStar *)
    | TyDyn, TyDyn -> v
    (* Succeed / Fail *)
    | TyDyn, (TyBool | TyInt | TyUnit | TyFun (TyDyn, TyDyn) | TyList TyDyn | TyRef TyDyn as u2) ->
      begin match v, u2 with
      | Tagged (B, v), TyBool -> v
      | Tagged (I, v), TyInt -> v
      | Tagged (U, v), TyUnit -> v
      | Tagged (Ar, v), TyFun (TyDyn, TyDyn) -> v
      | Tagged (Li, v), TyList TyDyn -> v
      | Tagged (Rf, v), TyRef TyDyn -> v
      | Tagged _, _ -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_bug "untagged value"
      end
    | TyDyn, TyTuple us when List.fold_left (fun b u -> u = TyDyn && b) true us ->
      begin match v with
      | Tagged (Tp n, v) when n = List.length us -> v
      | Tagged _ -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_bug "untagged value"
      end
    (* AppCast *)
    | TyFun (u11, u12), TyFun (u21, u22) -> 
      if u11 = u21 && u12 = u22 then v 
      else begin match v with
      | FunBV proc ->
        FunBV (
          fun ys x ->
            let arg = cast ~config x u21 u11 (r, neg p) in
            let res = proc ys arg in
            cast ~config res u12 u22 (r, p)
        )
      | _ -> raise @@ Eval_bug "non procedural value"
      end
    | TyList u1, TyList u2 -> 
      if u1 = u2 then v 
      else begin match v with
      | NilV -> NilV
      | ConsV (h, t) -> ConsV (cast ~config h u1 u2 (r, p), cast ~config t (TyList u1) (TyList u2) (r, p))
      | _ -> raise @@ Eval_bug "non list value"
      end
    | TyTuple us1, TyTuple us2 ->
      if us1 = us2 then v
      else begin match v with
      | TupleV vs ->
        let rec cast_list vs us1 us2 res = match vs, us1, us2 with
        | v :: vs, u1 :: us1, u2 :: us2 -> cast_list vs us1 us2 ((cast ~config v u1 u2 (r, p)) :: res)
        | [], [], [] -> TupleV (List.rev res)
        | _ -> raise @@ Eval_bug "tuple length is wrong"
        in 
        cast_list vs us1 us2 []
      | _ -> raise @@ Eval_bug "non tuple value"
      end
    | TyRef _, TyRef _ -> raise @@ Eval_bug "ref cast yet"
    (* Tagged *)
    | TyBool, TyDyn -> Tagged (B, v)
    | TyInt, TyDyn -> Tagged (I, v)
    | TyUnit, TyDyn -> Tagged (U, v)
    | TyFun (TyDyn, TyDyn), TyDyn -> Tagged (Ar, v)
    | TyList TyDyn, TyDyn -> Tagged (Li, v)
    | TyTuple us, TyDyn when List.fold_left (fun b u -> u = TyDyn && b) true us -> Tagged (Tp (List.length us), v)
    | TyRef TyDyn, TyDyn -> Tagged (Rf, v)
    (* Ground *)
    | TyFun _, TyDyn ->
      let dfun = TyFun (TyDyn, TyDyn) in
      let v = cast ~config v u1 dfun (r, p) in
      cast ~config v dfun TyDyn (r, p)
    | TyList _, TyDyn ->
      let dlist = TyList TyDyn in
      let v = cast ~config v u1 dlist (r, p) in
      cast ~config v dlist TyDyn (r, p)
    | TyTuple us, TyDyn ->
      let dtuple = TyTuple (List.map (fun _ -> TyDyn) us) in
      let v = cast ~config v u1 dtuple (r, p) in
      cast ~config v dtuple TyDyn (r, p)
    | TyRef _, TyDyn ->
      let dref = TyRef TyDyn in
      let v = cast ~config v u1 dref (r, p) in
      cast ~config v dref u2 (r, p)
    (* Expand *)
    | TyDyn, TyFun _ ->
      let dfun = TyFun (TyDyn, TyDyn) in
      let v = cast ~config v TyDyn dfun (r, p) in
      cast ~config v dfun u2 (r, p)
    | TyDyn, TyList _ ->
      let dlist = TyList TyDyn in
      let v = cast ~config v TyDyn dlist (r, p) in
      cast ~config v dlist u2 (r, p)
    | TyDyn, TyTuple us ->
      let dtuple = TyTuple (List.map (fun _ -> TyDyn) us) in
      let v = cast ~config v TyDyn dtuple (r, p) in
      cast ~config v dtuple u2 (r, p)
    | TyDyn, TyRef _ ->
      let dref = TyRef TyDyn in
      let v = cast ~config v TyDyn dref (r, p) in
      cast ~config v dref u2 (r, p)
    (* InstBase / InstArrow *)
    | TyDyn, (TyVar (_, ({ contents = None } as x)) as x') -> begin
        match v with
        | Tagged (B | I | U as t, v) ->
          let u = type_of_tag t in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          v
        | Tagged (Ar, v) ->
          let u = TyFun (fresh_tyvar (), fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyFun (TyDyn, TyDyn)) u (r, p)
        | Tagged (Li, v) ->
          let u = TyList (fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyList TyDyn) u (r, p)
        | Tagged (Tp n, v) ->
          let u = TyTuple (List.init n (fun _ -> fresh_tyvar ())) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyTuple (List.init n (fun _ -> TyDyn))) u (r, p)
        | Tagged (Rf, v) ->
          let u = TyRef (fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyRef TyDyn) u (r, p)
        | _ -> raise @@ Eval_bug "cannot instantiate"
      end
    | _ -> raise @@ Eval_bug (asprintf "cannot cast value: %a" Pp.CC.pp_value v)
  and coerce ~config v c (psi: ((value * ty) ref * ty) list) =
    let print_debug f = Utils.Format.make_print_debug config.debug f in
    print_debug "coer <-- %a<%a>@." Pp.CC.pp_value v Pp.pp_coercion c;
    let eager = config.eager in
    let monotonic = config.monotonic in
    match v, normalize_coercion ~monotonic c with
    | CoerceV (v, c'), c -> coerce ~config v (compose ~config c' c) psi
    | v, CId _ -> v, psi
    | _, CFail (_, (r, p), _) -> raise @@ Blame (r, p)
    | NilV, CList _ when eager -> NilV, psi
    | ConsV (v1, v2), CList s when eager ->
      let v2, psi = coerce ~config v2 (CList s) psi in
      let v1, psi = coerce ~config v1 s psi in
      ConsV (v1, v2), psi
    | TupleV vs, CTuple ss when eager ->
      let rec tp_c vs ss psi res = match vs, ss with
      | v :: vs, s :: ss ->
        let v, psi = coerce ~config v s psi in
        tp_c vs ss psi (v :: res)
      | _ -> TupleV (List.rev res), psi
      in
      tp_c vs ss psi []
    | RefV rv, CMRef (_, u) when monotonic -> RefV rv, psi @ [rv, u]
    | v, c when is_d c -> CoerceV (v, c), psi
    | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a <%a>" Pp.CC.pp_value v Pp.pp_coercion c)
  and consume ~config = function
    | ({ contents = v, u' } as rv, u) :: psi ->
      let print_debug f = Utils.Format.make_print_debug config.debug f in
      print_debug "cons <-- (%a, %a), %a@." Pp.CC.pp_value v Pp.pp_ty u' Pp.pp_ty u;
      let u'' = try Typing.ITGL.type_of_meet u' u with Typing.Type_error _ -> raise @@ Blame (Utils.Error.dummy_range, Pos) in (* TODO *)
      if u'' = u' then
        consume ~config psi
      else begin
        let s = make_s_coercion ~monotonic:config.monotonic (normalize_type u') (Utils.Error.dummy_range, Pos) (normalize_type u'') in (* TODO *)
        let v, psi = coerce ~config v s psi in
        rv := v, u'';
        consume ~config psi
      end
    | [] -> ()
  and eval_app_valD ~config env v1 v2 v3 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunSV proc -> proc [] (v2, v3)
    | FunDualV proc ->
      begin match v3 with
      | CoercionV (CId _) -> fst (proc []) v2
      | _ -> snd (proc []) (v2, v3)
      end
    | CoerceV (v1, CFun (s, t)) ->
      begin match v3 with
        | CoercionV c ->
          let k = CoercionV (compose ~config t c) in
          let v2, psi = coerce ~config v2 s [] in
          consume ~config psi;
          eval_app_valD ~config env v1 v2 k
        | _ -> raise @@ Eval_bug "app: application of non coercion value"
      end
    | _ -> raise @@ Eval_bug (asprintf "app_valD: application of non procedure value: %a" Pp.CC.pp_value v1)
  and eval_app_valM ~config env v1 v2 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunBV proc -> proc [] v2
    | FunDualV proc -> fst (proc []) v2
    | CoerceV (v1, CFun (s, t)) -> 
      let v2, psi = coerce ~config v2 s [] in
      consume ~config psi;
      eval_app_valD ~config env v1 v2 (CoercionV t)
    | _ -> raise @@ Eval_bug (asprintf "app_valM: application of non procedure value: %a" Pp.CC.pp_value v1)

  let eval_program ~(config:Config.t) env p = match p with
    | Exp f ->
      let v = eval ~config env f in
      env, "-", v
    | LetDecl (x, f) ->
      let v = eval ~config env f in
      let env = Environment.add x v env in
      env, x, v
end

module KNorm = struct
  open Syntax.KNorm
  open Subst.KNorm

  let rec eval_exp ~(config:Config.t) kenv f =
    let monotonic = config.monotonic in
    let debug = config.debug in
    if debug then fprintf err_formatter "keval <-- %a@." Pp.KNorm.pp_exp f;
    match f with
    | Var x ->
      Environment.find x kenv
    | IConst i -> IntV i
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
    | Tuple xs ->
      TupleV (List.map (fun x -> Environment.find x kenv) xs)
    | Hd x ->
      let v = Environment.find x kenv in
      begin match v with
      | ConsV (v1, _) -> v1
      | CoerceV (ConsV (v1, _), CList s) -> coerce ~config v1 s
      | _ -> raise @@ Eval_bug "hd: not list value"
      end
    | Tl x ->
      let v = Environment.find x kenv in
      begin match v with
      | ConsV (_, v2) -> v2
      | CoerceV (ConsV (_, v2), s) -> coerce ~config v2 s
      | _ -> raise @@ Eval_bug "tl: not list value"
      end
    | Tget (x, i) ->
      let v = Environment.find x kenv in
      begin match v with
      | TupleV vs -> List.nth vs i
      | CoerceV (TupleV vs, CTuple ss) -> coerce ~config (List.nth vs i) (List.nth ss i)
      | _ -> raise @@ Eval_bug "tget: not tuple value"
      end
    | IfEqExp (x1, x2, f1, f2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> if i1 = i2 then eval_exp ~config kenv f1 else eval_exp ~config kenv f2
        | _ -> raise @@ Eval_bug "IfEqExp: not int value"
      end
    | IfLteExp (x1, x2, f1, f2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | IntV i1, IntV i2 -> if i1 <= i2 then eval_exp ~config kenv f1 else eval_exp ~config kenv f2
        | _ -> raise @@ Eval_bug "IfLteExp: not int value"
      end
    | MatchExp (x, ms) ->
      let v = Environment.find x kenv in
      eval_next ~config kenv v ms
    | AppMExp (x, y) ->
      let v1 = Environment.find x kenv in
      let v2 = Environment.find y kenv in
      eval_app_valM ~config kenv v1 v2
    | AppDExp (x1, (x2, x3)) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      let v3 = Environment.find x3 kenv in
      eval_app_valD ~config kenv v1 v2 v3
    | CAppExp (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v2 with
      | CoercionV c -> coerce ~config v1 c
      | _ -> raise @@ Eval_bug "capp: application of non coercion value"
      end
    | CSeqExp (x1, x2) ->
      let v1 = Environment.find x1 kenv in
      let v2 = Environment.find x2 kenv in
      begin match v1, v2 with
        | CoercionV c1, CoercionV c2 -> CoercionV (compose ~config c1 c2)
        | _ -> raise @@ Eval_bug "cseq: sequence of non coercion value"
      end
    | AppTy (x, _, tas) ->
      let v1 = Environment.find x kenv in
      let us = List.map nu_to_fresh tas in
      begin match v1 with
        | FunBV proc -> FunBV (fun _ -> proc us)
        | FunSV proc -> FunSV (fun _ -> proc us)
        | FunDualV proc -> FunDualV (fun _ -> proc us)
        | FunTyV proc -> proc us
        | _ -> raise @@ Eval_bug "AppTy: not fun value"
      end
    | CastExp (x, u1, u2, r_p) ->
      let v = Environment.find x kenv in
      cast ~config v u1 u2 r_p
    | CoercionExp c -> CoercionV c
    | LetExp (x, f1, f2) ->
      let v1 = eval_exp ~config kenv f1 in
      eval_exp ~config (Environment.add x v1 kenv) f2
    | LetFunExp (x, tvs, fd, f2) -> match fd with
      | FunB (y, f1) ->
        let v1 =
          FunBV (
            fun us -> fun v ->
            let f1 = subst_exp ~monotonic (Utils.List.zip tvs us) f1 in
            let rec f _ v =
              let kenv = Environment.add x (FunBV f) kenv in
              let kenv = Environment.add y v kenv in
              eval_exp ~config kenv f1
            in f [] v
          )
        in eval_exp ~config (Environment.add x v1 kenv) f2
      | FunS ((y, k), f1) ->
        let v1 =
          FunSV (
            fun us -> fun (v1, v2) ->
            let f1 = subst_exp ~monotonic (Utils.List.zip tvs us) f1 in
            let rec f _ (v1, v2) =
              let kenv = Environment.add x (FunSV f) kenv in
              let kenv = Environment.add y v1 kenv in
              let kenv = Environment.add k v2 kenv in
              eval_exp ~config kenv f1
            in f [] (v1, v2)
          )
        in eval_exp ~config (Environment.add x v1 kenv) f2
      | FunDual ((y, k), (f1, f1')) ->
        let v1 =
          FunDualV (
            fun us ->
            let f1 = subst_exp ~monotonic (Utils.List.zip tvs us) f1 in
            let f1' = subst_exp ~monotonic (Utils.List.zip tvs us) f1' in
            let rec f1_ v =
              let kenv = Environment.add x (FunDualV (fun _ -> (f1_, f1'_))) kenv in
              let kenv = Environment.add y v kenv in
              eval_exp ~config kenv f1
            and f1'_ (v, w) =
              let kenv = Environment.add x (FunDualV (fun _ -> (f1_, f1'_))) kenv in
              let kenv = Environment.add y v kenv in
              let kenv = Environment.add k w kenv in
              eval_exp ~config kenv f1'
            in (f1_, f1'_)
          )
        in eval_exp ~config (Environment.add x v1 kenv) f2
      | FunTy f1 ->
        let v1 =
          FunTyV (
            fun us ->
            let f1 = subst_exp ~monotonic (Utils.List.zip tvs us) f1 in
            eval_exp ~config kenv f1
          )
        in eval_exp ~config (Environment.add x v1 kenv) f2
  and cast ~config v u1 u2 (r, p) = 
    let print_debug f = Utils.Format.make_print_debug config.debug f in
    print_debug "cast <-- %a: %a => %a@." Pp.KNorm.pp_value v Pp.pp_ty u1 Pp.pp_ty u2;
    match u1, u2 with
    (* When tyvars are instantiated *)
    | TyVar (_, {contents = Some u1}), u2 | u1, TyVar (_, {contents = Some u2}) ->
      cast ~config v u1 u2 (r, p)
    (* IdBase: iota => iota ... ok*)
    | TyBool, TyBool | TyInt, TyInt | TyUnit, TyUnit -> v
    (* IdStar: ? => ? ... ok*)
    | TyDyn, TyDyn -> v
    (* Succeed / Fail: ? => U *)
    | TyDyn, (TyBool | TyInt | TyUnit | TyFun (TyDyn, TyDyn) | TyList TyDyn | TyRef TyDyn as u2) -> 
      begin match v, u2 with
      | Tagged (B, v), TyBool -> v (* bool => ? => bool ... ok *)
      | Tagged (I, v), TyInt -> v (* int => ? => int ... ok *)
      | Tagged (U, v), TyUnit -> v (* unit => ? => unit ... ok *)
      | Tagged (Ar, v), TyFun (TyDyn, TyDyn) -> v (* ?->? => ? => ?->? ... ok *)
      | Tagged (Li, v), TyList TyDyn -> v
      | Tagged (Rf, v), TyRef TyDyn -> v
      | Tagged _, _ -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_bug "untagged value"
      end
    | TyDyn, TyTuple us when List.fold_left (fun b u -> u = TyDyn && b) true us ->
      begin match v with
      | Tagged (Tp n, v) when n = List.length us -> v
      | Tagged _ -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_bug "untagged value"
      end
    (* AppCast *)
    | TyFun (u11, u12), TyFun (u21, u22) ->
      begin match v with
        | FunBV proc -> 
          FunBV (
            fun us -> fun x ->
              let arg = cast ~config x u21 u11 (r, (neg p)) in
              let res = proc us arg in
              cast ~config res u12 u22 (r, p)
          )
        | _ -> raise @@ Eval_bug "non procedual value"
      end
    | TyList u1, TyList u2 -> 
      if u1 = u2 then v 
      else begin match v with
      | NilV -> NilV
      | ConsV (h, t) -> ConsV (cast ~config h u1 u2 (r, p), cast ~config t (TyList u1) (TyList u2) (r, p))
      | _ -> raise @@ Eval_bug "non list value"
      end
    | TyTuple us1, TyTuple us2 ->
      if us1 = us2 then v
      else begin match v with
      | TupleV vs ->
        let rec cast_list vs us1 us2 res = match vs, us1, us2 with
        | v :: vs, u1 :: us1, u2 :: us2 -> cast_list vs us1 us2 ((cast ~config v u1 u2 (r, p)) :: res)
        | [], [], [] -> TupleV (List.rev res)
        | _ -> raise @@ Eval_bug "tuple length is wrong"
        in 
        cast_list vs us1 us2 []
      | _ -> raise @@ Eval_bug "non tuple value"
      end
    | TyRef _, TyRef _ -> raise @@ Eval_bug "ref cast yet"
    (* Tagged *)
    | TyBool, TyDyn -> Tagged (B, v)
    | TyInt, TyDyn -> Tagged (I, v)
    | TyUnit, TyDyn -> Tagged (U, v)
    | TyFun (TyDyn, TyDyn), TyDyn -> Tagged (Ar, v)
    | TyList TyDyn, TyDyn -> Tagged (Li, v)
    | TyTuple us, TyDyn when List.fold_left (fun b u -> u = TyDyn && b) true us -> Tagged (Tp (List.length us), v)
    | TyRef TyDyn, TyDyn -> Tagged (Rf, v)
    (* Ground *)
    | (TyFun _ as u1), (TyDyn as u2) ->
      let dfun = TyFun (TyDyn, TyDyn) in
      let v = cast ~config v u1 dfun (r, p) in
      cast ~config v dfun u2 (r, p)
    | TyList _, TyDyn ->
      let dlist = TyList TyDyn in
      let v = cast ~config v u1 dlist (r, p) in
      cast ~config v dlist TyDyn (r, p)
    | TyTuple us, TyDyn ->
      let dtuple = TyTuple (List.map (fun _ -> TyDyn) us) in
      let v = cast ~config v u1 dtuple (r, p) in
      cast ~config v dtuple TyDyn (r, p)
    | TyRef _, TyDyn ->
      let dref = TyRef TyDyn in
      let v = cast ~config v u1 dref (r, p) in
      cast ~config v dref u2 (r, p)
    (* Expand *)
    | TyDyn, TyFun _ ->
      let dfun = TyFun (TyDyn, TyDyn) in
      let v = cast ~config v u1 dfun (r, p) in 
      cast ~config v dfun u2 (r, p)
    | TyDyn, TyList _ ->
      let dlist = TyList TyDyn in
      let v = cast ~config v TyDyn dlist (r, p) in
      cast ~config v dlist u2 (r, p)
    | TyDyn, TyTuple us ->
      let dtuple = TyTuple (List.map (fun _ -> TyDyn) us) in
      let v = cast ~config v TyDyn dtuple (r, p) in
      cast ~config v dtuple u2 (r, p)
    | TyDyn, TyRef _ ->
      let dref = TyRef TyDyn in
      let v = cast ~config v TyDyn dref (r, p) in
      cast ~config v dref u2 (r, p)
    (* InstBase / InstArrow *)
    | TyDyn, (TyVar (_, ({contents = None} as x)) as u') ->
      begin match v with
        | Tagged ((B | I | U as t), v) ->
          let u = type_of_tag t in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          v
        | Tagged (Ar, v) -> 
          let u = TyFun (fresh_tyvar (), fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyFun (TyDyn, TyDyn)) u (r, p)
        | Tagged (Li, v) ->
          let u = TyList (fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyList TyDyn) u (r, p)
        | Tagged (Tp n, v) ->
          let u = TyTuple (List.init n (fun _ -> fresh_tyvar ())) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyTuple (List.init n (fun _ -> TyDyn))) u (r, p)
        | Tagged (Rf, v) ->
          let u = TyRef (fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty u'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyRef TyDyn) u (r, p)
        | _ -> raise @@ Eval_bug "cannot instamtiate"
      end
    | _ -> raise @@ Eval_bug (asprintf "cannot cast value: %a: %a => %a" Pp.KNorm.pp_value v Pp.pp_ty u1 Pp.pp_ty u2)
  and coerce ~config v c = (* TODO consume, psi *)
    let print_debug f = Utils.Format.make_print_debug config.debug f in
    print_debug "coerce <-- %a<%a>@." Pp.KNorm.pp_value v Pp.pp_coercion c;
    match v with
    | CoerceV (v, c') -> coerce ~config v (compose ~config c' c)
    | v -> match normalize_coercion ~monotonic:config.monotonic c with
      | CId _ -> v
      | CFail (_, (r, p), _) -> raise @@ Blame (r, p)
      | c when is_d c -> CoerceV (v, (*Typing.ITGL.normalize_coercion*) c)
      | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a" Pp.KNorm.pp_value v)
  and match_mf ~config kenv v mf = match v, mf with
    (* | _, MatchVar (id, _) ->
      let kenv = Environment.add id v kenv in
      true, kenv *)
    | ConsV (v1, v2), MatchCons (mf1, mf2) ->
      let b1, kenv = match_mf ~config kenv v1 mf1 in
      let b2, kenv = match_mf ~config kenv v2 mf2 in
      b1&&b2, kenv 
    | NilV, MatchNil _ -> true, kenv
    | IntV i1, MatchILit i2 -> if i1 = i2 then (true, kenv) else (false, kenv)
    | TupleV vs, MatchTuple mfs ->
      let rec iter kenv vs mfs b = match vs, mfs with
      | v :: vs, mf :: mfs ->
        let b', kenv = match_mf ~config kenv v mf in
        iter kenv vs mfs (b && b')
      | _ :: _, [] | [], _ :: _ -> false, kenv
      | [], [] -> b, kenv
      in
      iter kenv vs mfs true
    (* | IntV i, MatchBLit b -> if i = 1 && b then (true, kenv) else if i = 0 && not b then (false, kenv) else raise @@ Eval_bug "MatchBLit didn't match"
    | IntV 0, MatchULit -> true, kenv *)
    (* | arg, MatchAsc (mf, _) -> match_mf env arg mf *)
    | _, MatchWild _ -> true, kenv
    | CoerceV (ConsV (v1, v2), CList s), MatchCons _ -> 
      match_mf ~config kenv (ConsV (coerce ~config v1 s, coerce ~config v2 (CList s))) mf (* lazy *)
    | CoerceV (TupleV vs, CTuple ss), MatchTuple _ -> 
      match_mf ~config kenv (TupleV (List.map2 (fun v -> fun s -> coerce ~config v s) vs ss)) mf
    | _, (MatchVar _ | MatchBLit _ | MatchULit) -> raise @@ Eval_bug "MatchVar, MatchBLit, MatchULit  does not appear in KNormal form"
    | _ -> false, kenv 
  and eval_next ~config kenv v ms = match ms with
    | (mf, f) :: ms ->
      let b, kenv' = match_mf ~config kenv v mf in
      if b then eval_exp ~config kenv' f
      else eval_next ~config kenv v ms
    | [] -> raise @@ Eval_bug "Didn't match"
  and eval_app_valD ~config kenv v1 v2 v3 = match v1 with
    | FunSV proc -> proc [] (v2, v3)
    | FunDualV proc -> 
      begin match v3 with
      | CoercionV (CId _) -> fst (proc []) v2
      | _ -> snd (proc []) (v2, v3)
      end
    | CoerceV (v1, CFun (s, t)) -> 
      begin match v3 with
        | CoercionV c -> 
          let k = CoercionV (compose ~config t c) in
          eval_app_valD ~config kenv v1 (coerce ~config v2 s) k
        | _ -> raise @@ Eval_bug "app: application of non coercion value"
      end
    | _ -> raise @@ Eval_bug "app_valD: application of non procedure value"
  and eval_app_valM ~config env v1 v2 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunDualV proc -> fst (proc []) v2
    | FunBV proc -> proc [] v2
    | CoerceV (v1, CFun (s, t)) -> eval_app_valD ~config env v1 (coerce ~config v2 s) (CoercionV t)
    | _ -> raise @@ Eval_bug "app_valM: application of non procedure value"

  let eval_program ~(config:Config.t) kenv p =
    let monotonic = config.monotonic in
    match p with
    | Exp f -> let v = eval_exp ~config kenv f in kenv, "-", v
    | LetDecl (x, f) ->
      let v = eval_exp ~config kenv f in
      let kenv = Environment.add x v kenv in
      kenv, x, v
    | LetFunDecl (x, tvs, fd) -> match fd with
      | FunB (y, f') ->  
        let v = 
          FunBV (
            fun us -> fun v ->
            let f' = subst_exp ~monotonic (Utils.List.zip tvs us) f' in
            let rec f _ v =
              let kenv = Environment.add x (FunBV f) kenv in
              let kenv = Environment.add y v kenv in
              eval_exp ~config kenv f'
            in f [] v
          )
        in let kenv = Environment.add x v kenv in
        kenv, x, v
      | FunS ((y, k), f') -> 
        let v = 
          FunSV (
            fun us -> fun (v1, v2) ->
            let f' = subst_exp ~monotonic (Utils.List.zip tvs us) f' in
            let rec f _ (v1, v2) =
              let kenv = Environment.add x (FunSV f) kenv in
              let kenv = Environment.add y v1 kenv in
              let kenv = Environment.add k v2 kenv in
              eval_exp ~config kenv f'
            in f [] (v1, v2)
          )
        in let kenv = Environment.add x v kenv in
        kenv, x, v
      | FunDual ((y, k), (f1, f1')) -> 
        let v = 
          FunDualV (
            fun us -> 
            let f1 = subst_exp ~monotonic (Utils.List.zip tvs us) f1 in
            let f1' = subst_exp ~monotonic (Utils.List.zip tvs us) f1' in
            let rec f1_ v =
              let kenv = Environment.add x (FunDualV (fun _ -> (f1_, f1'_))) kenv in
              let kenv = Environment.add y v kenv in
              eval_exp ~config kenv f1
            and f1'_ (v, w) =
              let kenv = Environment.add x (FunDualV (fun _ -> (f1_, f1'_))) kenv in
              let kenv = Environment.add y v kenv in
              let kenv = Environment.add k w kenv in
              eval_exp ~config kenv f1'
            in (f1_, f1'_)
          )
        in let kenv = Environment.add x v kenv in
        kenv, x, v
      | FunTy f' -> 
        let v = 
          FunTyV (
            fun us ->
            let f' = subst_exp ~monotonic (Utils.List.zip tvs us) f' in
            eval_exp ~config kenv f'
          )
        in let kenv = Environment.add x v kenv in
        kenv, x, v
end