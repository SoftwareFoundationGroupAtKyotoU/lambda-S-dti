open Format
open Syntax
open Type_utils
open Coercion
open Normalize
open Unify

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
      | FPlus, FloatV f1, FloatV f2 -> FloatV (f1 +. f2)
      | FMinus, FloatV f1, FloatV f2 -> FloatV (f1 -. f2)
      | FMult, FloatV f1, FloatV f2 -> FloatV (f1 *. f2)
      | FDiv, FloatV f1, FloatV f2 -> FloatV (f1 /. f2)
      | Eq, IntV i1, IntV i2 -> BoolV (i1 = i2)
      | Neq, IntV i1, IntV i2 -> BoolV (i1 <> i2)
      | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
      | Lte, IntV i1, IntV i2 -> BoolV (i1 <= i2)
      | Gt, IntV i1, IntV i2 -> BoolV (i1 > i2)
      | Gte, IntV i1, IntV i2 -> BoolV (i1 >= i2)
      | FEq, FloatV f1, FloatV f2 -> BoolV (f1 = f2)
      | FNeq, FloatV f1, FloatV f2 -> BoolV (f1 <> f2)
      | FLt, FloatV f1, FloatV f2 -> BoolV (f1 < f2)
      | FLte, FloatV f1, FloatV f2 -> BoolV (f1 <= f2)
      | FGt, FloatV f1, FloatV f2 -> BoolV (f1 > f2)
      | FGte, FloatV f1, FloatV f2 -> BoolV (f1 >= f2)
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
    | FConst f -> FloatV f
    | BConst b -> BoolV b
    | UConst -> UnitV
    | BinOp (op, f1, f2) ->
      let v1 = eval ~config env f1 in
      begin match op with
      | And -> begin match v1 with
        | BoolV false -> BoolV false
        | BoolV true -> 
          let v2 = eval ~config env f2 in
          begin match v2 with
          | BoolV _ -> v2
          | _ -> raise @@ Eval_bug "binop: unexpected type of argument"
          end
        | _ -> raise @@ Eval_bug "binop: unexpected type of argument"
        end
      | Or -> begin match v1 with
        | BoolV true -> BoolV true
        | BoolV false -> 
          let v2 = eval ~config env f2 in
          begin match v2 with
          | BoolV _ -> v2
          | _ -> raise @@ Eval_bug "binop: unexpected type of argument"
          end
        | _ -> raise @@ Eval_bug "binop: unexpected type of argument"
        end
      | _ ->
        let v2 = eval ~config env f2 in
        eval_binop op v1 v2
      end
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
      if config.intoB then
        let rec deref = function
          | CastRefV (v, u1, u2, (r, p)) ->
            let v = deref v in
            cast ~config v u1 u2 (r, p)
          | RefV ({ contents = v, _ }) -> v
          | _ -> raise @@ Eval_bug "eval: not refV deref"
        in
        deref v
      else begin match v, ou with
        | RefV { contents = (v, u) }, Some u' when monotonic ->
          let s = make_s_coercion ~monotonic (normalize_type u) (Utils.Error.dummy_range, Pos) (normalize_type u') in (* TODO *)
          toplevel_coerce ~config v s
        | RefV ({ contents = v, _ }), _ -> v
        | CoerceV (RefV ({ contents = v, _ }), CRef (c1, _)), _ when not monotonic -> toplevel_coerce ~config v c1
        | _ -> raise @@ Eval_bug "eval: not refV deref"
      end
    | SubstExp (f1, f2, ou) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      if config.intoB then
        let rec subst v1 v2 = match v1 with
          | CastRefV (v1, u1, u2, (r, p)) ->
            subst v1 (cast ~config v2 u2 u1 (r, neg p))
          | RefV ({ contents = _, u } as rv) ->
            rv := v2, u; UnitV
          | _ -> raise @@ Eval_bug "eval: not refV subst"
        in
        subst v1 v2
      else begin match v1, ou with
        | RefV ({ contents = (_, u) } as rv), Some u' when monotonic ->
          let s = make_s_coercion ~monotonic (normalize_type u') (Utils.Error.dummy_range, Pos) (normalize_type u) in (* TODO *)
          let v, psi = coerce ~config v2 s [] in
          rv := v, u;
          consume ~config psi;
          UnitV
        | RefV ({ contents = _, u } as rv), _ ->
          rv := v2, u; UnitV
        | CoerceV (RefV ({ contents = _, u } as rv), CRef (_, c2)), _ when not monotonic ->
          rv := (toplevel_coerce ~config v2 c2), u; UnitV
        | _ -> raise @@ Eval_bug "eval: not refV deref"
      end
    | MakeArrayExp (f1, f2, u) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      begin match v1 with
      | IntV i -> ArrayV (ref (Array.make i v2, u))
      | _ -> raise @@ Eval_bug "eval: not int in MakeArrayExp"
      end
    | GetExp (f1, f2, ou) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      begin match v2 with
      | IntV i -> 
        if config.intoB then
          let rec get v = match v with
            | CastArrayV (v, u1, u2, (r, p)) ->
              let v = get v in
              cast ~config v u1 u2 (r, p)
            | ArrayV { contents = vs, _ } -> vs.(i)
            | _ -> raise @@ Eval_bug "eval: not arrayV get"
          in
          get v1
        else begin match v1, ou with
          | ArrayV { contents = vs, u }, Some u' when monotonic ->
            let s = make_s_coercion ~monotonic (normalize_type u) (Utils.Error.dummy_range, Pos) (normalize_type u') in (* TODO *)
            toplevel_coerce ~config vs.(i) s
          | ArrayV { contents = vs, _ }, _ -> vs.(i)
          | CoerceV (ArrayV { contents = vs, _ }, CArray (c1, _)), _ when not monotonic -> toplevel_coerce ~config vs.(i) c1
          | _ -> raise @@ Eval_bug "eval: not refV deref"
        end
      | _ -> raise @@ Eval_bug "eval: not IntV GetExp"
      end
    | PutExp (f1, f2, f3, ou) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      let v3 = eval ~config env f3 in
      begin match v2 with
      | IntV i ->
        if config.intoB then
          let rec put v1 v2 = match v1 with
            | CastArrayV (v1, u1, u2, (r, p)) ->
              put v1 (cast ~config v2 u2 u1 (r, neg p))
            | ArrayV { contents = vs, _ } ->
              vs.(i) <- v3; UnitV
            | _ -> raise @@ Eval_bug "eval: not refV subst"
          in
          put v1 v2
        else begin match v1, ou with
          | ArrayV { contents = vs, u }, Some u' when monotonic ->
            let s = make_s_coercion ~monotonic (normalize_type u') (Utils.Error.dummy_range, Pos) (normalize_type u) in (* TODO *)
            let v, psi = coerce ~config v3 s [] in
            vs.(i) <- v;
            consume ~config psi;
            UnitV
          | ArrayV { contents = vs, _ }, _ ->
            vs.(i) <- v3; UnitV
          | CoerceV (ArrayV { contents = vs, _ }, CArray (_, c2)), _ when not monotonic ->
            vs.(i) <- toplevel_coerce ~config v3 c2; UnitV
          | _ -> raise @@ Eval_bug "eval: not refV deref"
        end
      | _ -> raise @@ Eval_bug "eval: not IntV PutExp"
      end
    | LengthExp f ->
      let v = eval ~config env f in
      if config.intoB then
        let rec length = function
          | CastArrayV (v, _, _, _) -> length v
          | ArrayV { contents = vs, _ } -> Array.length vs
          | _ -> raise @@ Eval_bug "eval: not arrayV length"
        in IntV (length v)
      else begin match v with
        | ArrayV { contents = vs, _ } -> IntV (Array.length vs)
        | CoerceV (ArrayV { contents = vs, _ }, (CArray _ | CMArray _)) -> IntV (Array.length vs)
        | _ -> raise @@ Eval_bug "eval: not arrayV length"
      end
    | CastExp (f, u1, u2, r_p) ->
      let v = eval ~config env f in
      cast ~config v u1 u2 r_p
    | CAppExp (f1, f2) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      begin match v2 with
        | CoercionV c -> toplevel_coerce ~config v1 c
        | _ -> raise @@ Eval_bug "capp: application of non coercion value"
      end
    | CCompExp (f1, f2) ->
      let v1 = eval ~config env f1 in
      let v2 = eval ~config env f2 in
      begin match v1, v2 with
        | CoercionV c1, CoercionV c2 -> CoercionV (compose ~config c1 c2)
        | _ -> raise @@ Eval_bug "cseq: sequence of non coercion value"
      end
    | CoercionExp c -> CoercionV c
  and match_mf ~config env v mf = match v, mf with
    | _, MatchVar id ->
      let env = Environment.add id v env in
      true, env
    | ConsV (v1, v2), MatchCons (mf1, mf2) ->
      let b1, env = match_mf ~config env v1 mf1 in
      let b2, env = match_mf ~config env v2 mf2 in
      b1&&b2, env
    | NilV, MatchNil -> true, env
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
    | _, MatchWild -> true, env
    | CastListV (v, _, _, _), MatchNil -> match_mf ~config env v mf
    | CastListV _, MatchCons _ ->
      let rec destruct_cons_cast = function
        | ConsV (v1, v2) -> Some (v1, v2)
        | CastListV (v, u1, u2, (r, p)) ->
          begin match destruct_cons_cast v with
          | Some (v1, v2) ->
            Some (cast ~config v1 u1 u2 (r, p), CastListV (v2, u1, u2, (r, p)))
          | None -> None
          end
        | _ -> None
      in
      begin match destruct_cons_cast v with
      | Some (v1, v2) -> match_mf ~config env (ConsV (v1, v2)) mf
      | None -> false, env
      end
    | CastTupleV _, MatchTuple _ ->
      let rec destruct_tuple_cast = function
        | TupleV vs -> Some vs
        | CastTupleV (v, us1, us2, (r, p)) ->
          begin match destruct_tuple_cast v with
          | Some vs ->
            Some (List.map2 (fun v (u1, u2) -> cast ~config v u1 u2 (r, p)) vs (List.combine us1 us2))
          | None -> None
          end
        | _ -> None
      in
      begin match destruct_tuple_cast v with
      | Some vs -> match_mf ~config env (TupleV vs) mf
      | None -> false, env
      end
    | CoerceV (NilV, CList _), MatchNil -> true, env
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
    | TyInt, TyInt
    | TyBool, TyBool
    | TyUnit, TyUnit
    | TyFloat, TyFloat -> v
    (* IdStar *)
    | TyDyn, TyDyn -> v
    (* Succeed / Fail *)
    | TyDyn, (TyInt | TyBool | TyUnit | TyFloat | TyFun (TyDyn, TyDyn) | TyList TyDyn | TyRef TyDyn | TyArray TyDyn as u2) ->
      begin match v, u2 with
      | Tagged (I, v), TyInt -> v
      | Tagged (B, v), TyBool -> v
      | Tagged (U, v), TyUnit -> v
      | Tagged (F, v), TyFloat -> v
      | Tagged (Fn, v), TyFun (TyDyn, TyDyn) -> v
      | Tagged (Li, v), TyList TyDyn -> v
      | Tagged (Rf, v), TyRef TyDyn -> v
      | Tagged (Ar, v), TyArray TyDyn -> v
      | Tagged _, _ -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_bug "untagged value"
      end
    | TyDyn, TyTuple us when List.for_all (fun u -> u = TyDyn) us ->
      begin match v with
      | Tagged (Tp n, v) when n = List.length us -> v
      | Tagged _ -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_bug "untagged value"
      end
    (* AppCast *)
    | TyFun (u11, u12), TyFun (u21, u22) -> 
      if u1 = u2 then v 
      else CastFunV (v, u11, u12, u21, u22, (r, p))
    | TyList u1, TyList u2 -> 
      if TyList u1 = TyList u2 then v
      else if not config.eager then CastListV (v, u1, u2, (r, p))
      else begin match v with
      | NilV -> NilV
      | ConsV (h, t) -> ConsV (cast ~config h u1 u2 (r, p), cast ~config t (TyList u1) (TyList u2) (r, p))
      | _ -> raise @@ Eval_bug "non list value"
      end
    | TyTuple us1, TyTuple us2 ->
      if u1 = u2 then v
      else if not config.eager then CastTupleV (v, us1, us2, (r, p))
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
    | TyRef u1, TyRef u2 ->
      if TyRef u1 = TyRef u2 then v 
      else CastRefV (v, u1, u2, (r, p))
    | TyArray u1, TyArray u2 ->
      if TyArray u1 = TyArray u2 then v 
      else CastArrayV (v, u1, u2, (r, p))
    (* Tagged *)
    | TyInt, TyDyn -> Tagged (I, v)
    | TyBool, TyDyn -> Tagged (B, v)
    | TyUnit, TyDyn -> Tagged (U, v)
    | TyFloat, TyDyn -> Tagged (F, v)
    | TyFun (TyDyn, TyDyn), TyDyn -> Tagged (Fn, v)
    | TyList TyDyn, TyDyn -> Tagged (Li, v)
    | TyTuple us, TyDyn when List.fold_left (fun b u -> u = TyDyn && b) true us -> Tagged (Tp (List.length us), v)
    | TyRef TyDyn, TyDyn -> Tagged (Rf, v)
    | TyArray TyDyn, TyDyn -> Tagged (Ar, v)
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
    | TyArray _, TyDyn ->
      let darray = TyArray TyDyn in
      let v = cast ~config v u1 darray (r, p) in
      cast ~config v darray u2 (r, p)
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
    | TyDyn, TyArray _ ->
      let darray = TyArray TyDyn in
      let v = cast ~config v TyDyn darray (r, p) in
      cast ~config v darray u2 (r, p)
    (* InstBase / InstArrow *)
    | TyDyn, (TyVar (_, ({ contents = None } as x)) as x') -> begin
        match v with
        | Tagged (I | B | U | F as t, v) ->
          let u = type_of_tag t in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          v
        | Tagged (Fn, v) ->
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
        | Tagged (Ar, v) ->
          let u = TyArray (fresh_tyvar ()) in
          print_debug "DTI: %a is instantiated to %a@."
            Pp.pp_ty x'
            Pp.pp_ty u;
          x := Some u;
          cast ~config v (TyArray TyDyn) u (r, p)
        | _ -> raise @@ Eval_bug "cannot instantiate"
      end
    | _ -> raise @@ Eval_bug (asprintf "cannot cast value: %a" Pp.CC.pp_value v)
  and coerce ~config v c (psi: (value * ty) list) =
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
    | RefV rv, CMRef (_, u) when monotonic -> RefV rv, psi @ [RefV rv, u]
    | ArrayV rv, CMArray (_, u) when monotonic -> ArrayV rv, psi @ [ArrayV rv, u]
    | v, c when is_d c -> CoerceV (v, c), psi
    | _ -> raise @@ Eval_bug (asprintf "cannot coercion value: %a <%a>" Pp.CC.pp_value v Pp.pp_coercion c)
  and consume ~config = function
    | (v, u) :: psi ->
      let print_debug f = Utils.Format.make_print_debug config.debug f in
      print_debug "cons <-- %a, %a@." Pp.CC.pp_value v Pp.pp_ty u;
      begin match v with
      | RefV ({ contents = v, u' } as rv) ->
        let u'' = try unify_meet u' u with Typing.Type_error _ -> raise @@ Blame (Utils.Error.dummy_range, Pos) in (* TODO *)
        if u'' = u' then
          consume ~config psi
        else begin
          let s = make_s_coercion ~monotonic:config.monotonic (normalize_type u') (Utils.Error.dummy_range, Pos) (normalize_type u'') in (* TODO *)
          let v, psi = coerce ~config v s psi in
          rv := v, u'';
          consume ~config psi
        end
      | ArrayV ({ contents = vs, u' } as rv) ->
        let u'' = try unify_meet u' u with Typing.Type_error _ -> raise @@ Blame (Utils.Error.dummy_range, Pos) in (* TODO *)
        if u'' = u' then
          consume ~config psi
        else begin
          let s = make_s_coercion ~monotonic:config.monotonic (normalize_type u') (Utils.Error.dummy_range, Pos) (normalize_type u'') in (* TODO *)
          let n = Array.length vs in
          let vs' = Array.make n (IntV 0) in
          let rec loop i psi =
            if i = n then psi
            else
              let v, psi = coerce ~config vs.(i) s psi in
              vs'.(i) <- v;
              loop (i + 1) psi
          in
          let psi = loop 0 psi in
          rv := vs', u'';
          consume ~config psi
        end
      | _ -> raise @@ Eval_bug "not ref or array is passed to consume"
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
          let v2 = toplevel_coerce ~config v2 s in
          eval_app_valD ~config env v1 v2 k
        | _ -> raise @@ Eval_bug "app: application of non coercion value"
      end
    | _ -> raise @@ Eval_bug (asprintf "app_valD: application of non procedure value: %a" Pp.CC.pp_value v1)
  and eval_app_valM ~config env v1 v2 = match v1 with (*値まで評価しきっているので，論文のようなlet k = t;;c in ~~とはできない*)
    | FunBV proc -> proc [] v2
    | FunDualV proc -> fst (proc []) v2
    | CoerceV (v1, CFun (s, t)) -> 
      let v2 = toplevel_coerce ~config v2 s in
      eval_app_valD ~config env v1 v2 (CoercionV t)
    | CastFunV (v1, u11, u12, u21, u22, (r, p)) ->
      let v2 = cast ~config v2 u21 u11 (r, neg p) in
      let v = eval_app_valM ~config env v1 v2 in
      cast ~config v u12 u22 (r, p)
    | _ -> raise @@ Eval_bug (asprintf "app_valM: application of non procedure value: %a" Pp.CC.pp_value v1)
  and toplevel_coerce ~config v c =
    let v, psi = coerce ~config v c [] in
    consume ~config psi;
    v

  let eval_program ~(config:Config.t) env p = match p with
    | Exp f ->
      let v = eval ~config env f in
      env, "-", v
    | LetDecl (x, f) ->
      let v = eval ~config env f in
      let env = Environment.add x v env in
      env, x, v
end