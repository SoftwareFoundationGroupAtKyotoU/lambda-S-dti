open Syntax
open Syntax.C
open Config
open Utils.Error
open Static_manage

exception ToC_bug of string
exception ToC_error of string

let dummy_value = Cast (VALUE, Null)

let string_of_tag = function
  | I -> "INT"
  | B -> "BOOL"
  | U -> "UNIT"
  | Fn -> "FN"
  | Li -> "LI"
  | Tp _ -> "TP"
  | Rf -> "RF"

let string_of_tyvar (i, _) = "_ty" ^ string_of_int i

let toC_ty = function
  | TyInt -> Addr "tyint"
  | TyBool -> Addr "tybool"
  | TyUnit -> Addr "tyunit"
  | TyDyn -> Addr "tydyn"
  | TyFun (TyDyn, TyDyn) -> Addr "tyfn"
  | TyFun (_, _) as u -> Addr (TyManager.find u)
  | TyList TyDyn -> Addr "tyli"
  | TyList _ as u -> Addr (TyManager.find u)
  | TyTuple _ as u -> Addr (TyManager.find u)
  | TyRef TyDyn -> Addr "tyrf"
  | TyRef _ as u -> Addr (TyManager.find u)
  | TyVar (i, { contents = None }) as u ->
    begin try 
      Addr (TyManager.find u)
    with Not_found ->
      Var (Format.asprintf "_ty%d" i)
    end
  | TyVar (i, { contents = Some (TyFun _) }) -> Var (Format.asprintf "_tyfun%d" i)
  | TyVar (i, { contents = Some (TyList _) }) -> Var (Format.asprintf "_tylist%d" i)
  | TyVar (i, { contents = Some (TyTuple _) }) -> Var (Format.asprintf "_tytuple%d" i)
  | TyVar (i, { contents = Some (TyRef _) }) -> Var (Format.asprintf "_tyref%d" i)
  | TyVar _ -> raise @@ ToC_bug "tyvar should not contain other than constructor type"
  | TyCoercion _ -> raise @@ ToC_error "toC_ty tycoercion"

let toC_ta = function
  | Ty u -> toC_ty u
  | TyNu -> App (Var "newty", [])

let toC_tycontent = function
  | TyVar _ -> Struct ["tykind", Var "TYVAR"]
  | TyFun (u1, u2) ->
    Struct ["tykind", Var "TYFUN"; "tydat", Struct ["tyfun", Struct ["left", toC_ty u1; "right", toC_ty u2]]]
  | TyList u ->
    Struct ["tykind", Var "TYLIST"; "tydat", Struct ["tylist", toC_ty u]]
  | TyTuple us ->
    Struct ["tykind", Var "TYTUPLE"; "tydat", Struct ["tytuple", Struct ["arity", Int (List.length us); "tys", Cast (ARRAY (PTR TY), Array (List.map (fun u -> toC_ty u) us))]]] 
  | TyRef u -> Struct ["tykind", Var "TYREF"; "tydat", Struct ["tyref", toC_ty u]]
  | _ as u -> raise @@ ToC_bug (Format.asprintf "toC_content yet: %a" Pp.pp_ty u)

(* ========================================= *)

let int_of_pos = function Pos -> 1 | Neg -> 0

let rid r = 
  try
    int_of_string @@ RangeManager.find r
  with
    Not_found -> raise @@ ToC_bug "rid cannot find r"

let rec check_has_tv = function
  | CId _ | CInj _ | CProj _ | CFail _ -> false
  | CList c' -> check_has_tv c'
  | CTvInj _ | CTvProj _ | CTvProjInj _ -> true
  | CSeq (c1, c2) | CFun (c1, c2) | CRef (c1, c2) -> (check_has_tv c1) || (check_has_tv c2)
  | CTuple cs -> List.fold_left (fun b c -> b || check_has_tv c) false cs
  | CMRef (u1, u2) ->
    let rec has_tv_ty = function
      | TyVar _ -> true
      | TyFun (u1, u2) -> has_tv_ty u1 || has_tv_ty u2
      | TyList u' | TyRef u' -> has_tv_ty u'
      | TyTuple us -> List.exists has_tv_ty us
      | _ -> false
    in
    has_tv_ty u1 || has_tv_ty u2

let rec toC_crc x c =
  let stm_crc x c = match c with
    | CId _ -> [], Addr "crc_id"
    | CSeq (CId _, CInj (I | B | U | Fn | Li | Rf as g)) -> [], Addr ("crc_inj_" ^ string_of_tag g)
    | CSeq (CMRef (_, TyDyn), CInj Rf) -> [], Addr ("crc_inj_RF")
    | _ ->
      if CrcManager.mem c then [], Addr (CrcManager.find c)
      else
        let stm, exp = toC_crc x c in
        SDecl (VALUE, x, None) :: stm @ [SDecl (CRC, x ^ "_tmp" , Some exp); SAssign (LVar x, Cast (VALUE, App (Var "alloc_crc", [Addr (x ^ "_tmp")])))], Cast (PTR CRC, Var x)
  in
  let has_tv_val = if check_has_tv c then 1 else 0 in
  match c with
    | CSeq (c', CInj g) ->
      let arity = match g with Tp arity -> arity | _ -> 0 in
      let stm, ptr_crc = stm_crc (x ^ "_inj") c' in
      stm,
      Struct [
        "crckind", Var "SEQ_INJ";
        "g_inj", Var ("G_" ^ string_of_tag g);
        "arity_inj", Int arity;
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["seq_tv", Struct ["ptr", Struct ["s", ptr_crc]]]
      ]
    | CSeq (CProj (g, (r, p)), c') ->
      let arity = match g with Tp arity -> arity | _ -> 0 in
      let stm, ptr_crc = stm_crc (x ^ "_inj") c' in
      stm,
      Struct [
        "crckind", Var "SEQ_PROJ";
        "g_proj", Var ("G_" ^ string_of_tag g);
        "p_proj", Int (int_of_pos p);
        "arity_proj", Int arity;
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["seq_tv", Struct ["rid_proj", Int (rid r); "ptr", Struct ["s", ptr_crc]]]
      ]
    | CTvInj (tv, (r, p)) ->
      [],
      Struct [
        "crckind", Var "TV_INJ";
        "p_inj", Int (int_of_pos p);
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["seq_tv", Struct ["rid_inj", Int (rid r); "ptr", Struct ["tv", toC_ty (TyVar tv)]]]
      ]
    | CTvProj (tv, (r, p)) ->
      [],
      Struct [
        "crckind", Var "TV_PROJ";
        "p_proj", Int (int_of_pos p);
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["seq_tv", Struct ["rid_proj", Int (rid r); "ptr", Struct ["tv", toC_ty (TyVar tv)]]]
      ]
    | CFun (c1, c2) ->
      let stm1, ptr_crc1 = stm_crc (x ^ "_fun1") c1 in
      let stm2, ptr_crc2 = stm_crc (x ^ "_fun2") c2 in
      stm1 @ stm2,
      Struct [
        "crckind", Var "FUN";
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["fun_crc", Struct ["c1", ptr_crc1; "c2", ptr_crc2]]
      ]
    | CList c ->
      let stm, ptr_crc = stm_crc (x ^ "_list") c in
      stm,
      Struct [
        "crckind", Var "LIST";
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["lst_crc", ptr_crc]
      ]
    | CTuple cs ->
      let stms, ptr_crcs = List.split @@ List.mapi (fun i c -> stm_crc (x ^ "_elm" ^ string_of_int i) c) cs in
      List.flatten stms,
      Struct [
        "crckind", Var "TUPLE";
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["tpl_crc", Struct ["arity", Int (List.length cs); "crcs", Cast (ARRAY (PTR CRC), Array ptr_crcs)]]
      ]
    | CRef (c1, c2) ->
      let stm1, ptr_crc1 = stm_crc (x ^ "_ref1") c1 in
      let stm2, ptr_crc2 = stm_crc (x ^ "_ref2") c2 in
      stm1 @ stm2,
      Struct [
        "crckind", Var "REF";
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["ref_crc", Struct ["c1", ptr_crc1; "c2", ptr_crc2]]
      ]
    | CMRef (_, u) ->
      [],
      Struct [
        "crckind", Var "REF";
        "has_tv", Int has_tv_val;
        "crcdat", Struct ["mref_crc", toC_ty u]
      ]
    | _ as c -> raise @@ ToC_bug (Format.asprintf "toC_crc yet: %a" Pp.pp_coercion c)

(*
(* コアーションの定義 *)
let toC_crccontent ppf (c, name) = 
  ...
  | CMRef _ -> ...
*)

  (*
  ...
  | CMRef _ -> ...
  | _ -> raise @@ ToC_bug "bad coercion" *)

(* ========================================= *)

let app_env l n f lst =
  let lval_env = LArrow (l, "env") in
  List.mapi (fun i h -> SAssign (LIndex (lval_env, n + i), Cast (PTR VOID, f h))) lst

let alloc_closure env_size =
  Malloc (VALUE, Add (Sizeof FUN, Mul (Sizeof (PTR VOID), Int env_size)))

let set_func_stm ~config fun_x func_d func_m =
  if config.intoB || config.static then
    [SAssign (LArrow (fun_x, "funcM"), func_m)]
  else if config.alt then
    [SAssign (LArrow (fun_x, "funcD"), func_d);
     SAssign (LArrow (fun_x, "funcM"), func_m)]
  else
    [SAssign (LArrow (fun_x, "funcD"), func_d)]

let make_cls_stm ~set_func x ({ entry = _; fvs; offset = n; ftvs }: Cls.closure) =
  let env_size = List.length fvs + n + List.length ftvs in
  let fun_x = LCast (PTR FUN, LVar x) in
  SDecl (VALUE, x, Some (alloc_closure env_size))
  :: set_func fun_x
  @ app_env fun_x 0 (fun fv -> Var fv) fvs
  @ app_env fun_x (List.length fvs + n) (fun ftv -> Var (string_of_tyvar ftv)) ftvs

let set_ty i opu =
  let u, name = match opu with
    | None -> TyVar (i, ref None), "_ty" ^ string_of_int i
    | Some (TyFun _ as u) ->
      u, "_tyfun" ^ string_of_int i
    | Some (TyList _ as u) ->
      u, "_tylist" ^ string_of_int i
    | Some (TyTuple _ as u) ->
      u, "_tytuple" ^ string_of_int i
    | Some (TyRef _ as u) ->
      u, "_tyref" ^ string_of_int i
    | Some u -> raise @@ ToC_bug (Format.asprintf "set_ty yet: %a" Pp.pp_ty u)
  in
  name, [SAssign (LDeref (LVar name), Cast (TY, toC_tycontent u))]
    (* 
    | Some _ -> raise @@ ToC_bug "not tyfun or tylist is in tyvar option"
    end *)

let rec toC_mf ~config x_exp = function
  | MatchVar _ | MatchBLit _ | MatchULit -> raise @@ ToC_bug "MatchVar, MatchBLit, MatchULit should not appear in toC"
  | MatchILit i -> Eq (x_exp, Int i)
  | MatchWild -> Int 1
  | MatchNil ->
    if config.eager then
      Eq (Cast (PTR LST, x_exp), Null)
    else
      App (Var "is_NULL", [Cast (PTR LST, x_exp)])
  | MatchCons (mf1, mf2) ->
    if config.eager then
      let mf1 = toC_mf ~config (Arrow (Cast (PTR LST, x_exp), "h")) mf1 in
      let mf2 = toC_mf ~config (Arrow (Cast (PTR LST, x_exp), "t")) mf2 in
      And (Neq (Cast (PTR LST, x_exp), Null), And (mf1, mf2))
    else
      let mf1 = toC_mf ~config (App (Var "hd", [Cast (PTR LST, x_exp)])) mf1 in
      let mf2 = toC_mf ~config (App (Var "tl", [Cast (PTR LST, x_exp)])) mf2 in
      And (Not (App (Var "is_NULL", [Cast (PTR LST, x_exp)])), And (mf1, mf2))
  | MatchTuple mfs ->
    let toC_mfi mf i =
      if config.eager then
        toC_mf ~config (Index (Arrow (Cast (PTR TPL, x_exp), "fields"), i)) mf
      else
        toC_mf ~config (App (Var "tget", [Cast (PTR TPL, x_exp); Int i])) mf
    in
    List.fold_left (fun e1 e2 -> And (e1, e2)) (Int 1) (List.mapi (fun i mf -> toC_mfi mf i) mfs)
  (* | _ as mf -> ignore config; raise @@ ToC_bug (Format.asprintf "toC_mf yet: %a" Pp.pp_matchform mf) *)

let rec toC_exp ~is_main ~config = function
  | Cls.Let (x, f1, f2) ->
    SDecl (VALUE, x, None) :: toC_assign ~config x f1 @ toC_exp ~is_main ~config f2
  | Cls.IfEq (x, y, f1, f2) ->
    SIf (Eq (Var x, Var y), toC_exp ~is_main ~config f1, toC_exp ~is_main ~config f2) :: []
  | Cls.IfLte (x, y, f1, f2) ->
    SIf (Lte (Var x, Var y), toC_exp ~is_main ~config f1, toC_exp ~is_main ~config f2) :: []
  | Cls.MakeCls (x, cls, f) ->
    let set_func fun_x =
      let alt_str = if config.alt then "alt_" else "" in
      let func_d = Var ("fun_" ^ cls.entry) in
      let func_m = Var ("fun_" ^ alt_str ^ cls.entry) in
      set_func_stm ~config fun_x func_d func_m
    in
    make_cls_stm ~set_func x cls @ toC_exp ~is_main ~config f
  | Cls.MakeTyCls (x, cls, f) ->
    let set_func fun_x = [SAssign (LArrow (fun_x, "funcM"), Var ("tfun_" ^ cls.entry))] in
    make_cls_stm ~set_func x cls @ toC_exp ~is_main ~config f
  | Cls.SetTy ((i, { contents = opu }), f) ->
    let name, stm = set_ty i opu in
    SDecl (PTR TY, name, Some (Malloc (PTR TY, Sizeof TY))) :: stm @ toC_exp ~is_main ~config f
  | Cls.Match (x, ms) ->
    List.fold_left (fun stm (mf, f) -> [SIf (toC_mf ~config (Var x) mf, toC_exp ~is_main ~config f, stm)])
      [SApp (Var "printf", [Str "didn't match"]); SApp (Var "exit", [Int 1])] (List.rev ms)
  | Cls.Var _ | Cls.Int _ | Cls.Coercion _ | Cls.Nil | Cls.Tuple _ | Cls.Ref _
  | Cls.Hd _ | Cls.Tl _ | Cls.Tget _ | Cls.Deref _ 
  | Cls.Add _ | Cls.Sub _ | Cls.Mul _ | Cls.Div _ | Cls.Mod _ | Cls.Cons _ | Cls.Subst _ | Cls.CComp _
  | Cls.AppDDir _ | Cls.AppDCls _  | Cls.AppMDir _ | Cls.AppMCls _ | Cls.AppTy _ | Cls.AppTyFun _ | Cls.CApp _ | Cls.Cast _
    as f ->
    let return = SReturn (if is_main then Int 0 else Var "retv") in
    SDecl (VALUE, "retv", None) :: toC_assign ~config "retv" f @ [return]
and toC_assign ~config x f =
  let assign_x e = SAssign (LVar x, e) :: [] in
  match f with
  | Cls.Var y -> assign_x (Var y)
  | Cls.Int i -> assign_x (Int i)
  | Cls.Nil -> assign_x dummy_value
  | Cls.Tuple ys ->
    let arity = List.length ys in
    assign_x (Malloc (VALUE, Add (Sizeof TPL_RAW, Mul (Sizeof VALUE, Int arity)))) @ [SAssign (LDot (LArrow (LCast (PTR TPL_RAW, LVar x), "hdr"), "arity"), Int arity)]
    @ List.mapi (fun i y -> SAssign (LIndex (LArrow (LCast (PTR TPL_RAW, LVar x), "fields"), i), Var y)) ys
  | Cls.Ref (y, u) ->
    if config.monotonic then
      let c = toC_ty u in
      assign_x (Malloc (VALUE, Sizeof REF)) @ [SAssign (LDeref (LCast (PTR REF, LVar x)), Cast (REF, Struct ["v", Var y; "u", c]))]
    else if config.static then
      assign_x (Malloc (VALUE, Sizeof REF)) @ [SAssign (LDeref (LCast (REF, LVar x)), Var y)]
    else
      assign_x (Malloc (VALUE, Sizeof REF)) @ [SAssign (LArrow (LCast (PTR REF, LVar x), "v"), Var y)]
  | Cls.Coercion c -> begin match c with
    | CId _ -> assign_x (Cast (VALUE, Addr "crc_id"))
    | CSeq (CId _, CInj (I | B | U | Fn | Li | Rf as g)) -> assign_x (Cast (VALUE, Addr ("crc_inj_" ^ string_of_tag g)))
    | CSeq (CMRef (_, TyDyn), CInj Rf) -> assign_x (Cast (VALUE, Addr ("crc_inj_RF")))
    | _ ->
      if CrcManager.mem c then assign_x (Cast (VALUE, Addr (CrcManager.find c)))
      else
        let stm, exp = toC_crc x c in
        stm @ [SDecl (CRC, x ^ "_tmp" , Some exp)] @ assign_x (Cast (VALUE, App (Var "alloc_crc", [Addr (x ^ "_tmp")])))
    end
  | Cls.Hd y ->
    if config.eager then
      assign_x (Arrow (Cast (PTR LST, Var y), "h"))
    else
      assign_x (App (Var "hd", [Cast (PTR LST, Var y)]))
  | Cls.Tl y ->
    if config.eager then
      assign_x (Arrow (Cast (PTR LST, Var y), "t"))
    else
      assign_x (App (Var "tl", [Cast (PTR LST, Var y)]))
  | Cls.Tget (y, i) ->
    if config.eager then
      assign_x (Index (Arrow (Cast (PTR TPL, Var y), "fields"), i))
    else
      assign_x (App (Var "tget", [Cast (PTR TPL, Var y); Int i]))
  | Cls.Deref (y, ou) ->
    if config.monotonic then match ou with
      | None -> assign_x (Arrow (Cast (PTR REF, Var y), "v"))
      | Some u -> assign_x (App (Var "toplevel_coerce", [Arrow (Cast (PTR REF, Var y), "v"); App (Var "make_s_coercion", [Arrow (Cast (PTR REF, Var y), "u"); toC_ty u])]))
    else if config.static then
      assign_x (Deref (Cast (REF, Var y)))
    else
      assign_x (App (Var "deref", [Cast (PTR REF, Var y)]))
  | Cls.Add (y, z) -> assign_x (Add (Var y, Var z))
  | Cls.Sub (y, z) -> assign_x (Sub (Var y, Var z))
  | Cls.Mul (y, z) -> assign_x (Mul (Var y, Var z))
  | Cls.Div (y, z) -> assign_x (Div (Var y, Var z))
  | Cls.Mod (y, z) -> assign_x (Mod (Var y, Var z))
  | Cls.Cons (y, z) -> assign_x (Malloc (VALUE, Sizeof LST)) @ [SAssign (LDeref (LCast (PTR LST, LVar x)), Cast (LST, Struct ["h", Var y; "t", Var z]))]
  | Cls.Subst (y, z, ou) ->
    if config.monotonic then match ou with
      | None -> SAssign (LArrow (LCast (PTR REF, LVar y), "v"), Var z) :: assign_x (Int 0)
      | Some u -> SAssign (LArrow (LCast (PTR REF, LVar y), "v"), App (Var "coerce", [Var z; App (Var "make_s_coercion", [toC_ty u; Arrow (Cast (PTR REF, Var y), "u")])])) :: SApp (Var "consume", []) :: assign_x (Int 0)
    else if config.static then
      SAssign (LDeref (LCast (REF, LVar y)), Var z) :: assign_x (Int 0)
    else
      SApp (Var "subst", [Cast (PTR REF, Var y); Var z]) :: assign_x (Int 0)
  | Cls.CComp (y, z) -> assign_x (Cast (VALUE, App (Var "compose", [Cast (PTR CRC, Var y); Cast (PTR CRC, Var z)])))
  | Cls.AppDDir (l, (y1, y2)) ->
    assign_x (App (Var ("fun_" ^ l), [dummy_value; Var y1; Var y2]))
  | Cls.AppDCls (y, (z1, z2)) ->
    let func = Arrow (Cast (PTR FUN, Var y), "funcD") in
    assign_x (App (func, [Var y; Var z1; Var z2]))
  | Cls.AppMDir (l, y) ->
    let alt_str = if config.alt then "alt_" else "" in
    assign_x (App (Var ("fun_" ^ alt_str ^ l), [dummy_value; Var y]))
  | Cls.AppMCls (y, z) ->
    let func = Arrow (Cast (PTR FUN, Var y), "funcM") in
    assign_x (App (func, [Var y; Var z]))
  | Cls.AppTy (y, i1, tas, n) ->
    let env_size = i1 + List.length tas + n in
    let fun_x = LCast (PTR FUN, LVar x) in
    let fun_y = Cast (PTR FUN, Var y) in
    let set_func =
      let func_d = Arrow (fun_y, "funcD") in
      let func_m = Arrow (fun_y, "funcM") in
      set_func_stm ~config fun_x func_d func_m
    in
    let rec copy i n =
      if i = n then []
      else SAssign (LIndex (LArrow (fun_x, "env"), i), Index (Arrow (fun_y, "env"), i)) :: copy (i + 1) n
    in
    SAssign (LVar x, alloc_closure env_size) :: set_func @ copy 0 i1 @ app_env fun_x i1 toC_ta tas @ copy (i1 + List.length tas) env_size
  | Cls.AppTyFun (y, i1, tas, n) ->
    toC_assign ~config x (Cls.AppTy (y, i1, tas, n)) @ [SAssign (LVar x, App (Var ("tfun_" ^ y), [Var x; dummy_value]))]
  | Cls.CApp (y, z) -> assign_x (App (Var "toplevel_coerce", [Var y; Cast (PTR CRC, Var z)]))
  (* TODO: CrcManager から inj, proj を消したので、最適化処理はtoCに任せる *)
  | Cls.Cast (y, u1, u2, (r, p)) -> assign_x (App (Var "cast", [Var y; toC_ty u1; toC_ty u2; Int (rid r); Int (int_of_pos p)]))
  | Cls.Let (y, f1, f2) -> SDecl (VALUE, y, None) :: toC_assign ~config y f1 @ toC_assign ~config x f2
  | Cls.IfEq (y, z, f1, f2) ->
    SIf (Eq (Var y, Var z), toC_assign ~config x f1, toC_assign ~config x f2) :: []
  | Cls.IfLte (y, z, f1, f2) ->
    SIf (Lte (Var y, Var z), toC_assign ~config x f1, toC_assign ~config x f2) :: []
  | Cls.MakeCls (y, cls, f) ->
    let set_func fun_y =
      let alt_str = if config.alt then "alt_" else "" in
      let func_d = Var ("fun_" ^ cls.entry) in
      let func_m = Var ("fun_" ^ alt_str ^ cls.entry) in
      set_func_stm ~config fun_y func_d func_m
    in
    make_cls_stm ~set_func y cls @ toC_assign ~config x f
  | Cls.MakeTyCls (y, cls, f) ->
    let set_func fun_y = [SAssign (LArrow (fun_y, "funcM"), Var ("tfun_" ^ cls.entry))] in
    make_cls_stm ~set_func y cls @ toC_assign ~config x f
  | Cls.SetTy ((i, { contents = opu }), f) ->
    let name, stm = set_ty i opu in
    SDecl (PTR TY, name, Some (Malloc (PTR TY, Sizeof TY))) :: stm @ toC_assign ~config x f
  | Cls.Match (y, ms) ->
    List.fold_left (fun stm (mf, f) -> [SIf (toC_mf ~config (Var y) mf, toC_assign ~config x f, stm)])
      [SApp (Var "printf", [Str "didn't match"]); SApp (Var "exit", [Int 1])] (List.rev ms)

(* ======================================= *)

let toC_tydecls tys = List.map (fun (_, name) -> Decl (Static, TY, name, None)) tys

let toC_tycontents tys = List.map (fun (u, name) -> Decl (Static, TY, name, Some (toC_tycontent u))) tys

let toC_tys tys = toC_tydecls tys, toC_tycontents tys

(* ================================ *)

let toC_ranges ranges =
  let toC_contents (r, _) =
    Struct [
      "filename", Str (if r.start_p.pos_fname <> "" then "File \\\"" ^ r.start_p.pos_fname ^ "\\\", " else "");
      "startline", Int r.start_p.pos_lnum;
      "startchr", Int (r.start_p.pos_cnum - r.start_p.pos_bol);
      "endline", Int r.end_p.pos_lnum;
      "endchr", Int (r.end_p.pos_cnum - r.end_p.pos_bol)
    ]
  in
  if List.length ranges = 0 then []
  else [Decl (Static, RANGE, "local_range_list[]", Some (Array (List.map (fun r -> toC_contents r) (List.sort (fun (_, i1) (_, i2) -> compare i1 i2) ranges))))]

(* ================================ *)

let toC_crcdecls crcs = List.map (fun (_, name) -> Decl (Static, CRC, name, None)) crcs

let toC_crccontents crcs = List.map (fun (c, name) -> Decl (Static, CRC, name, Some (snd @@ toC_crc name c))) crcs

let toC_crcs ~config crcs = 
  let register = 
    List.map (fun str -> SApp (Var "register_static_crc", [Addr str]))
      (["crc_id"; "crc_inj_INT"; "crc_inj_BOOL"; "crc_inj_UNIT"; "crc_inj_AR"; "crc_inj_LI"; "crc_inj_RF"]
      @ (List.map snd crcs))
  in
  let crcinit =
    if config.hash then
      [FunDef (Static, { ret_ty = VOID; fname = "init_crcs"; params = [] }, register)]
    else []
  in
  toC_crcdecls crcs, toC_crccontents crcs, crcinit

(* ================================ *)

let pick_env x fvs ftvs =
  let pick_x t i = Cast (t, Index (Arrow (Cast (PTR FUN, Var x), "env"), i)) in
  List.mapi (fun i fv -> SDecl (VALUE, fv, Some (pick_x VALUE i))) fvs @
    List.mapi (fun i ftv -> SDecl (PTR TY, string_of_tyvar ftv, Some (pick_x (PTR TY) (i + List.length fvs)))) ftvs

let toC_fundef ~config fundef =
  let name, fname, params, vs, tvs, body = match fundef with
    | Cls.FundefD { name; arg = (y, k); vs; tvs; body } ->
      name, "fun_" ^ name, [name; y; k], vs, tvs, body
    | Cls.FundefM { name; arg = y; vs; tvs; body } ->
      let alt_str = if config.alt then "alt_" else "" in
      name, "fun_" ^ alt_str ^ name, [name; y], vs, tvs, body
    | Cls.FundefTy { name; vs; tvs; body } ->
      name, "tfun_" ^ name, [name; "dummy"], vs, tvs, body
  in
  let f_s = { ret_ty = VALUE; fname; params = List.map (fun x -> (VALUE, x)) params } in
  let fvs_ftvs = pick_env name vs tvs in
  let body = toC_exp ~is_main:false ~config body in
  FunDecl (Static, f_s), FunDef (Static, f_s, fvs_ftvs @ body)

let toC_toplevel ~config toplevel =
  List.split @@ List.map (fun fd -> toC_fundef ~config fd) toplevel

(* ================================ *)

let toC_program ?(bench=0) ~config (Cls.Prog (toplevel, f)) =
  let tys = TyManager.get_definitions () in
  let ranges = RangeManager.get_definitions () in
  let crcs = CrcManager.get_definitions () in
  let inc = [
    Include "<gc.h>";
    Include (
      if bench = 0 then Format.asprintf "\"%s/runtime.h\"" (Resources.libc_dir ())
      else "\"../../../libC/runtime.h\""
    );
  ]
  in
  let tydecl, tydef = toC_tys tys in
  let rangedef = toC_ranges ranges in
  let crcdecl, crcdef, crcinit = toC_crcs ~config crcs in
  let fundecl, fundef = toC_toplevel ~config toplevel in
  let decl = if bench = 0 && not config.static then [Decl (No, PTR RANGE, "range_list", None)] else [] in
  let main = [
    FunDef (
      No,
      { ret_ty = INT; fname = if bench = 0 then "main" else "mutant" ^ string_of_int bench; params = []},
      (if config.hash then [SApp (Var "init_crcs", [])] else [])
        @ (if config.monotonic then [SApp (Var "sc_init", [Int 16])] else [])
        @ (if List.length ranges <> 0 then [SAssign (LVar "range_list", Var "local_range_list")] else [])
        @ toC_exp ~is_main:true ~config f
    )
  ]
  in
  inc @ tydecl @ tydef @ rangedef @ crcdecl @ crcdef @ crcinit @ fundecl @ fundef @ decl @ main

(* 
  fprintf ppf "%s\n%s\n%a%a%a%a%s%s%s%a%s"
    (if bench = 0 then "#define GC_INITIAL_HEAP_SIZE 1048576\n" else "")
    ...
    (if bench = 0 then asprintf "int main() {\nGC_INIT();\n%s" init_crcs else asprintf "int mutant%d() {\n%s" bench init_crcs)
    ...
*)

(* 

(* ======================================== *)

let rec toC_exp ppf f ~config ~is_main = 
  let toC_exp = toC_exp ~config ~is_main in
  match f with
  | Insert (x, f) -> begin match f with
    | Ref (y, u) ->
      let c = c_of_ty u in
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(ref));\n((ref*)%s)->v = %s;\n((ref*)%s)->u = %s;\n"
        x x y x c
    | Deref (y, None) -> fprintf ppf "%s = ((ref*)%s)->v;\n" x y
    | Subst (y, z, None) -> fprintf ppf "((ref*)%s)->v = %s;\n%s = 0;\n" y z x
    | Deref _ | Subst _ -> raise @@ ToC_bug "yet"
    | CApp (y, z) -> (* TODO *)
      if CrcManager.mem_inj z then
        let tag = CrcManager.find_inj z in
        fprintf ppf "#ifdef PROFILE\ncurrent_cast++;\n#endif\n%s = (%s << 3) | G_%a;\n"
          x
          y
          toC_tag tag
      else if CrcManager.mem_proj z then
        let (tag, rid, p) = CrcManager.find_proj z in
        fprintf ppf "#ifdef PROFILE\ncurrent_cast++;\n#endif\nif ((uint8_t)(%s & 0b111) == G_%a) {\n%s = %s >> 3;\n} else {\nblame(%d, %d);\n}"
          y
          toC_tag tag
          x
          y
          rid
          (match p with Pos -> 1 | Neg -> 0)
      else
        fprintf ppf "%s = coerce(%s, (crc*)%s);\n"
          x
          y
          z
    (*以下は内部にexpがあるので，後者のexpまでinsertを送る
      letはf2のみに，ifはf1,f2の両方にinsertを送る*)
    end
  (*以下は項の中にexpを含まないので，main関数かどうかを判定してreturn文を変える必要がある．
    main関数ならreturn 0;でプログラムを終える．main関数でなければ，その値自体をreturnする．*)
  | Tuple _ | Tget _ | Ref _ | Deref _ | Subst _ as f ->
    fprintf ppf "value retv;\n%areturn %s;\n"
      toC_exp (Insert ("retv", f))
      (if is_main then "0" else "retv")
*)