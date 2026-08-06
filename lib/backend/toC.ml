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
  | Ar -> "AR"

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
  | TyArray TyDyn -> Addr "tyar"
  | TyArray _ as u -> Addr (TyManager.find u)
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
  | TyVar (i, { contents = Some (TyArray _) }) -> Var (Format.asprintf "_tyarray%d" i)
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
    Struct ["tykind", Var "TYTUPLE"; "tydat", Struct ["tytuple", Struct ["size", Int (List.length us); "tys", Cast (ARRAY (PTR TY), Array (List.map (fun u -> toC_ty u) us))]]] 
  | TyRef u -> Struct ["tykind", Var "TYREF"; "tydat", Struct ["tyref", toC_ty u]]
  | TyArray u -> Struct ["tykind", Var "TYARRAY"; "tydat", Struct ["tyarray", toC_ty u]]
  | _ as u -> raise @@ ToC_bug (Format.asprintf "toC_content yet: %a" Pp.pp_ty u)

(* ========================================= *)

let int_of_pos = function Pos -> 1 | Neg -> 0

let rid r = 
  try
    int_of_string @@ RangeManager.find r
  with
    Not_found -> raise @@ ToC_bug "rid cannot find r"

let rec has_tv_ty = function
  | TyVar _ -> true
  | TyFun (u1, u2) -> has_tv_ty u1 || has_tv_ty u2
  | TyList u' | TyRef u' | TyArray u' -> has_tv_ty u'
  | TyTuple us -> List.exists has_tv_ty us
  | _ -> false

let rec check_has_tv = function
  | CId _ | CInj _ | CProj _ | CFail _ -> false
  | CList c' -> check_has_tv c'
  | CTvInj _ | CTvProj _ | CTvProjInj _ -> true
  | CSeq (c1, c2) | CFun (c1, c2) | CRef (c1, c2) | CArray (c1, c2) -> (check_has_tv c1) || (check_has_tv c2)
  | CTuple cs -> List.fold_left (fun b c -> b || check_has_tv c) false cs
  | CMRef (u1, u2) | CMArray (u1, u2) -> has_tv_ty u1 || has_tv_ty u2

let rec toC_crc x c =
  let stm_crc x c = match c with
    | CId _ -> [], Addr "crc_id"
    | CSeq (CId _, CInj (I | B | U | Fn | Li | Rf | Ar as g)) -> [], Addr ("crc_inj_" ^ string_of_tag g)
    | CSeq (CMRef (_, TyDyn), CInj Rf) -> [], Addr ("crc_inj_RF")
    | CSeq (CMArray (_, TyDyn), CInj Ar) -> [], Addr ("crc_inj_AR")
    | _ ->
      if CrcManager.mem c then [], Addr (CrcManager.find c)
      else
        let stm, exp = toC_crc x c in
        SDecl (VALUE, x, None) :: stm @ [SDecl (CRC, x ^ "_tmp" , Some exp); SAssign (Var x, Cast (VALUE, App (Var "alloc_crc", [Addr (x ^ "_tmp")])))], Cast (PTR CRC, Var x)
  in
  let has_tv_val = if check_has_tv c then 1 else 0 in
  let c, info_proj_inj = match c with
    | CSeq (CProj (_, (r, p)), (CSeq (c, CInj _))) -> c, ["has_proj", Int 1; "has_inj", Int 1; "p_proj", Int (int_of_pos p); "rid_proj", Int (rid r)]
    | CSeq (CProj (_, (r, p)), c) -> c, ["has_proj", Int 1; "p_proj", Int (int_of_pos p); "rid_proj", Int (rid r)]
    | CSeq (c, CInj _) -> c, ["has_inj", Int 1]
    | CTvProjInj (_, (r, p), _) as c -> c, ["has_proj", Int 1; "has_inj", Int 1; "p_proj", Int (int_of_pos p); "rid_proj", Int (rid r)]
    | CTvProj (_, (r, p)) as c -> c, ["has_proj", Int 1; "p_proj", Int (int_of_pos p); "rid_proj", Int (rid r)]
    | CTvInj _ as c -> c, ["has_inj", Int 1]
    | c -> c, []
  in
  match c with
    | CId u ->
      let g, size = match u with
        | TyInt -> "G_INT", 0 | TyBool -> "G_BOOL", 0 | TyUnit -> "G_UNIT", 0 | TyFun _ -> "G_FN", 0
        | TyList _ -> "G_LI", 0 | TyTuple us -> "G_TP", List.length us | TyRef _ -> "G_RF", 0 | TyArray _ -> "G_AR", 0
        | TyDyn | TyVar _ | TyCoercion _ -> raise @@ ToC_bug "Seq CId shouldn't have tydyn, tyvar, tycoercion"
      in
      [],
      Struct (
        ("crckind", Var "C_ID") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["id", Struct ["g", Var g; "size", Int size]]
        ]
      )
    | CFun (c1, c2) ->
      let stm1, ptr_crc1 = stm_crc (x ^ "_fun1") c1 in
      let stm2, ptr_crc2 = stm_crc (x ^ "_fun2") c2 in
      stm1 @ stm2,
      Struct (
        ("crckind", Var "C_FUN") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["fun_crc", Struct ["c1", ptr_crc1; "c2", ptr_crc2]]
        ]
      )
    | CList c ->
      let stm, ptr_crc = stm_crc (x ^ "_list") c in
      stm,
      Struct (
        ("crckind", Var "C_LIST") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["lst_crc", ptr_crc]
        ]
      )
    | CTuple cs ->
      let stms, ptr_crcs = List.split @@ List.mapi (fun i c -> stm_crc (x ^ "_elm" ^ string_of_int i) c) cs in
      List.flatten stms,
      Struct (
        ("crckind", Var "C_TUPLE") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["tpl_crc", Struct ["size", Int (List.length cs); "crcs", Cast (ARRAY (PTR CRC), Array ptr_crcs)]]
        ]
      )
    | CRef (c1, c2) ->
      let stm1, ptr_crc1 = stm_crc (x ^ "_ref1") c1 in
      let stm2, ptr_crc2 = stm_crc (x ^ "_ref2") c2 in
      stm1 @ stm2,
      Struct (
        ("crckind", Var "C_REF") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["ref_crc", Struct ["c1", ptr_crc1; "c2", ptr_crc2]]
        ]
      )
    | CMRef (_, u) ->
      [],
      Struct (
        ("crckind", Var "C_REF") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["mref_crc", toC_ty u]
        ]
      )
    | CArray (c1, c2) ->
      let stm1, ptr_crc1 = stm_crc (x ^ "_array1") c1 in
      let stm2, ptr_crc2 = stm_crc (x ^ "_array2") c2 in
      stm1 @ stm2,
      Struct (
        ("crckind", Var "C_ARRAY") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["array_crc", Struct ["c1", ptr_crc1; "c2", ptr_crc2]]
        ]
      )
    | CMArray (_, u) ->
      [],
      Struct (
        ("crckind", Var "C_ARRAY") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["marray_crc", toC_ty u]
        ]
      )
    | CTvInj (tv, (r, p)) ->
      [],
      Struct (
        ("crckind", Var "C_TV") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["tv", Struct ["rid_inj", Int (rid r); "p_inj", Int (int_of_pos p); "tv_ptr", toC_ty (TyVar tv)]]
        ]
      )
    | CTvProj (tv, _) ->
      [],
      Struct (
        ("crckind", Var "C_TV") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["tv", Struct ["tv_ptr", toC_ty (TyVar tv)]]
        ]
      )
    | CTvProjInj (tv, _, (r, p)) ->
      [],
      Struct (
        ("crckind", Var "C_TV") :: info_proj_inj @ [
          "has_tv", Int has_tv_val;
          "crcdat", Struct ["tv", Struct ["rid_inj", Int (rid r); "p_inj", Int (int_of_pos p); "tv_ptr", toC_ty (TyVar tv)]]
        ]
      )
    | CSeq _ | CProj _ | CInj _ as c -> raise @@ ToC_bug (Format.asprintf "%a should not be passed to toC_crc" Pp.pp_coercion c)
    | CFail _ as c -> raise @@ ToC_bug (Format.asprintf "toC_crc yet: %a" Pp.pp_coercion c)


(* ========================================= *)

let app_env l n f lst =
  let lval_env = Arrow (l, "env") in
  List.mapi (fun i h -> SAssign (Index (lval_env, Int (n + i)), Cast (PTR VOID, f h))) lst

let alloc_closure env_size =
  Malloc (VALUE, BinOp (Sizeof FUN, Plus, BinOp (Sizeof (PTR VOID), Mult, Int env_size)))

let set_func_stm ~config fun_x func_d func_m =
  if config.intoB || config.static then
    [SAssign (Arrow (fun_x, "funcM"), func_m)]
  else if config.alt then
    [SAssign (Arrow (fun_x, "funcD"), func_d);
     SAssign (Arrow (fun_x, "funcM"), func_m)]
  else
    [SAssign (Arrow (fun_x, "funcD"), func_d)]

let make_cls_stm ~set_func x ({ entry = _; fvs; offset = n; ftvs }: Cls.closure) =
  let env_size = List.length fvs + n + List.length ftvs in
  let fun_x = Cast (PTR FUN, Var x) in
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
    | Some (TyArray _ as u) ->
      u, "_tyarray" ^ string_of_int i
    | Some u -> raise @@ ToC_bug (Format.asprintf "set_ty yet: %a" Pp.pp_ty u)
  in
  name, [SAssign (PreOp (Deref, (Var name)), Cast (TY, toC_tycontent u))]
    (* 
    | Some _ -> raise @@ ToC_bug "not tyfun or tylist is in tyvar option"
    end *)

let rec toC_mf ~config x_exp = function
  | MatchVar _ | MatchBLit _ | MatchULit -> raise @@ ToC_bug "MatchVar, MatchBLit, MatchULit should not appear in toC"
  | MatchILit i -> BinOp (x_exp, Eq, Int i)
  | MatchWild -> Int 1
  | MatchNil ->
    if config.eager then
      BinOp (Cast (PTR LST, x_exp), Eq, Null)
    else
      App (Var "is_NULL", [Cast (PTR LST, x_exp)])
  | MatchCons (mf1, mf2) ->
    if config.eager then
      let mf1 = toC_mf ~config (Arrow (Cast (PTR LST, x_exp), "h")) mf1 in
      let mf2 = toC_mf ~config (Arrow (Cast (PTR LST, x_exp), "t")) mf2 in
      BinOp (BinOp (Cast (PTR LST, x_exp), Neq, Null), And, BinOp (mf1, And, mf2))
    else
      let mf1 = toC_mf ~config (App (Var "hd", [Cast (PTR LST, x_exp)])) mf1 in
      let mf2 = toC_mf ~config (App (Var "tl", [Cast (PTR LST, x_exp)])) mf2 in
      BinOp (PreOp (Not, (App (Var "is_NULL", [Cast (PTR LST, x_exp)]))), And, BinOp (mf1, And, mf2))
  | MatchTuple mfs ->
    let toC_mfi mf i =
      if config.eager then
        toC_mf ~config (Index (Arrow (Cast (PTR TPL, x_exp), "fields"), Int i)) mf
      else
        toC_mf ~config (App (Var "tget", [Cast (PTR TPL, x_exp); Int i])) mf
    in
    List.fold_left (fun e1 e2 -> BinOp (e1, And, e2)) (Int 1) (List.mapi (fun i mf -> toC_mfi mf i) mfs)
  (* | _ as mf -> ignore config; raise @@ ToC_bug (Format.asprintf "toC_mf yet: %a" Pp.pp_matchform mf) *)

let rec toC_exp ~is_main ~config = function
  | Cls.Let (x, f1, f2) ->
    SDecl (VALUE, x, None) :: toC_assign ~config x f1 @ toC_exp ~is_main ~config f2
  | Cls.If (x, f1, f2) ->
    SIf (Var x, toC_exp ~is_main ~config f1, toC_exp ~is_main ~config f2) :: []
  | Cls.MakeCls (x, cls, f) ->
    let set_func fun_x =
      let alt_str = if config.alt then "alt_" else "" in
      let func_d = Var ("fun_" ^ cls.entry) in
      let func_m = Var ("fun_" ^ alt_str ^ cls.entry) in
      set_func_stm ~config fun_x func_d func_m
    in
    make_cls_stm ~set_func x cls @ toC_exp ~is_main ~config f
  | Cls.MakeTyCls (x, cls, f) ->
    let set_func fun_x = [SAssign (Arrow (fun_x, "funcM"), Var ("tfun_" ^ cls.entry))] in
    make_cls_stm ~set_func x cls @ toC_exp ~is_main ~config f
  | Cls.SetTy ((i, { contents = opu }), f) ->
    let name, stm = set_ty i opu in
    SDecl (PTR TY, name, Some (Malloc (PTR TY, Sizeof TY))) :: stm @ toC_exp ~is_main ~config f
  | Cls.Match (x, ms) ->
    List.fold_left (fun stm (mf, f) -> [SIf (toC_mf ~config (Var x) mf, toC_exp ~is_main ~config f, stm)])
      [SExp (App (Var "printf", [Str "didn't match"])); SExp (App (Var "exit", [Int 1]))] (List.rev ms)
  | Cls.Var _ | Cls.Int _ | Cls.Coercion _ | Cls.Nil | Cls.Tuple _ | Cls.Ref _ | Cls.MakeArray _
  | Cls.Hd _ | Cls.Tl _ | Cls.Tget _ | Cls.Deref _ | Cls.Get _
  | Cls.BinOp _ | Cls.Cons _ | Cls.Subst _ | Cls.Put _ | Cls.CComp _
  | Cls.AppDDir _ | Cls.AppDCls _  | Cls.AppMDir _ | Cls.AppMCls _ | Cls.AppTy _ | Cls.AppTyFun _ | Cls.CApp _ | Cls.Cast _
    as f ->
    let return = SReturn (if is_main then Int 0 else Var "retv") in
    SDecl (VALUE, "retv", None) :: toC_assign ~config "retv" f @ [return]
and toC_assign ~config x f =
  let assign_x e = SAssign (Var x, e) :: [] in
  match f with
  | Cls.Var y -> assign_x (Var y)
  | Cls.Int i -> assign_x (Int i)
  | Cls.Nil -> assign_x dummy_value
  | Cls.Tuple ys ->
    let size = List.length ys in
    assign_x (Malloc (VALUE, BinOp (Sizeof TPL_RAW, Plus, BinOp (Sizeof VALUE, Mult, Int size)))) @ [SAssign (Dot (Arrow (Cast (PTR TPL_RAW, Var x), "hdr"), "size"), Int size)]
    @ List.mapi (fun i y -> SAssign (Index (Arrow (Cast (PTR TPL_RAW, Var x), "fields"), Int i), Var y)) ys
  | Cls.Ref (y, u) ->
    assign_x (Malloc (VALUE, Sizeof REF)) @ 
    if config.monotonic then
      [SAssign (PreOp (Deref, (Cast (PTR REF, Var x))), Cast (REF, Struct ["v", Var y; "u", toC_ty u]))]
    else if config.static then
      [SAssign (PreOp (Deref, (Cast (REF, Var x))), Var y)]
    else
      [SAssign (Arrow (Cast (PTR REF, Var x), "v"), Var y)]
  | Cls.MakeArray (y, z, u) ->
    assign_x (Malloc (VALUE, BinOp (Sizeof ARR_RAW, Plus, BinOp (Sizeof VALUE, Mult, Var y)))) @ [SAssign (Arrow (Cast (PTR ARR_RAW, Var x), "length"), Var y)] @
    [SFor ((SDecl (INT, "i", Some (Int 0)), BinOp (Var "i", Lt, Var y), PostOp (Var "i", Incr)),
      [SAssign (Index (Arrow (Cast (PTR ARR_RAW, Var x), "vs"), Var "i"), Var z)])]
    @
    if config.monotonic then
      [SAssign (Arrow (Cast (PTR ARR_RAW, Var x), "u"), toC_ty u)]
    else 
      []
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
      assign_x (Index (Arrow (Cast (PTR TPL, Var y), "fields"), Int i))
    else
      assign_x (App (Var "tget", [Cast (PTR TPL, Var y); Int i]))
  | Cls.Deref (y, ou) ->
    if config.monotonic then match ou with
      | None -> assign_x (Arrow (Cast (PTR REF, Var y), "v"))
      | Some u -> assign_x (App (Var "toplevel_coerce", [Arrow (Cast (PTR REF, Var y), "v"); App (Var "make_s_coercion", [Arrow (Cast (PTR REF, Var y), "u"); toC_ty u])]))
    else if config.static then
      assign_x (PreOp (Deref, (Cast (REF, Var y))))
    else
      assign_x (App (Var "deref", [Cast (PTR REF, Var y)]))
  | Cls.Get (y, z, ou) ->
    if config.monotonic then match ou with
      | None -> assign_x (Index (Arrow (Cast (PTR ARR, Var y), "vs"), Var z))
      | Some u -> assign_x (App (Var "toplevel_coerce", [Index (Arrow (Cast (PTR ARR, Var y), "vs"), Var z); App (Var "make_s_coercion", [Arrow (Cast (PTR ARR, Var y), "u"); toC_ty u])]))
    else if config.static then
      assign_x (Index (Arrow (Cast (PTR ARR, Var y), "vs"), Var z))
    else
      assign_x (App (Var "get", [Cast (PTR ARR, Var y); Cast (INT, Var z)]))
  | Cls.BinOp (y, op, z) -> assign_x (BinOp (Var y, op, Var z))
  | Cls.Cons (y, z) -> assign_x (Malloc (VALUE, Sizeof LST)) @ [SAssign (PreOp (Deref, (Cast (PTR LST, Var x))), Cast (LST, Struct ["h", Var y; "t", Var z]))]
  | Cls.Subst (y, z, ou) ->
    if config.monotonic then match ou with
      | None -> SAssign (Arrow (Cast (PTR REF, Var y), "v"), Var z) :: assign_x (Int 0)
      | Some u -> SAssign (Arrow (Cast (PTR REF, Var y), "v"), App (Var "coerce", [Var z; App (Var "make_s_coercion", [toC_ty u; Arrow (Cast (PTR REF, Var y), "u")])])) :: SExp (App (Var "consume", [])) :: assign_x (Int 0)
    else if config.static then
      SAssign (PreOp (Deref, (Cast (REF, Var y))), Var z) :: assign_x (Int 0)
    else
      SExp (App (Var "subst", [Cast (PTR REF, Var y); Var z])) :: assign_x (Int 0)
  | Cls.Put (y, z, v_x, ou) ->
    if config.monotonic then match ou with
      | None -> SAssign (Index (Arrow (Cast (PTR ARR, Var y), "vs"), Var z), Var v_x) :: assign_x (Int 0)
      | Some u -> SAssign (Index (Arrow (Cast (PTR ARR, Var y), "vs"), Var z), App (Var "coerce", [Var v_x; App (Var "make_s_coercion", [toC_ty u; Arrow (Cast (PTR ARR, Var y), "u")])])) :: SExp (App (Var "consume", [])) :: assign_x (Int 0)
    else if config.static then
      SAssign (Index (Arrow (Cast (PTR ARR, Var y), "vs"), Var z), Var v_x) :: assign_x (Int 0)
    else
      SExp (App (Var "put", [Cast (PTR ARR, Var y); Cast (INT, Var z); Var v_x])) :: assign_x (Int 0)
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
    let fun_x = Cast (PTR FUN, Var x) in
    let fun_y = Cast (PTR FUN, Var y) in
    let set_func =
      let func_d = Arrow (fun_y, "funcD") in
      let func_m = Arrow (fun_y, "funcM") in
      set_func_stm ~config fun_x func_d func_m
    in
    let rec copy i n =
      if i = n then []
      else SAssign (Index (Arrow (fun_x, "env"), Int i), Index (Arrow (fun_y, "env"), Int i)) :: copy (i + 1) n
    in
    SAssign (Var x, alloc_closure env_size) :: set_func @ copy 0 i1 @ app_env fun_x i1 toC_ta tas @ copy (i1 + List.length tas) env_size
  | Cls.AppTyFun (y, i1, tas, n) ->
    toC_assign ~config x (Cls.AppTy (y, i1, tas, n)) @ [SAssign (Var x, App (Var ("tfun_" ^ y), [Var x; dummy_value]))]
  | Cls.CApp (y, z) -> assign_x (App (Var "toplevel_coerce", [Var y; Cast (PTR CRC, Var z)]))
  (* TODO: CrcManager から inj, proj を消したので、最適化処理はtoCに任せる *)
  | Cls.Cast (y, u1, u2, (r, p)) -> assign_x (App (Var "cast", [Var y; toC_ty u1; toC_ty u2; Int (rid r); Int (int_of_pos p)]))
  | Cls.Let (y, f1, f2) -> SDecl (VALUE, y, None) :: toC_assign ~config y f1 @ toC_assign ~config x f2
  | Cls.If (y, f1, f2) ->
    SIf (Var y, toC_assign ~config x f1, toC_assign ~config x f2) :: []
  | Cls.MakeCls (y, cls, f) ->
    let set_func fun_y =
      let alt_str = if config.alt then "alt_" else "" in
      let func_d = Var ("fun_" ^ cls.entry) in
      let func_m = Var ("fun_" ^ alt_str ^ cls.entry) in
      set_func_stm ~config fun_y func_d func_m
    in
    make_cls_stm ~set_func y cls @ toC_assign ~config x f
  | Cls.MakeTyCls (y, cls, f) ->
    let set_func fun_y = [SAssign (Arrow (fun_y, "funcM"), Var ("tfun_" ^ cls.entry))] in
    make_cls_stm ~set_func y cls @ toC_assign ~config x f
  | Cls.SetTy ((i, { contents = opu }), f) ->
    let name, stm = set_ty i opu in
    SDecl (PTR TY, name, Some (Malloc (PTR TY, Sizeof TY))) :: stm @ toC_assign ~config x f
  | Cls.Match (y, ms) ->
    List.fold_left (fun stm (mf, f) -> [SIf (toC_mf ~config (Var y) mf, toC_assign ~config x f, stm)])
      [SExp (App (Var "printf", [Str "didn't match"])); SExp (App (Var "exit", [Int 1]))] (List.rev ms)

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
    List.map (fun str -> SExp (App (Var "register_static_crc", [Addr str])))
      (["crc_id"; "crc_inj_INT"; "crc_inj_BOOL"; "crc_inj_UNIT"; "crc_inj_FN"; "crc_inj_LI"; "crc_inj_RF"; "crc_inj_AR"]
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
  let pick_x t i = Cast (t, Index (Arrow (Cast (PTR FUN, Var x), "env"), Int i)) in
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
      (if config.hash then [SExp (App (Var "init_crcs", []))] else [])
        @ (if config.monotonic then [SExp (App (Var "sc_init", [Int 16]))] else [])
        @ (if List.length ranges <> 0 then [SAssign (Var "range_list", Var "local_range_list")] else [])
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
*)