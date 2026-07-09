open Syntax
open Syntax.C
open Config
open Utils.Error
open Static_manage
(* open Fv.Cls *)

exception ToC_bug of string
exception ToC_error of string

let string_of_tag = function
  | I -> "INT"
  | B -> "BOOL"
  | U -> "UNIT"
  | Ar -> "AR"
  | Li -> "LI"
  | Tp _ -> "TP"
  | Rf -> "RF"

let string_of_tyvar (i, _) = "_ty" ^ string_of_int i

let toC_ty = function
  | TyInt -> Addr "tyint"
  | TyBool -> Addr "tybool"
  | TyUnit -> Addr "tyunit"
  | TyDyn -> Addr "tydyn"
  | TyFun (TyDyn, TyDyn) -> Addr "tyar"
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

(* ========================================= *)

let int_of_pos = function Pos -> 1 | Neg -> 0

let rid r = int_of_string @@ RangeManager.find r

let rec check_has_tv = function
  | CId _ | CInj _ | CProj _ -> false
  | CList c' -> check_has_tv c'
  | CTvInj _ | CTvProj _ | CTvProjInj _ -> true
  | CSeq (c1, c2) | CFun (c1, c2) | CRef (c1, c2) -> (check_has_tv c1) || (check_has_tv c2)
  | CTuple cs -> List.fold_left (fun b c -> b || check_has_tv c) false cs
  | CMRef _ | CFail _ as c -> raise @@ ToC_bug (Format.asprintf "check_has_tv yet: %a" Pp.pp_coercion c)

let rec toC_crc x c =
  let stm_crc x c = match c with
    | CId _ -> [], Addr "crc_id"
    | CSeq (CId _, CInj (I | B | U | Ar | Li | Rf as g)) -> [], Addr ("crc_inj_" ^ string_of_tag g)
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
      | _ as c -> raise @@ ToC_bug (Format.asprintf "toC_crc yet: %a" Pp.pp_coercion c)

  (*
  ...
  | CList c ->
    fprintf ppf "value %s_c;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = LIST;\n%s_temp.has_tv = ((crc*)%s_c)->has_tv;\n%s_temp.crcdat.lst_crc = (crc*)%s_c;\n%s = (value)alloc_crc(&%s_temp);" 
      x toC_crc (c, x ^ "_c") x x x x x x x x
  | CTuple cs ->
    let arity = List.length cs in
    let toC_sep ppf () = fprintf ppf "\n" in
    let counter = ref 0 in
    let toC_elem ppf c = 
      let i = !counter in
      counter := !counter + 1;
      fprintf ppf "value %s_c%d;\n%a\n%s_crcs[%d] = (crc*)%s_c%d;" x i toC_crc (c, Printf.sprintf "%s_c%d" x i) x i x i
    in
    fprintf ppf "crc **%s_crcs = (crc**)GC_MALLOC(sizeof(crc*) * %d);\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = TUPLE;\n%s_temp.has_tv = 0;\n"
      x arity (pp_print_list toC_elem ~pp_sep:toC_sep) cs x x x;
    for i = 0 to arity - 1 do
       fprintf ppf "%s_temp.has_tv |= ((crc*)%s_c%d)->has_tv;\n" x x i
    done;
    fprintf ppf "%s_temp.crcdat.tpl_crc.arity = %d;\n%s_temp.crcdat.tpl_crc.crcs = %s_crcs;\n%s = (value)alloc_crc(&%s_temp);" x arity x x x x
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

let set_ty i opu = match opu with
  | None ->
    let name = "_ty" ^ string_of_int i in
    name,
    [SAssign (LArrow (LVar name, "tykind"), Var "TYVAR")]
  | Some (TyFun (u1, u2)) ->
    let name = "_tyfun" ^ string_of_int i in
    name,
    [
      SAssign (LArrow (LVar name, "tykind"), Var "TYFUN");
      SAssign (LDot (LDot (LArrow (LVar name, "tydat"), "tyfun"), "left"), Malloc (PTR TY, Sizeof TY));
      SAssign (LDot (LDot (LArrow (LVar name, "tydat"), "tyfun"), "right"), Malloc (PTR TY, Sizeof TY));
      SAssign (LDot (LDot (LArrow (LVar name, "tydat"), "tyfun"), "left"), toC_ty u1);
      SAssign (LDot (LDot (LArrow (LVar name, "tydat"), "tyfun"), "right"), toC_ty u2);
    ]
  | Some u -> raise @@ ToC_bug (Format.asprintf "set_ty yet: %a" Pp.pp_ty u)
    (* 
    | Some (TyList u) -> 
      fprintf ppf "ty *_tylist%d = (ty*)GC_MALLOC(sizeof(ty));\n_tylist%d->tykind = TYLIST;\n_tylist%d->tydat.tylist = (ty*)GC_MALLOC(sizeof(ty));\n_tylist%d->tydat.tylist = %s;\n%a"
        i
        i
        i
        i
        (c_of_ty u)
        toC_exp f
    | Some _ -> raise @@ ToC_bug "not tyfun or tylist is in tyvar option"
    end *)

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
  | SetTy ((i, { contents = opu }), f) ->
    let name, stm = set_ty i opu in
    SDecl (PTR TY, name, Some (Malloc (PTR TY, Sizeof TY))) :: stm @ toC_exp ~is_main ~config f
  | Cls.Var _ | Cls.Int _ | Cls.Coercion _ | Cls.Add _ | Cls.Sub _ | Cls.Mul _ | Cls.Div _ | Cls.Mod _ | Cls.CComp _
  | Cls.AppDDir _ | Cls.AppDCls _  | Cls.AppMDir _ | Cls.AppMCls _ | Cls.AppTy _ | Cls.AppTyFun _ | Cls.CApp _ | Cls.Cast _ as f ->
    let return = SReturn (if is_main then Int 0 else Var "retv") in
    SDecl (VALUE, "retv", None) :: toC_assign ~config "retv" f @ [return]
  | _ as f -> raise @@ ToC_bug (Format.asprintf "toC_exp yet: %a" Pp.Cls.pp_exp f)
and toC_assign ~config x f =
  let assign_x e = SAssign (LVar x, e) :: [] in
  match f with
  | Cls.Var y -> assign_x (Var y)
  | Cls.Int i -> assign_x (Int i)
  | Cls.Coercion c -> begin match c with
    | CId _ -> assign_x (Cast (VALUE, Addr "crc_id"))
    | CSeq (CId _, CInj (I | B | U | Ar | Li | Rf as g)) -> assign_x (Cast (VALUE, Addr ("crc_inj_" ^ string_of_tag g)))
    | _ ->
      if CrcManager.mem c then assign_x (Cast (VALUE, Addr (CrcManager.find c)))
      else
        let stm, exp = toC_crc x c in
        stm @ [SDecl (CRC, x ^ "_tmp" , Some exp)] @ assign_x (Cast (VALUE, App (Var "alloc_crc", [Addr (x ^ "_tmp")])))
    end
  | Cls.Add (y, z) -> assign_x (Add (Var y, Var z))
  | Cls.Sub (y, z) -> assign_x (Sub (Var y, Var z))
  | Cls.Mul (y, z) -> assign_x (Mul (Var y, Var z))
  | Cls.Div (y, z) -> assign_x (Div (Var y, Var z))
  | Cls.Mod (y, z) -> assign_x (Mod (Var y, Var z))
  | Cls.CComp (y, z) -> assign_x (Cast (VALUE, App (Var "compose", [Cast (PTR CRC, Var y); Cast (PTR CRC, Var z)])))
  | Cls.AppDDir (l, (y1, y2)) ->
    assign_x (App (Var ("fun_" ^ l), [Cast (VALUE, Null); Var y1; Var y2]))
  | Cls.AppDCls (y, (z1, z2)) ->
    let func = Arrow (Cast (PTR FUN, Var y), "funcD") in
    assign_x (App (func, [Var y; Var z1; Var z2]))
  | Cls.AppMDir (l, y) ->
    let alt_str = if config.alt then "alt_" else "" in
    assign_x (App (Var ("fun_" ^ alt_str ^ l), [Cast (VALUE, Null); Var y]))
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
    toC_assign ~config x (Cls.AppTy (y, i1, tas, n)) @ [SAssign (LVar x, App (Var ("tfun_" ^ y), [Var x; Cast (VALUE, Null)]))]
  | Cls.CApp (y, z) -> assign_x (App (Var "coerce", [Var y; Cast (PTR CRC, Var z)]))
  (* TODO: CrcManager から inj, proj を消したので、最適化処理はtoCに任せる *)
  | Cls.Cast (y, u1, u2, (r, p)) -> assign_x (App (Var "cast", [Var y; toC_ty u1; toC_ty u2; Int (int_of_string @@ RangeManager.find r); Int (match p with Pos -> 1 | Neg -> 0)]))
  | Cls.Let (y, f1, f2) -> SDecl (VALUE, y, None) :: toC_assign ~config y f1 @ toC_assign ~config x f2
  | Cls.IfEq (y, z, f1, f2) ->
    SIf (Eq (Var y, Var z), toC_assign ~config x f1, toC_assign ~config x f2) :: []
  | Cls.IfLte (y, z, f1, f2) ->
    SIf (Lte (Var y, Var z), toC_assign ~config x f1, toC_assign ~config x f2) :: []
  | Cls.MakeCls (x, cls, f) ->
    let set_func fun_x =
      let alt_str = if config.alt then "alt_" else "" in
      let func_d = Var ("fun_" ^ cls.entry) in
      let func_m = Var ("fun_" ^ alt_str ^ cls.entry) in
      set_func_stm ~config fun_x func_d func_m
    in
    make_cls_stm ~set_func x cls @ toC_assign ~config x f
  | Cls.MakeTyCls (x, cls, f) ->
    let set_func fun_x = [SAssign (LArrow (fun_x, "funcM"), Var ("tfun_" ^ cls.entry))] in
    make_cls_stm ~set_func x cls @ toC_assign ~config x f
  | Cls.SetTy ((i, { contents = opu }), f) ->
    let name, stm = set_ty i opu in
    SDecl (PTR TY, name, Some (Malloc (PTR TY, Sizeof TY))) :: stm @ toC_assign ~config x f
  | _ -> raise @@ ToC_bug (Format.asprintf "toC_assign yet: %a" Pp.Cls.pp_exp f)

(* ======================================= *)

let toC_tydecls tys = List.map (fun (_, name) -> Decl (Static, TY, name, None)) tys

(*型の定義*)
(*let toC_tycontent ppf (u, name) = match u with
  ...
  | TyList u ->
    fprintf ppf "static ty %s = { .tykind = TYLIST, .tydat.tylist = %s };"
      name
      (c_of_ty u)
  | TyTuple us ->
    let arity = List.length us in
    let tys_str = String.concat ", " (List.map (fun u -> "(ty*)" ^ c_of_ty u) us) in
    fprintf ppf "static ty *%s_tys[] = { %s };\n" name tys_str;
    fprintf ppf "static ty %s = { .tykind = TYTUPLE, .tydat.tytuple = { .arity = %d, .tys = %s_tys } };"
      name arity name  | u -> raise @@ ToC_bug (Format.asprintf "not tyvar, tyfun or tylist in tycontent: %a" Pp.pp_ty2 u) 
*)

let toC_tycontents tys =
  let toC_content = function
    | TyVar _ -> Struct ["tykind", Var "TYVAR"]
    | TyFun (u1, u2) ->
      Struct ["tykind", Var "TYFUN"; "tydat", Struct ["tyfun", Struct ["left", toC_ty u1; "right", toC_ty u2]]]
    | _ as u -> raise @@ ToC_bug (Format.asprintf "toC_content yet: %a" Pp.pp_ty u)
  in
  List.map (fun (u, name) -> Decl (Static, TY, name, Some (toC_content u))) tys

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

(*
(* コアーションの定義 *)
let toC_crccontent ppf (c, name) = 
  ...
  | CTuple cs ->
    let arity = List.length cs in
    let crcs_str = String.concat ", " (List.map (fun c -> "(crc*)" ^ c_of_crc c) cs) in
    fprintf ppf "static crc *%s_crcs[] = { %s };\n" name crcs_str;
    fprintf ppf "static crc %s = { .crckind = TUPLE, .has_tv = %d, .crcdat.tpl_crc = { .arity = %d, .crcs = %s_crcs } };"
      name has_tv_val arity name
  | CList c' ->
    fprintf ppf "static crc %s = { .crckind = LIST, .has_tv = %d, .crcdat.lst_crc = %s };"
      name
      has_tv_val
      (c_of_crc c')
  | _ -> raise @@ ToC_bug (Format.asprintf "not in crccontent")

(*型定義全体を記述*)
let toC_crcs ppf l ~config =
  let register_builtins ppf () =
    fprintf ppf "\tregister_static_crc(&crc_id);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_INT);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_BOOL);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_UNIT);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_AR);\n";
    fprintf ppf "\tregister_static_crc(&crc_inj_LI);\n"
  in
  if config.static then fprintf ppf ""
  else if l = [] then 
    fprintf ppf "\n#ifdef HASH\nstatic void init_crcs() {\n%a}\n#endif\n\n"
      register_builtins ()
  else 
    fprintf ppf "%a%a\n#ifdef HASH\nstatic void init_crcs() {\n%a%a}\n#endif\n\n"
      toC_crcdecls l
      toC_crccontents l
      register_builtins ()
      (fun ppf decls ->
         List.iter (fun (_, name) -> fprintf ppf "\tregister_static_crc(&%s);\n" name) decls
      ) l
*)

let toC_crcdecls crcs = List.map (fun (_, name) -> Decl (Static, CRC, name, None)) crcs

let toC_crccontents crcs = List.map (fun (c, name) -> Decl (Static, CRC, name, Some (snd @@ toC_crc name c))) crcs

let toC_crcs crcs = toC_crcdecls crcs, toC_crccontents crcs

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
    Include (Format.asprintf "\"../%slibC/runtime.h\"" (if bench = 0 then "" else "../../"));
  ]
  in
  let tydecl, tydef = toC_tys tys in
  let rangedef = toC_ranges ranges in
  let crcdecl, crcdef = toC_crcs crcs in
  let fundecl, fundef = toC_toplevel ~config toplevel in
  let decl = if bench = 0 && not config.static then [Decl (No, PTR RANGE, "range_list", None)] else [] in
  let main = [
    FunDef (
      No,
      { ret_ty = INT; fname = "main"; params = []},
      (if List.length ranges <> 0 then [SAssign (LVar "range_list", Var "local_range_list")] else [])
        @ toC_exp ~is_main:true ~config f
    )
  ]
  in
  inc @ tydecl @ tydef @ rangedef @ crcdecl @ crcdef @ fundecl @ fundef @ decl @ main

(* 
  let init_crcs = if config.static then "" else "#ifdef HASH\ninit_crcs();\n#endif\n" in
  fprintf ppf "%s\n%s\n%a%a%a%a%s%s%s%a%s"
    (if bench = 0 then "#define GC_INITIAL_HEAP_SIZE 1048576\n" else "")
    ...
    (if bench = 0 then asprintf "int main() {\nGC_INIT();\n%s" init_crcs else asprintf "int mutant%d() {\n%s" bench init_crcs)
    ...
*)

(* 

(* ======================================== *)
let rec toC_mf ppf (x, mf) ~config =
  let toC_mf = toC_mf ~config in
  match mf with
  | MatchVar _ | MatchBLit _ | MatchULit -> raise @@ ToC_bug "MatchVar, MatchBLit, MatchULit does not appear in toC"
  | MatchILit i -> 
    fprintf ppf "%s == %d"
      x
      i
  | MatchNil _ -> 
    if config.eager then
      fprintf ppf "((lst*)%s) == NULL"
        x
    else
      fprintf ppf "is_NULL((lst*)%s)"
        x
  | MatchCons (mf1, mf2) ->
    if config.eager then
      fprintf ppf "((lst*)%s) != NULL && %a && %a"
        x
        toC_mf (asprintf "((lst*)%s)->h" x, mf1)
        toC_mf (asprintf "((lst*)%s)->t" x, mf2)
    else
      fprintf ppf "!(is_NULL((lst*)%s)) && %a && %a"
        x
        toC_mf (asprintf "hd((lst*)%s)" x, mf1)
        toC_mf (asprintf "tl((lst*)%s)" x, mf2)
  | MatchTuple mfs ->
    let counter = ref (-1) in
    let toC_mfi ppf mi =
      if config.eager then
        toC_mf ppf (counter := !counter + 1; asprintf "((tpl*)%s)->fields[%d]" x !counter, mi)
      else
        toC_mf ppf (counter := !counter + 1; asprintf "tget((tpl*)%s, %d)" x !counter, mi)
    in
    let toC_sep ppf () = fprintf ppf " && " in
    let toC_list ppf ms = pp_print_list toC_mfi ppf ms ~pp_sep:toC_sep in
    fprintf ppf "%a"
      toC_list mfs
  | MatchWild _ -> 
    fprintf ppf "1"

let rec toC_exp ppf f ~config ~is_main = 
  let toC_exp = toC_exp ~config ~is_main in
  match f with
  | Insert (x, f) -> begin match f with
    | Nil -> 
      fprintf ppf "%s = 0;\n" (* Insert(x, []) ~> x.l = (lst* )NULL; *)
        x
    | Cons (y, z) -> (* Insert(x, y::z) ~> TODO *)
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(lst));\n((lst*)%s)->h = %s;\n((lst*)%s)->t = %s;\n"
        x
        x
        y
        x
        z
    | Tuple ys ->
      let arity = List.length ys in
      let counter = ref (-1) in
      let toC_sep ppf () = fprintf ppf "\n" in
      let toC_list ppf ys = pp_print_list (fun ppf y -> counter := !counter + 1; fprintf ppf "((tpl_raw*)%s)->fields[%d] = %s;" x !counter y) ppf ys ~pp_sep:toC_sep in
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(tpl_raw) + sizeof(value) * %d);\n((tpl_raw*)%s)->hdr.arity = %d;\n%a\n" x arity x arity toC_list ys;
    | Hd y -> (* TODO *)
      if config.eager then
        fprintf ppf "%s = ((lst*)%s)->h;\n"
          x
          y
      else
        fprintf ppf "%s = hd((lst*)%s);\n"
          x
          y
    | Tl y -> (* TODO *)
      if config.eager then
        fprintf ppf "%s = ((lst*)%s)->t;\n"
          x
          y
      else
        fprintf ppf "%s = tl((lst*)%s);\n"
          x
          y
    | Tget (y, i) ->
      if config.eager then
        fprintf ppf "%s = ((tpl*)%s)->fields[%d];\n"
          x
          y
          i
      else
        fprintf ppf "%s = tget((tpl*)%s, %d);\n"
          x
          y
          i
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
    | Match (y, ms) -> toC_exp ppf (Match (y, List.map (fun (mf, f) -> mf, Insert (x, f)) ms))
    end
  | Match (x, ms) ->
    begin match ms with
    | (mf, f) :: t ->
      fprintf ppf "if(%a) {\n%a} else %a"
        (toC_mf ~config) (x, mf)
        toC_exp f
        toC_exp (Match (x, t))
    | [] -> 
      fprintf ppf "{\nprintf(\"didn't match\");\nexit(1);\n}\n"
    end
  (*以下は項の中にexpを含まないので，main関数かどうかを判定してreturn文を変える必要がある．
    main関数ならreturn 0;でプログラムを終える．main関数でなければ，その値自体をreturnする．*)
  | Nil | Cons _ | Tuple _ | Hd _ | Tl _ | Tget _ | Ref _ | Deref _ | Subst _ as f ->
    fprintf ppf "value retv;\n%areturn %s;\n"
      toC_exp (Insert ("retv", f))
      (if is_main then "0" else "retv")
*)