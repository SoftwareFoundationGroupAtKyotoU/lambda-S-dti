open Syntax
open Syntax.C
open Config
(* open Utils.Error *)
open Static_manage
(* open Fv.Cls *)

exception ToC_bug of string
exception ToC_error of string

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
  | TyCoercion _ -> raise @@ ToC_error "c_of_ty tycoercion"

let toC_ta = function
  | Ty u -> toC_ty u
  | TyNu -> App (Var "newty", [])

let app_env l n f lst =
  let lval_env = LArrow (l, "env") in
  List.mapi (fun i h -> SAssign (LIndex (lval_env, n + i), Cast (PTR VOID, f h))) lst

let rec toC_exp ~is_main ~config = function
  | Cls.Let (x, f1, f2) ->
    SDecl (VALUE, x, None) :: toC_assign ~config x f1 @ toC_exp ~is_main ~config f2
  | Cls.IfEq (x, y, f1, f2) ->
    SIf (Eq (Var x, Var y), toC_exp ~is_main ~config f1, toC_exp ~is_main ~config f2) :: []
  | Cls.IfLte (x, y, f1, f2) ->
    SIf (Lte (Var x, Var y), toC_exp ~is_main ~config f1, toC_exp ~is_main ~config f2) :: []
  | Cls.MakeCls (x, { entry; fvs; offset = n; ftvs }, f) ->
    let env_size = List.length fvs + n + List.length ftvs in
    let cls = Malloc (VALUE, Add (Sizeof FUN, Mul (Sizeof (PTR VOID), Int env_size))) in
    let fun_x = LCast (PTR FUN, LVar x) in
    let set_func =
      if config.intoB || config.static then
        SAssign (LArrow (fun_x, "funcM"), Var ("fun_" ^ entry)) :: []
      else if config.alt then
        SAssign (LArrow (fun_x, "funcD"), Var ("fun_" ^ entry)) ::
        SAssign (LArrow (fun_x, "funcM"), Var ("fun_" ^ "alt_" ^ entry)) :: []
      else
        SAssign (LArrow (fun_x, "funcD"), Var ("fun_" ^ entry)) :: []
    in
    let app_fvs = app_env fun_x 0 (fun fv -> Var fv) fvs in
    let app_ftvs = app_env fun_x (List.length fvs + n) (fun ftv -> Var (string_of_tyvar ftv)) ftvs in
    SDecl (VALUE, x, Some cls) :: set_func @ app_fvs @ app_ftvs @ toC_exp ~is_main ~config f
  | Cls.Var _ | Cls.Int _ | Cls.Add _ | Cls.Sub _ | Cls.Mul _ | Cls.Div _ | Cls.Mod _ | Cls.Coercion _
  | Cls.AppDDir _ | Cls.AppDCls _  | Cls.AppMDir _ | Cls.AppMCls _ | Cls.AppTy _ | Cls.CApp _ as f ->
    let return = SReturn (if is_main then Int 0 else Var "retv") in
    SDecl (VALUE, "retv", None) :: toC_assign ~config "retv" f @ [return]
  | _ as f -> raise @@ ToC_bug (Format.asprintf "toC_exp yet: %a" Pp.Cls.pp_exp f)
and toC_assign ~config x f =
  let assign_x e = SAssign (LVar x, e) :: [] in
  match f with
  | Cls.Var y -> assign_x (Var y)
  | Cls.Int i -> assign_x (Int i)
  | Cls.Add (y, z) -> assign_x (Add (Var y, Var z))
  | Cls.Sub (y, z) -> assign_x (Sub (Var y, Var z))
  | Cls.Mul (y, z) -> assign_x (Mul (Var y, Var z))
  | Cls.Div (y, z) -> assign_x (Div (Var y, Var z))
  | Cls.Mod (y, z) -> assign_x (Mod (Var y, Var z))
  | Cls.Coercion (CId _) -> assign_x (Cast (VALUE, (Addr "crc_id")))
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
    let cls = Malloc (VALUE, Add (Sizeof FUN, Mul (Sizeof (PTR VOID), Int env_size))) in
    let fun_x = LCast (PTR FUN, LVar x) in
    let fun_y = Cast (PTR FUN, Var y) in
    let set_func =
      if config.intoB || config.static then
        SAssign (LArrow (fun_x, "funcM"), Arrow (fun_y, "funcM")) :: []
      else if config.alt then
        SAssign (LArrow (fun_x, "funcD"), Arrow (fun_y, "funcD")) ::
        SAssign (LArrow (fun_x, "funcM"), Arrow (fun_y, "funcM")) :: []
      else
        SAssign (LArrow (fun_x, "funcD"), Arrow (fun_y, "funcD")) :: []
    in
    let rec copy i n =
      if i = n then []
      else SAssign (LIndex (LArrow (fun_x, "env"), i), Index (Arrow (fun_y, "env"), i)) :: copy (i + 1) n
    in
    SAssign (LVar x, cls) :: set_func @ copy 0 i1 @ app_env fun_x i1 toC_ta tas @ copy (i1 + List.length tas) env_size
  | Cls.CApp (y, z) -> assign_x (App (Var "coerce", [Var y; Cast (PTR CRC, Var z)]))  (* TODO: CrcManager から inj, proj を消したので、最適化処理はtoCに任せる *)
  | Cls.Let (y, f1, f2) -> SDecl (VALUE, y, None) :: toC_assign ~config y f1 @ toC_assign ~config x f2
  | Cls.IfEq (y, z, f1, f2) ->
    SIf (Eq (Var y, Var z), toC_assign ~config x f1, toC_assign ~config x f2) :: []
  | Cls.IfLte (y, z, f1, f2) ->
    SIf (Lte (Var y, Var z), toC_assign ~config x f1, toC_assign ~config x f2) :: []
  (* | Cls.MakeCls (x, cls, f) -> *)
  | _ -> raise @@ ToC_bug (Format.asprintf "toC_assign yet: %a" Pp.Cls.pp_exp f)

let toC_tydecls tys = List.map (fun (_, name) -> Decl (Static, TY, name, None)) tys

(*型の定義*)
(*let toC_tycontent ppf (u, name) = match u with
  | TyVar _ -> (* TyVarはtykindをTYVARにする *)
    fprintf ppf "static ty %s = { .tykind = TYVAR };"
      name
  | TyFun (u1, u2) -> 
    (*TyFunはtykindをTYFUNとする
      さらに，leftとrightにTyFunの二つの型をそれぞれ代入する*)
    fprintf ppf "static ty %s = { .tykind = TYFUN, .tydat.tyfun = { .left = %s, .right = %s } };"
      name
      (c_of_ty u1)
      (c_of_ty u2)
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

let toC_tycontents ppf l = 
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_tycontent ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l*)

let toC_tycontents tys =
  let toC_content = function
    | TyVar _ -> Struct ["tykind", Var "TYVAR"]
    | TyFun (u1, u2) ->
      Struct ["tykind", Var "TYFUN"; "tydat", Struct ["tyfun", Struct ["left", toC_ty u1; "right", toC_ty u2]]]
    | _ as u -> raise @@ ToC_bug (Format.asprintf "toC_content yet: %a" Pp.pp_ty u)
  in
  List.map (fun (u, name) -> Decl (Static, TY, name, Some (toC_content u))) tys

let toC_tys tys = toC_tydecls tys, toC_tycontents tys

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

let toC_program ?(bench=0) ~config (Cls.Prog (toplevel, f)) =
  let tys = TyManager.get_definitions () in
  let inc = [
    Include "<gc.h>";
    Include (Format.asprintf "\"../%slibC/runtime.h\"" (if bench = 0 then "" else "../../"));
  ]
  in
  let tydecl, tydef = toC_tys tys in
  let fundecl, fundef = toC_toplevel ~config toplevel in
  let decl = if bench = 0 && not config.static then [Decl (No, PTR RANGE, "range_list", None)] else [] in
  let main = [FunDef (No, { ret_ty = INT; fname = "main"; params = []}, toC_exp ~is_main:true ~config f)] in
  inc @ tydecl @ tydef @ fundecl @ fundef @ decl @ main
  (* let tys = TyManager.get_definitions () in
  let ranges = RangeManager.get_definitions () in
  let crcs = CrcManager.get_definitions () in
  let init_crcs = if config.static then "" else "#ifdef HASH\ninit_crcs();\n#endif\n" in
  fprintf ppf "%s\n%s\n%a%a%a%a%s%s%s%a%s"
    (asprintf "#include <gc.h>\n#include \"../%slibC/runtime.h\"\n"
      (if bench = 0 then "" else "../../"))
    (if bench = 0 then "#define GC_INITIAL_HEAP_SIZE 1048576\n" else "")
    toC_tys tys
    toC_ranges ranges
    (toC_crcs ~config) crcs
    (toC_fundefs ~config) toplevel
    (if bench = 0 && not config.static then "range *range_list;\n\n" else "")
    (if bench = 0 then asprintf "int main() {\nGC_INIT();\n%s" init_crcs else asprintf "int mutant%d() {\n%s" bench init_crcs)
    (if List.length ranges != 0 then "range_list = local_range_list;\n" else "")
    (toC_exp ~config ~is_main:true) f
    "}" *)

(* 
let toC_tag ppf = function
  | I -> pp_print_string ppf "INT"
  | B -> pp_print_string ppf "BOOL"
  | U -> pp_print_string ppf "UNIT"
  | Ar -> pp_print_string ppf "AR"
  | Li -> pp_print_string ppf "LI"
  | Tp _ -> pp_print_string ppf "TP"
  | Rf -> pp_print_string ppf "RF"

let rec toC_crc ppf (c, x) = 
  if CrcManager.mem c then 
    fprintf ppf "%s = (value)&%s;" x (CrcManager.find c)
  else match c with
  | CId -> fprintf ppf "%s = (value)&crc_id;" x
  | CSeqInj (CId, (I | B | U | Ar | Li as t)) ->
    fprintf ppf "%s = (value)&crc_inj_%a;" x toC_tag t
  | CSeqInj (CId, Tp arity) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = SEQ_INJ;\n%s_temp.g_inj = G_TP;\n%s_temp.arity_inj = %d;\n%s_temp.has_tv = 0;\n%s_temp.crcdat.seq_tv.ptr.s = &crc_id;\n%s = (value)alloc_crc(&%s_temp);"
      x x x x arity x x x x
  | CSeqInj (CFun _ as c1, Ar) ->
    fprintf ppf "value %s_cfun;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_INJ;\n%s_temp.g_inj = G_AR;\n%s_temp.has_tv = ((crc*)%s_cfun)->has_tv;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_cfun;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c1, x ^ "_cfun") x x x x x x x x x
  | CSeqInj (CList _ as c1, Li) ->
    fprintf ppf "value %s_clist;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_INJ;\n%s_temp.g_inj = G_LI;\n%s_temp.has_tv = ((crc*)%s_clist)->has_tv;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_clist;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c1, x ^ "_clist") x x x x x x x x x
  | CSeqInj (CTuple _ as c1, Tp arity) ->
    fprintf ppf "value %s_ctuple;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_INJ;\n%s_temp.g_inj = G_TP;\n%s_temp.arity_inj = %d;\n%s_temp.has_tv = ((crc*)%s_ctuple)->has_tv;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_ctuple;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c1, x ^ "_ctuple") x x x x arity x x x x x x
  | CSeqProj ((I | B | U | Ar | Li as t), (r, p), CId) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_%a;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = 0;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = &crc_id;\n%s = (value)alloc_crc(&%s_temp);"
      x x x toC_tag t x (match p with Pos -> 1 | Neg -> 0) x x r x x x
  | CSeqProj (Tp arity, (r, p), CId) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_TP;\n%s_temp.arity_proj = %d;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = 0;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)&crc_id;\n%s = (value)alloc_crc(&%s_temp);"
      x x x x arity x (match p with Pos -> 1 | Neg -> 0) x x r x x x
  | CSeqProj (Ar, (r, p), (CFun _ as c2)) ->
    fprintf ppf "value %s_cfun;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_AR;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = ((crc*)%s_cfun)->has_tv;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_cfun;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c2, x ^ "_cfun") x x x x (match p with Pos -> 1 | Neg -> 0) x x x r x x x x
  | CSeqProj (Li, (r, p), (CList _ as c2)) ->
    fprintf ppf "value %s_clist;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_LI;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = ((crc*)%s_clist)->has_tv;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_clist;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c2, x ^ "_clist") x x x x (match p with Pos -> 1 | Neg -> 0) x x x r x x x x
  | CSeqProj (Tp arity, (r, p), (CTuple _ as c2)) ->
    fprintf ppf "value %s_ctuple;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = SEQ_PROJ;\n%s_temp.g_proj = G_TP;\n%s_temp.arity_proj = %d;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = ((crc*)%s_ctuple)->has_tv;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.s = (crc*)%s_ctuple;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c2, x ^ "_ctuple") x x x x arity x (match p with Pos -> 1 | Neg -> 0) x x x r x x x x
  | CTvInj (tv, (r, p)) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = TV_INJ;\n%s_temp.p_inj = %d;\n%s_temp.has_tv = 1;\n%s_temp.crcdat.seq_tv.rid_inj = %d;\n%s_temp.crcdat.seq_tv.ptr.tv = %s;\n%s = (value)alloc_crc(&%s_temp);"
      x x x (match p with Pos -> 1 | Neg -> 0) x x r x (c_of_ty (TyVar tv)) x x
  | CTvProj (tv, (r, p)) ->
    fprintf ppf "crc %s_temp = {0};\n%s_temp.crckind = TV_PROJ;\n%s_temp.p_proj = %d;\n%s_temp.has_tv = 1;\n%s_temp.crcdat.seq_tv.rid_proj = %d;\n%s_temp.crcdat.seq_tv.ptr.tv = %s;\n%s = (value)alloc_crc(&%s_temp);"
      x x x (match p with Pos -> 1 | Neg -> 0) x x r x (c_of_ty (TyVar tv)) x x
  | CFun (c1, c2) ->
    fprintf ppf "value %s_c1;\n%a\nvalue %s_c2;\n%a\ncrc %s_temp = {0};\n%s_temp.crckind = FUN;\n%s_temp.has_tv = ((crc*)%s_c1)->has_tv | ((crc*)%s_c2)->has_tv;\n%s_temp.crcdat.fun_crc.c1 = (crc*)%s_c1;\n%s_temp.crcdat.fun_crc.c2 = (crc*)%s_c2;\n%s = (value)alloc_crc(&%s_temp);"
      x toC_crc (c1, x ^ "_c1") x toC_crc (c2, x ^ "_c2") x x x x x x x x x x x
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
  | _ -> raise @@ ToC_bug "bad coercion"

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
  | Let (x, f1, f2) -> (* 先にxを宣言しておいて，f1の内容をxに代入する *)
    fprintf ppf "value %s;\n%a%a"
      x
      toC_exp (Insert (x, f1))
      toC_exp f2
  | Insert (x, f) -> begin match f with
    | Var y -> 
      fprintf ppf "%s = %s;\n" (* Insert(x, y) ~> x = y; *)
        x
        y
    | Int i -> 
      fprintf ppf "%s = %d;\n" (* Insert(x, i) ~> x.i_b_u = i; *)
        x
        i
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
    | Add (y, z) ->
      fprintf ppf "%s = %s + %s;\n" (* Insert (x, y+z) ~> x.i_b_u = y.i_b_u + z.i_b_u; *)
        x
        y
        z
    | Sub (y, z) ->
      fprintf ppf "%s = %s - %s;\n" (*Addと同じ*)
        x
        y
        z
    | Mul (y, z) ->
      fprintf ppf "%s = %s * %s;\n" (*Addと同じ*)
        x
        y
        z
    | Div (y, z) ->
      fprintf ppf "%s = %s / %s;\n" (*Addと同じ*)
        x
        y
        z
    | Mod (y, z) ->
      fprintf ppf "%s = %s %% %s;\n" (*Addと同じ*)
        x
        y
        z
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
    | AppDDir (y, (z1, z2)) ->
      fprintf ppf "%s = fun_%s(0, %s, %s);\n" (* Insert(x, y (z1, z2)) ~> x = fun_y(z1, z2); *) (*yが直接適用できる関数の場合*)
        x
        y
        z1
        z2
    | AppDCls (y, (z1, z2)) ->
      fprintf ppf "%s = (((fun*)%s)->funcD)(%s, %s, %s);\n" (* Insert(x, y (z1, z2)) ~> x = appD(y, z1, z2); *) (*yがクロージャを用いて適用する関数の場合*)
        x
        y
        y
        z1
        z2
    | AppMDir (y, z) ->
      fprintf ppf "%s = fun%s_%s(0, %s);\n" (* Insert(x, y z) ~> x = fun_y(z); *) (*yが直接適用できる関数の場合*)
        x
        (if config.alt then "_alt" else "")
        y
        z
    | AppMCls (y, z) -> 
      fprintf ppf "%s = (((fun*)%s)->funcM)(%s, %s);\n" (* Insert(x, y z) ~> x = appM(y, z); *) (*yがクロージャを用いて適用する関数の場合*)
        x
        y
        y
        z
    | AppTy (y, zs_len, outer_tvs_len, tas) ->
      let total_env_size = zs_len + List.length tas + outer_tvs_len in
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n*((fun*)%s) = *((fun*)%s);\n%a"
        x
        total_env_size
        x
        y
        toC_tas (y, zs_len, total_env_size, x, tas)
    | AppTyFun (y, zs_len, outer_tvs_len, tas) ->
      let total_env_size = zs_len + List.length tas + outer_tvs_len in
      fprintf ppf "%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n*((fun*)%s) = *((fun*)%s);\n%a%s = tfun_%s(%s, 0);\n"
        x
        total_env_size
        x
        y
        toC_tas (y, zs_len, total_env_size, x, tas)
        x
        y
        x
    | Cast (y, u1, u2, (r, p)) -> 
      (*
      Insert(x, y:u1=>^(r, p)u2)
      ~>
      ran_pol x_r_p = { .filename = ~~, .startline = ~~, .startchr = ~~, .endline = ~~, .endchr = ~~, .polarity = ~~};
      x = cast(y, u1, u2, x_p_r);
      *)
      (*filenameやrangeの出力形式はUtilsを参照*)
      (*castの処理にはcast関数を用いる*)
      (*型の出力形式は関数c_of_tyによる TODO *)
      (* 名前の被りを防ぐために，Letとinsertはran_polにyではなくxを使う *)
      let c1, c2 = c_of_ty u1, c_of_ty u2 in
      fprintf ppf "%s = cast(%s, %s, %s, %d, %d);\n"
        x
        y
        c1
        c2
        r
        (match p with Pos -> 1 | Neg -> 0)
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
    | Coercion c -> (* TODO *)
      fprintf ppf "%a\n"
        toC_crc (c, x)
    | CSeq (y, z) -> 
      fprintf ppf "%s = (value)compose((crc*)%s, (crc*)%s);\n"
        x
        y
        z
    (*以下は内部にexpがあるので，後者のexpまでinsertを送る
      letはf2のみに，ifはf1,f2の両方にinsertを送る*)
    | Let (y, f1, f2) -> toC_exp ppf (Let (y, f1, Insert (x, f2)))
    | IfEq (y, z, f1, f2) -> toC_exp ppf (IfEq (y, z, Insert (x, f1), Insert (x, f2)))
    | IfLte (y, z, f1, f2) -> toC_exp ppf (IfLte (y, z, Insert (x, f1), Insert (x, f2)))
    | Match (y, ms) -> toC_exp ppf (Match (y, List.map (fun (mf, f) -> mf, Insert (x, f)) ms))
    | MakeCls (y, c, tvs, f) -> toC_exp ppf (MakeCls (y, c, tvs, Insert (x, f)))
    | MakeTyCls (y, c, tvs, f) -> toC_exp ppf (MakeTyCls (y, c, tvs, Insert (x, f)))
    | SetTy (tv, f) -> toC_exp ppf (SetTy (tv, Insert (x, f)))
    (*insertはletの一項目には最初の一回しか入らないので，二回insertがかぶさることはない*)
    | Insert _ -> raise @@ ToC_bug "Insert should not be doubled"
    end
  | IfEq (x, y, f1, f2) ->
    (*
    if x = y then f1 else f2
    ~>
    if(x.i_b_u == y.i_b_u) {
      f1
    } else {
      f2
    }
    *)
    (*等価判定はint型を用いて行うので，.i_b_uを取り出す*)
    fprintf ppf "if(%s == %s) {\n%a} else {\n%a}\n"
      x
      y
      toC_exp f1
      toC_exp f2
  | IfLte (x, y, f1, f2) -> (*IfEqと同じ*)
    fprintf ppf "if(%s <= %s) {\n%a} else {\n%a}\n"
      x
      y
      toC_exp f1
      toC_exp f2
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
  | MakeCls (x, { entry = l; actual_fv = vs }, { ftvs = ftv; offset = n }, f) -> (*TODO*)
    let env_size = List.length vs + List.length ftv + n in
    cnt_env := 0;
    fprintf ppf "value %s;\n%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n%s%a%a%a"
      x
      x
      env_size
      begin if config.intoB || config.static then
        asprintf "((fun*)%s)->funcM = fun_%s;\n" x l
      else if config.alt then
        asprintf "((fun*)%s)->funcD = fun_%s;\n((fun*)%s)->funcM = fun_alt_%s;\n" x l x l
      else
        asprintf "((fun*)%s)->funcD = fun_%s;\n" x l
      end
      toC_vs (x, vs)
      toC_ftas (n, x, ftv)
      toC_exp f
  | MakeTyCls (x, { entry = l; actual_fv = vs }, { ftvs = ftv; offset = n }, f) -> (*TODO*)
    let env_size = List.length vs + List.length ftv + n in
    cnt_env := 0;
    fprintf ppf "value %s;\n%s = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * %d);\n%s%a%a%a"
      x
      x
      env_size
      (asprintf "((fun*)%s)->funcM = tfun_%s;\n" x l)
      toC_vs (x, vs)
      toC_ftas (n, x, ftv)
      toC_exp f
  | SetTy ((i, { contents = opu }), f) -> begin match opu with (* ここはtoC_tycontentを参照 *)
    | None ->
        fprintf ppf "ty *_ty%d = (ty*)GC_MALLOC(sizeof(ty));\n_ty%d->tykind = TYVAR;\n%a"
          i
          i
          toC_exp f
    | Some (TyFun (u1, u2)) -> 
      fprintf ppf "ty *_tyfun%d = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tykind = TYFUN;\n_tyfun%d->tydat.tyfun.left = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tydat.tyfun.right = (ty*)GC_MALLOC(sizeof(ty));\n_tyfun%d->tydat.tyfun.left = %s;\n_tyfun%d->tydat.tyfun.right = %s;\n%a"
        i
        i
        i
        i
        i
        (c_of_ty u1)
        i
        (c_of_ty u2)
        toC_exp f
    | Some (TyList u) -> 
      fprintf ppf "ty *_tylist%d = (ty*)GC_MALLOC(sizeof(ty));\n_tylist%d->tykind = TYLIST;\n_tylist%d->tydat.tylist = (ty*)GC_MALLOC(sizeof(ty));\n_tylist%d->tydat.tylist = %s;\n%a"
        i
        i
        i
        i
        (c_of_ty u)
        toC_exp f
    | Some _ -> raise @@ ToC_bug "not tyfun or tylist is in tyvar option"
    end
  (*以下は項の中にexpを含まないので，main関数かどうかを判定してreturn文を変える必要がある．
    main関数ならreturn 0;でプログラムを終える．main関数でなければ，その値自体をreturnする．*)
  | Var _ | Int _ | Nil | Cons _ | Tuple _ | Add _ | Sub _ | Mul _ | Div _ | Mod _ | Hd _ | Tl _ | Tget _ | AppDDir _ | AppDCls _ | AppMDir _ | AppMCls _ | Cast _ | AppTy _ | AppTyFun _ | CApp _ | Coercion _ | CSeq _ | Ref _ | Deref _ | Subst _ as f ->
    fprintf ppf "value retv;\n%areturn %s;\n"
      toC_exp (Insert ("retv", f))
      (if is_main then "0" else "retv")

(* =================================== *)

(*型定義をするCプログラムを記述*)
(*ここで行われる型定義は，プログラム全体で共有される型についてのみである*)
(*型名の前方定義
  型はポインタなので，共有して型を扱うには，まず名前を先に定義する必要がある*)
let toC_tydecl ppf (_, name) =
  fprintf ppf "static ty %s;" name

let toC_tydecls ppf l = 
  if List.length l = 0 then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_tydecl ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l

(*型の定義*)
let toC_tycontent ppf (u, name) = match u with
  | TyVar _ -> (* TyVarはtykindをTYVARにする *)
    fprintf ppf "static ty %s = { .tykind = TYVAR };"
      name
  | TyFun (u1, u2) -> 
    (*TyFunはtykindをTYFUNとする
      さらに，leftとrightにTyFunの二つの型をそれぞれ代入する*)
    fprintf ppf "static ty %s = { .tykind = TYFUN, .tydat.tyfun = { .left = %s, .right = %s } };"
      name
      (c_of_ty u1)
      (c_of_ty u2)
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

let toC_tycontents ppf l = 
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_tycontent ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l

(*型定義全体を記述*)
let toC_tys ppf l =
  if l = [] then fprintf ppf ""
  else 
    fprintf ppf "%a%a\n\n"
      toC_tydecls l
      toC_tycontents l

(* ================================ *)

(*Castのran_polを記述する関数*)
(*toC_exp Let Castを参照*)
let toC_range ppf (r, _) =
  fprintf ppf "{ .filename = %s, .startline = %d, .startchr = %d, .endline = %d, .endchr = %d }"
    (if r.start_p.pos_fname <> "" then "\"File \\\""^r.start_p.pos_fname^"\\\", \"" else "\"\"")
    r.start_p.pos_lnum
    (r.start_p.pos_cnum - r.start_p.pos_bol)
    r.end_p.pos_lnum
    (r.end_p.pos_cnum - r.end_p.pos_bol)

let toC_ranges ppf ranges =
  let toC_sep ppf () = fprintf ppf ",\n" in
  let toC_list ppf range = pp_print_list toC_range ppf range ~pp_sep:toC_sep in
  if List.length ranges = 0 then 
    fprintf ppf ""(*"#ifndef STATIC\nstatic range local_range_list[] = { 0 };\n#endif\n\n"*)
  else
  fprintf ppf "static range local_range_list[] = {\n%a\n};\n\n"
    toC_list (List.sort (fun (_, i1) (_, i2) -> compare i1 i2) ranges)

(* ================================ *)

(*コアーション定義をするCプログラムを記述*)
(*ここで行われるコアーション定義は，プログラム全体で共有されるコアーションについてのみである*)
(*コアーション名の前方定義*)
let toC_crcdecl ppf (_, name) =
  fprintf ppf "static crc %s;" name

let toC_crcdecls ppf l = 
  if List.length l = 0 then fprintf ppf ""
  else let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_crcdecl ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l
    
let rec check_has_tv = function
  | CId -> false
  | CSeqInj (c', _) | CSeqProj (_, _, c') | CList c' -> check_has_tv c'
  | CTvInj _ | CTvProj _ -> true
  | CFun (c1, c2) -> (check_has_tv c1) || (check_has_tv c2)
  | CTuple cs -> List.fold_left (fun b c -> b || check_has_tv c) false cs

(* コアーションの定義 *)
let toC_crccontent ppf (c, name) = 
  let has_tv_val = if check_has_tv c then 1 else 0 in
  let c_of_crc c = match c with
  | CId -> "&crc_id"
  | CSeqInj (CId, g) -> Format.asprintf "&crc_inj_%a" toC_tag g
  | _ -> "&" ^ CrcManager.find c 
  in match c with
  | CSeqInj (c', g) ->
    let arity_str = match g with Tp arity -> Format.asprintf ", .arity_inj = %d" arity | _ -> "" in
    fprintf ppf "static crc %s = { .crckind = SEQ_INJ, .g_inj = G_%a%s, .has_tv = %d, .crcdat.seq_tv = { .ptr.s = (crc*)%s } };"
      name
      toC_tag g
      arity_str
      has_tv_val
      (c_of_crc c')
  | CSeqProj (g, (rid, p), c') -> 
    let arity_str = match g with Tp arity -> Format.asprintf ", .arity_proj = %d" arity | _ -> "" in
    fprintf ppf "static crc %s = { .crckind = SEQ_PROJ, .g_proj = G_%a%s, .p_proj = %d,  .has_tv = %d, .crcdat.seq_tv = { .rid_proj = %d, .ptr.s = (crc*)%s } };"
      name
      toC_tag g
      arity_str
      (match p with Pos -> 1 | Neg -> 0)
      has_tv_val
      rid
      (c_of_crc c')
  | CTuple cs ->
    let arity = List.length cs in
    let crcs_str = String.concat ", " (List.map (fun c -> "(crc*)" ^ c_of_crc c) cs) in
    fprintf ppf "static crc *%s_crcs[] = { %s };\n" name crcs_str;
    fprintf ppf "static crc %s = { .crckind = TUPLE, .has_tv = %d, .crcdat.tpl_crc = { .arity = %d, .crcs = %s_crcs } };"
      name has_tv_val arity name
  | CTvInj (tv, (rid, p)) ->
    fprintf ppf "static crc %s = { .crckind = TV_INJ, .p_inj = %d, .has_tv = %d, .crcdat.seq_tv = { .rid_inj = %d, .ptr.tv = %s } };"
      name
      (match p with Pos -> 1 | Neg -> 0)
      has_tv_val
      rid
      (c_of_ty (TyVar tv))
  | CTvProj (tv, (rid, p)) ->
    fprintf ppf "static crc %s = { .crckind = TV_PROJ, .p_proj = %d, .has_tv = %d, .crcdat.seq_tv = { .rid_proj = %d, .ptr.tv = %s } };"
      name
      (match p with Pos -> 1 | Neg -> 0)
      has_tv_val
      rid
      (c_of_ty (TyVar tv))
  | CFun (c1, c2) -> 
    fprintf ppf "static crc %s = { .crckind = FUN, .has_tv = %d, .crcdat.fun_crc = { .c1 = %s, .c2 = %s } };"
      name
      has_tv_val
      (c_of_crc c1)
      (c_of_crc c2)
  | CList c' ->
    fprintf ppf "static crc %s = { .crckind = LIST, .has_tv = %d, .crcdat.lst_crc = %s };"
      name
      has_tv_val
      (c_of_crc c')
  | _ -> raise @@ ToC_bug (Format.asprintf "not in crccontent")

let toC_crccontents ppf l = 
  let toC_sep ppf () = fprintf ppf "\n" in
  let toC_list ppf decls = pp_print_list toC_crccontent ppf decls ~pp_sep:toC_sep in
  fprintf ppf "%a\n"
    toC_list l

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

(* ================================ *)
  
(*関数定義全体を記述*)
let toC_fundefs ppf toplevel ~config =
  if toplevel = [] then pp_print_string ppf ""
  else let toC_sep ppf () = fprintf ppf "\n\n" in
  let toC_list ppf labels = pp_print_list (toC_label ~config) ppf labels ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n"
    toC_list toplevel;
  let toC_list ppf defs = pp_print_list (toC_fundef ~config) ppf defs ~pp_sep:toC_sep in
  fprintf ppf "%a\n\n" 
    toC_list toplevel

(* =================================== *)

(*全体を記述*)
let toC_program ?(bench=0) ~config ppf (Prog (toplevel, f)) =
  let tys = TyManager.get_definitions () in
  let ranges = RangeManager.get_definitions () in
  let crcs = CrcManager.get_definitions () in
  let init_crcs = if config.static then "" else "#ifdef HASH\ninit_crcs();\n#endif\n" in
  fprintf ppf "%s\n%s\n%a%a%a%a%s%s%s%a%s"
    (asprintf "#include <gc.h>\n#include \"../%slibC/runtime.h\"\n"
      (if bench = 0 then "" else "../../"))
    (if bench = 0 then "#define GC_INITIAL_HEAP_SIZE 1048576\n" else "")
    toC_tys tys
    toC_ranges ranges
    (toC_crcs ~config) crcs
    (toC_fundefs ~config) toplevel
    (if bench = 0 && not config.static then "range *range_list;\n\n" else "")
    (if bench = 0 then asprintf "int main() {\nGC_INIT();\n%s" init_crcs else asprintf "int mutant%d() {\n%s" bench init_crcs)
    (if List.length ranges != 0 then "range_list = local_range_list;\n" else "")
    (toC_exp ~config ~is_main:true) f
    "}" *)