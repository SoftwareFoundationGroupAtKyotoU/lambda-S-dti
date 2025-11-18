open Syntax

exception Closure_bug of string
exception Closure_error of string

let toplevel = ref []

let tvset = ref TV.empty

module KNorm = struct
  open Syntax.KNorm

  let rec exist_tv l1 l2 = match l2 with
    | h :: t -> if List.mem h l1 then true else exist_tv l1 t
    | [] -> false
  
  let rec ty_tv tvs = function
    | TyInt | TyBool | TyUnit | TyDyn | TyFun (TyDyn, TyDyn) as u -> (u, fun x -> x)
    | TyVar tv as u -> if not (List.mem tv tvs) then (tvset := TV.add tv !tvset; (u, fun x -> x)) else (u, fun x -> x)
    | TyFun (u1, u2) ->
      let u1, ufun1 = ty_tv tvs u1 in
      let u2, ufun2 = ty_tv tvs u2 in
      let newu = Typing.fresh_tyvar () in
      let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyFun (u1, u2)); (i, u)
        | _ -> raise @@ Closure_bug "not tyvar was created"
      in if not (exist_tv (TV.elements (Syntax.ftv_ty u1)) tvs) && not (exist_tv (TV.elements (Syntax.ftv_ty u2)) tvs) then 
        (tvset := TV.add newtv !tvset; (newu, fun x -> ufun1 (ufun2 x)))
      else (newu, fun x -> ufun1 (ufun2 (Cls.SetTy (newtv, x))))
    | TyCoercion _ -> raise @@ Closure_bug "TyCoercion yet"

  let ta_tv tvs = function
    | Ty u -> let (u, f) = ty_tv tvs u in (Ty u, f)
    | TyNu -> (TyNu, fun x -> x)

  let tyvar_to_tyarg tvs = 
    let rec ttt l r = match l with
    | tv :: t -> ttt t ((Ty (TyVar tv)) :: r)
    | [] -> r
  in ttt (List.rev tvs) []

  let rec crc_tv tvs = function
    | CInj _ | CProj _ | CId _ -> ()
    | CTvInj tv | CTvProj (tv, _) | CTvProjInj (tv, _) -> 
      if not (List.mem tv tvs) then tvset := TV.add tv !tvset else ()
    | CFun (c1, c2) | CSeq (c1, c2) -> 
      crc_tv tvs c1; crc_tv tvs c2
    | CFail _ -> raise @@ Closure_bug "CFail appear in crc_tv" 

  let rec toCls_exp known tvs = function
    | Var x -> Cls.Var x
    | IConst i -> Cls.Int i
    | UConst -> Cls.Unit
    | Add (x, y) -> Cls.Add (x, y)
    | Sub (x, y) -> Cls.Sub (x, y)
    | Mul (x, y) -> Cls.Mul (x, y)
    | Div (x, y) -> Cls.Div (x, y)
    | Mod (x, y) -> Cls.Mod (x, y)
    | IfEqExp (x, y, f1, f2) -> Cls.IfEq (x, y, toCls_exp known tvs f1, toCls_exp known tvs f2)
    | IfLteExp (x, y, f1, f2) -> Cls.IfLte (x, y, toCls_exp known tvs f1, toCls_exp known tvs f2)
    | AppExp (x, y) when Cls.V.mem x known -> Cls.AppDir (Cls.to_label x, y)
    | AppExp (x, y) -> Cls.AppCls (x, y)
    (* | AppExp_alt (x, y) when Cls.V.mem x known -> Cls.AppDir_alt (Cls.to_label x, y)
    | AppExp_alt (x, y) -> Cls.AppCls_alt (x, y) *)
    | AppTy (x, _, tas) -> 
      let uandf = List.map (ta_tv tvs) tas in
      let rec destruct_uandf l ru rf = match l with
        | (u, f) :: t -> destruct_uandf t (u::ru) (fun x -> rf (f x))
        | [] -> ru, rf 
      in let us, f = destruct_uandf (List.rev uandf) [] (fun x -> x) in
      f (Cls.AppTy (x, List.length tas + List.length tvs, us))
    (* | CastExp (r, x, u1, u2, p) -> 
      let u1, udeclfun1 = ty_tv tvs u1 in 
      let u2, udeclfun2 = ty_tv tvs u2 in 
      udeclfun1 (udeclfun2 (Cls.Cast (x, u1, u2, r, p))) *)
    | CAppExp (x, y) -> Cls.CApp (x, y)
    | CSeqExp (x, y) -> Cls.CSeq (x, y)
    | CoercionExp c -> 
      crc_tv tvs c;
      Coercion c
    | LetExp (x, f1, f2) -> 
      let f1 = toCls_exp known tvs f1 in
      let f2 = toCls_exp known tvs f2 in
      Cls.Let (x, f1, f2)
    | LetRecExp (x, tvs', (y, z), f1, f2) ->
      let toplevel_backup = !toplevel in
      let tvset_backup = !tvset in
      let new_tvs = tvs' @ tvs in
      let known' = Cls.V.add x known in
      let f1' = toCls_exp known' new_tvs f1 in
      let zs = Cls.V.diff (Cls.fv f1') (Cls.V.of_list [y; z]) in
      let known', f1' =
        if Cls.V.is_empty zs && List.length new_tvs = 0 then known', f1'
        else (toplevel := toplevel_backup; tvset := tvset_backup;
        let f1' = toCls_exp known new_tvs f1 in
        known, f1')
      in let zs = Cls.V.elements (Cls.V.diff (Cls.fv f1') (Cls.V.of_list [x; y; z])) in
      (* let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in *)
      toplevel := (Cls.Fundef { name = Cls.to_label x; tvs = (new_tvs, List.length tvs'); arg = (y, z); formal_fv = zs; body = f1' }) :: !toplevel;
      let f2' = toCls_exp known' tvs f2 in
      if Cls.V.mem x (Cls.fv f2') then
        if List.length zs = 0 && List.length new_tvs = 0 then Cls.MakeLabel (x, Cls.to_label x, f2')
        else if List.length new_tvs = 0 then Cls.MakeCls (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, f2')
        else if List.length zs = 0 then Cls.MakePolyLabel (x, Cls.to_label x, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
        else Cls.MakePolyCls (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
      else f2'
    (* | LetRecExp_alt (x, tvs', (y, z), (f11, f12), f2) ->
      let toplevel_backup = !toplevel in
      let tvset_backup = !tvset in
      let new_tvs = tvs' @ tvs in
      let known' = Cls.V.add x known in
      let f11' = toCls_exp known' new_tvs f11 in
      let zs = Cls.V.diff (Cls.fv f11') (Cls.V.of_list [y; z]) in
      let known', f11', f12' =
        if Cls.V.is_empty zs && List.length new_tvs = 0 then known', f11', toCls_exp known' new_tvs f12
        else (toplevel := toplevel_backup; tvset := tvset_backup;
        let f11' = toCls_exp known new_tvs f11 in
        let f12' = toCls_exp known new_tvs f12 in
        known, f11', f12')
      in let zs = Cls.V.elements (Cls.V.diff (Cls.fv f11') (Cls.V.of_list [x; y; z])) in
      (* let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in *)
      toplevel := (Cls.Fundef { name = Cls.to_label x; tvs = (new_tvs, List.length tvs'); arg = (y, z); formal_fv = zs; body = f12' }) :: !toplevel;
      toplevel := (Cls.Fundef_alt { name = Cls.to_label x; tvs = (new_tvs, List.length tvs'); arg = y; formal_fv = zs; body = f11' }) :: !toplevel;
      let f2' = toCls_exp known' tvs f2 in
      if Cls.V.mem x (Cls.fv f2') then
        if List.length zs = 0 && List.length new_tvs = 0 then Cls.MakeLabel_alt (x, Cls.to_label x, f2')
        else if List.length new_tvs = 0 then Cls.MakeCls_alt (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, f2')
        else if List.length zs = 0 then Cls.MakePolyLabel_alt (x, Cls.to_label x, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
        else Cls.MakePolyCls_alt (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
      else f2' *)
    | LetRecExp_alt _ | AppExp_alt _ -> raise @@ Closure_bug "shouldn't apper alt in closure"

  let ini x vs = Cls.V.add x vs

  let venv = 
    ini "print_newline"
    @@ ini "print_bool"
    @@ ini "print_int"
    @@ Cls.V.empty
end

module Cls = struct
  open Syntax.Cls

  let rec replace_var vx vy f = 
    let replace x = if x = vx then vy else x in
    match f with
    | Var x -> Var (replace x)
    | Int i -> Int i
    | Unit -> Unit
    | Add (x, y) -> Add (replace x, replace y)
    | Sub (x, y) -> Sub (replace x, replace y)
    | Mul (x, y) -> Mul (replace x, replace y)
    | Div (x, y) -> Div (replace x, replace y)
    | Mod (x, y) -> Mod (replace x, replace y)
    | IfEq (x, y, f1, f2) -> IfEq (replace x, replace y, replace_var vx vy f1, replace_var vx vy f2)
    | IfLte (x, y, f1, f2) -> IfLte (replace x, replace y, replace_var vx vy f1, replace_var vx vy f2)
    | AppTy (x, n, tas) -> AppTy (replace x, n, tas)
    | AppCls (x, (y, k)) -> AppCls (replace x, (replace y, replace k))
    | AppDir (l, (y, k)) -> AppDir (to_label (replace (to_id l)), (replace y, replace k))
    | CApp (x, k) -> CApp (replace x, replace k)
    | CSeq (k1, k2) -> CSeq (replace k1, replace k2)
    | Coercion c -> Coercion c
    | Let (x, f1, f2) -> Let (x, replace_var vx vy f1, replace_var vx vy f2)
    | MakeCls (x, {entry = l; actual_fv = fvs}, f) -> MakeCls (x, {entry=to_label (replace (to_id l)); actual_fv = List.map replace fvs}, replace_var vx vy f)
    | MakeLabel (x, l, f) -> MakeLabel (x, to_label (replace (to_id l)), replace_var vx vy f)
    | MakePolyCls (x, {entry = l; actual_fv = fvs}, ftvs, f) -> MakePolyCls (x, {entry=to_label (replace (to_id l)); actual_fv = List.map replace fvs}, ftvs, replace_var vx vy f)
    | MakePolyLabel (x, l, ftvs, f) -> MakePolyLabel (x, to_label (replace (to_id l)), ftvs, replace_var vx vy f)
    | SetTy _ | Insert _ -> raise @@ Closure_bug "SetTy or Insert appear in replace"
    | AppCls_alt _ | AppDir_alt _ | MakeLabel_alt _ | MakeCls_alt _ | MakePolyLabel_alt _ | MakePolyCls_alt _ -> raise @@ Closure_bug "alt form appear in replace"

  let rec to_alt ids = function
    | Let (x, Coercion (CId _), f) -> 
      let f = to_alt (V.add x ids) f in
      if V.mem x (fv f) then raise @@ Closure_error "to_alt: id appear"
      else f
    | Let (x, CSeq (k1, k2), f) ->
      begin match V.mem k1 ids, V.mem k2 ids with
      | true, true -> 
        let f = to_alt (V.add x ids) f in
        if V.mem x (fv f) then raise @@ Closure_error "to_alt: id appear"
        else f
      | true, false -> to_alt ids @@ replace_var x k2 f
      | false, true -> to_alt ids @@ replace_var x k1 f
      | false, false -> Let (x, CSeq (k1, k2), to_alt ids f)
      end
    | Let (x, CApp (y, k), f) when V.mem k ids -> to_alt ids (replace_var x y f)
    | Let (x, f1, f2) -> Let (x, to_alt ids f1, to_alt ids f2)
    | IfEq (x, y, f1, f2) -> IfEq (x, y, to_alt ids f1, to_alt ids f2)
    | IfLte (x, y, f1, f2) -> IfLte (x, y, to_alt ids f1, to_alt ids f2)
    | AppCls (x, (y, k)) when V.mem k ids -> AppCls_alt (x, y)
    | AppDir (l, (y, k)) when V.mem k ids -> AppDir_alt (l, y)
    | CApp (x, k) when V.mem k ids -> Var x
    | MakeCls (x, cls, f) -> MakeCls_alt (x, cls, to_alt ids f)
    | MakeLabel (x, l, f) -> MakeLabel_alt (x, l, to_alt ids f)
    | MakePolyCls (x, cls, ftvs, f) -> MakePolyCls_alt (x, cls, ftvs, to_alt ids f)
    | MakePolyLabel (x, l, ftvs, f) -> MakePolyLabel_alt (x, l, ftvs, to_alt ids f)
    | AppCls_alt _ | AppDir_alt _ | MakeLabel_alt _ | MakeCls_alt _ | MakePolyLabel_alt _ | MakePolyCls_alt _ -> raise @@ Closure_bug "alt form appear in replace"
    | f -> f

  let rec alt_funs = function
    | h :: t -> 
      begin match h with
      | Fundef {name = l; tvs = (tvs, n); arg = (y, k); formal_fv = ids; body = f } -> 
        Fundef_alt {name = l; tvs = (tvs, n); arg = y; formal_fv = ids; body = to_alt (V.singleton k) f } ::
        Fundef {name = l; tvs = (tvs, n); arg = (y, k); formal_fv = ids; body = to_alt V.empty f } ::
        (alt_funs t)
      | Fundef_alt _ -> raise @@ Closure_bug "alt form appear in alt_funs"
      end
    | [] -> []
end

let toCls_program p alt =
  toplevel := []; tvset := TV.empty;
  let f = KNorm.toCls_exp KNorm.venv [] p in
  if alt then Syntax.Cls.Prog (!tvset, Cls.alt_funs !toplevel, Cls.to_alt Syntax.Cls.V.empty f)
  else Syntax.Cls.Prog (!tvset, List.rev !toplevel, f)

(*
let quad:int->int = fun (x:int) ->
  let dbl:int->int = fun (_var16:int) ->
    _var16 + _var16
  in (let _var14:int = dbl x in dbl _var14)
in (let _var15:int = 123 in quad _var15)

toplevel:=[]
g [] [] e
  LetFunExp(_,quad,int->int,[],[x,int],e1=LetExp(),e2=LetExp())
  env'=[quad,int->int], known'=[quad]
  g [x,int;quad,int->int] [quad] e1
    LetFunExp(_,dbl,int->int,[],[_var16,int],e1=BinOp(),e2=LetExp())
    env'=[dbl,int->int;x,int;quad,int->int], known'=[dbl,quad]
    g [_var16,int;dbl,int->int;x,int;quad,int->int] [dbl,quad] e1
    e1'=BinOp(_,Plus,_var16,_var16)
    zs=[_var16]-[_var16]=[]
    known'=known', e1'=e1'
    zs=[], zts=[]
    toplevel:={name=(quad,int->int);args=[_var16,int];formal_fv=[];body=e1'}::[]
    g [dbl,int->int;x,int;quad,int->int] [dbl,quad] e2
      LetExp(_,_var14,int,[],e1=AppExp(),e2=AppExp())
      g env known e1=AppDir(_,L(dbl),x)
      g env known e2=AppDir(_,L(dbl),_var14)
    e2'=Let(_,_var14,int,[],AppDir(_,L(dbl),x),AppDir(_,L(dbl),_var14))
  e1'=Let(_,_var14,int,[],AppDir(_,L(dbl),x),AppDir(_,L(dbl),_var14))
  zs=[x]-[x]=[] (*_var14はLetのfv、dblはAppDirの一つ目なので、含まれない*)
  known'=known', e1'=e1'
  zs=[],zts=[]
  toplevel:={name=(dbl,int->int);args=[x,int];formal_fv=[];body=e1'}::!toplevel
  g [quad,int->int] [quad] e2
    LetExp(_,_var15,[],e1=IConst(),e2=AppExp())
    g env known e1=Int(_,123)
    g env known e2=AppDir(_,L(quad),_var15)
  e2'=Let(_,_var15,[],Int(_,123),AppDir(_,L(quad),_var15))
e'=Let(_,_var15,[],Int(_,123),AppDir(_,L(quad),_var15))

let make_adder = fun (x:int) -> 
  let adder = fun (y:int) -> 
    x + y 
  in adder 
in (let _var17 = 3 in (let _var18 = make_adder _var17 in (let _var19 = 7 in _var18 _var19)))

toplevel:=[]
g [] [] e
  LetExp(_,make_adder,[],FunExp(_,x,int,e1=LetExp()),e2=LetExp())
  env'=[make_adder,int->int], known'=[make_adder]
  g [x,int;make_adder,int->int] [make_adder] e1
    LetExp(_,adder,[],FunExp(_,y,int,e1=BinOp()),e2=Var())
    env'=[adder,int->int;x,int;make_adder,int->int], known'=[adder,make_adder]
    g [y,int;adder,int->int;x,int;make_adder,int->int] [adder,make_adder] e1
    e1'=BinOp(_,Plus,x,y)
    zs=[x,y]-[y]=[x]
    g [y,int;adder,int->int;x,int;make_adder,int->int] [make_adder] e1
    e1'=BinOp(_,Plus,x,y)
    known'=known, e1'=e1'
    zs=[x,y]-[adder,y]=[x], zts=[x,int]
    toplevel:={name=(adder,int->int);args=[y,int];formal_fv=[x,int];body=e1'}::[]
    g [adder,int->int;x,int;make_adder,int->int] [make_adder] e2
    e2'=Var(_,adder)
  e1'=MakeCls((adder,int->int),{entry=L(adder);actual_fv=[x]},Var(_,adder))
  zs=[x]-[x]=[] (*adderはMakeClsのfvなので、含まれない*)
  known'=known', e1'=e1'
  zs=[],zts=[]
  toplevel:={name=(make_adder,int->int);args=[x,int];formal_fv=[];body=e1'}::!toplevel
  g [quad,int->int] [quad] e2
    LetExp(_,_var15,[],e1=IConst(),e2=AppExp())
    g env known e1=Int(_,123)
    g env known e2=AppDir(_,quad,_var15)
  e2'=Let(_,_var15,[],Int(_,123),AppDir(_,quad,_var15))
e'=Let(_,_var15,[],Int(_,123),AppDir(_,quad,_var15))
*)
      


  
