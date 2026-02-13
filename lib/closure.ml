open Syntax
open Static_manage

exception Closure_bug of string
exception Closure_error of string

let toplevel = ref []

(* let tvset = ref TV.empty *)

let ranges = ref []

(* let crcs = ref [] *)

let range_id r = 
  let rec itr n l = match l with
  | h :: t -> if h = r then n else itr (n + 1) t
  | [] -> ranges := !ranges @ [r]; n
  in itr 0 !ranges

module KNorm = struct
  open Syntax.KNorm

  let rec exist_tv l1 l2 = match l2 with
    | h :: t -> if List.mem h l1 then true else exist_tv l1 t
    | [] -> false
  
  let rec ty_tv tvs u = match u with
    | TyInt | TyBool | TyUnit | TyDyn | TyFun (TyDyn, TyDyn) | TyList TyDyn as u -> (u, fun x -> x)
    | TyVar tv -> if not (List.mem tv tvs) then (StaticTyManager.register u; (u, fun x -> x)) else (u, fun x -> x)
    | TyFun (u1, u2) ->
      let u1, ufun1 = ty_tv tvs u1 in
      let u2, ufun2 = ty_tv tvs u2 in
      if not (exist_tv (TV.elements (Syntax.ftv_ty u1)) tvs) && not (exist_tv (TV.elements (Syntax.ftv_ty u2)) tvs) then begin
        StaticTyManager.register u;
        (u, fun x -> x)
      end else 
        let newu = Typing.fresh_tyvar () in
        let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyFun (u1, u2)); (i, u)
        | _ -> raise @@ Closure_bug "not tyvar was created"
        in
        (newu, fun x -> ufun1 (ufun2 (Cls.SetTy (newtv, x))))
    | TyList u' -> 
      let u', ufun' = ty_tv tvs u' in
      if not (exist_tv (TV.elements (Syntax.ftv_ty u)) tvs) then begin
        StaticTyManager.register u;
        (u, fun x -> x)
      end else
        let newu = Typing.fresh_tyvar () in
        let newtv = match newu with
          | TyVar (i, u) -> u := Some (TyList u'); (i, u)
          | _ -> raise @@ Closure_bug "not tyvar was created"
        in
        (newu, fun x -> ufun' (Cls.SetTy (newtv, x)))

  let ta_tv tvs = function
    | Ty u -> let (u, f) = ty_tv tvs u in (Ty u, f)
    | TyNu -> (TyNu, fun x -> x)

  let tyvar_to_tyarg tvs = 
    let rec ttt l r = match l with
    | tv :: t -> ttt t ((Ty (TyVar tv)) :: r)
    | [] -> r
  in ttt (List.rev tvs) []

  let rec toCls_crc tvs c = match c with 
    | CId _ -> Cls.Id
    (* | CFail (_, (r, p), _) -> Cls.Fail (range_id r, p) *)
    (* | CSeq (CProj (g, (r, p)), CSeq (c, CInj g')) -> Cls.SeqProjInj (g, (range_id r, p), toCls_crc tvs c, g') *)
    | CSeq (CProj (g, (r, p)), c) -> Cls.SeqProj (g, (range_id r, p), toCls_crc tvs c)
    | CSeq (c, CInj g) -> Cls.SeqInj (toCls_crc tvs c, g)
    | CTvInj (tv, (r, p)) -> 
      if not (List.mem tv tvs) then StaticTyManager.register (TyVar tv);
      Cls.TvInj (tv, (range_id r, p))
    | CTvProj (tv, (r, p)) -> 
      if not (List.mem tv tvs) then StaticTyManager.register (TyVar tv);
      Cls.TvProj (tv, (range_id r, p))
    (* | CTvProjInj (tv, (r, p)) ->
      if not (List.mem tv tvs) then StaticTyManager.register (TyVar tv);
      Cls.TvProjInj (tv, (range_id r, p)) *)
    | CFun (c1, c2) -> Cls.Fun (toCls_crc tvs c1, toCls_crc tvs c2)
    | CList c -> Cls.List (toCls_crc tvs c)
    | _ -> raise @@ Closure_bug "bad coercion"

  let rec toCls_exp known tvs = function
    | Var x -> Cls.Var x
    | IConst i -> Cls.Int i
    | Add (x, y) -> Cls.Add (x, y)
    | Sub (x, y) -> Cls.Sub (x, y)
    | Mul (x, y) -> Cls.Mul (x, y)
    | Div (x, y) -> Cls.Div (x, y)
    | Mod (x, y) -> Cls.Mod (x, y)
    | Nil -> Cls.Nil
    | Cons (x, y) -> Cls.Cons (x, y) 
    | Hd x -> Cls.Hd x
    | Tl x -> Cls.Tl x
    | MatchExp (x, ms) -> Cls.Match (x, List.map (fun (mf, f) -> mf, toCls_exp known tvs f) ms)
    | IfEqExp (x, y, f1, f2) -> Cls.IfEq (x, y, toCls_exp known tvs f1, toCls_exp known tvs f2)
    | IfLteExp (x, y, f1, f2) -> Cls.IfLte (x, y, toCls_exp known tvs f1, toCls_exp known tvs f2)
    | AppDExp (x, (y, z)) when V.mem x known -> Cls.AppDDir (Cls.to_label x, (y, z))
    | AppDExp (x, (y, z)) -> Cls.AppDCls (x, (y, z))
    | AppMExp (x, y) when V.mem x known -> Cls.AppMDir (Cls.to_label x, y)
    | AppMExp (x, y) -> Cls.AppMCls (x, y)
    | AppTy (x, _, tas) -> 
      let uandf = List.map (ta_tv tvs) tas in
      let rec destruct_uandf l ru rf = match l with
        | (u, f) :: t -> destruct_uandf t (u::ru) (fun x -> rf (f x))
        | [] -> ru, rf 
      in let us, f = destruct_uandf (List.rev uandf) [] (fun x -> x) in
      f (Cls.AppTy (x, List.length tas + List.length tvs, us))
    | CastExp (x, u1, u2, (r, p)) -> 
      let u1, udeclfun1 = ty_tv tvs u1 in 
      let u2, udeclfun2 = ty_tv tvs u2 in 
      udeclfun1 (udeclfun2 (Cls.Cast (x, u1, u2, (range_id r, p))))
    | CAppExp (x, y) -> Cls.CApp (x, y)
    | CSeqExp (x, y) -> Cls.CSeq (x, y)
    | CoercionExp c -> Cls.Coercion (toCls_crc tvs c)
    | LetExp (x, f1, f2) -> 
      let f1 = toCls_exp known tvs f1 in
      let f2 = toCls_exp known tvs f2 in
      Cls.Let (x, f1, f2)
    | LetRecSExp (x, tvs', (y, z), f1, f2) ->
      let k_fv = V.remove x @@ V.remove y @@ V.remove z @@ fv_exp f1 in
      let new_tvs = tvs' @ tvs in
      let known', f1' =
        if not (V.is_empty k_fv) || List.length new_tvs != 0 then
          let f1' = toCls_exp known new_tvs f1 in
          known, f1'
        else 
          let toplevel_backup = !toplevel in
          let staticTy_backup = StaticTyManager.save () in
          let ranges_backup = !ranges in
          let known' = V.add x known in
          let f1' = toCls_exp known' new_tvs f1 in
          let zs = V.diff (Cls.fv_exp f1') (V.of_list [y; z]) in
          if V.is_empty zs (*&& List.length new_tvs = 0*) then 
            known', f1'
          else begin
            toplevel := toplevel_backup; StaticTyManager.restore staticTy_backup; ranges := ranges_backup;
            (* Format.fprintf Format.err_formatter "backtracking %s\n" x; *)
            let f1' = toCls_exp known new_tvs f1 in
            known, f1'
          end
      in
      let zs = V.elements (V.diff (Cls.fv_exp f1') (V.of_list [x; y; z])) in
      (* let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in *)
      let fundef = Cls.FundefD { name = Cls.to_label x; tvs = (new_tvs, List.length tvs'); arg = (y, z); formal_fv = zs; body = f1' } in
      if not @@ List.mem fundef !toplevel then toplevel := fundef :: !toplevel;
      let f2' = toCls_exp known' tvs f2 in
      if V.mem x (Cls.fv_exp f2') then
        if List.length zs = 0 && List.length new_tvs = 0 then Cls.MakeLabel (x, Cls.to_label x, f2')
        else if List.length new_tvs = 0 then Cls.MakeCls (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, f2')
        else if List.length zs = 0 then Cls.MakePolyLabel (x, Cls.to_label x, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
        else Cls.MakePolyCls (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
      else f2'
    | LetRecAExp _ -> raise @@ Closure_bug "shouldn't apper alt in closure"
    | LetRecBExp (x, tvs', y, f1, f2) ->
      let k_fv = V.remove x @@ V.remove y @@ fv_exp f1 in
      let new_tvs = tvs' @ tvs in
      let known', f1' =
        if not (V.is_empty k_fv) || List.length new_tvs != 0 then
          let f1' = toCls_exp known new_tvs f1 in
          known, f1'
        else 
          let toplevel_backup = !toplevel in
          let staticTy_backup = StaticTyManager.save () in
          let ranges_backup = !ranges in
          let known' = V.add x known in
          let f1' = toCls_exp known' new_tvs f1 in
          let zs = V.diff (Cls.fv_exp f1') (V.singleton y) in
          if V.is_empty zs (*&& List.length new_tvs = 0*) then 
            known', f1'
          else begin
            toplevel := toplevel_backup; StaticTyManager.restore staticTy_backup; ranges := ranges_backup;
            (* Format.fprintf Format.err_formatter "backtracking %s\n" x; *)
            let f1' = toCls_exp known new_tvs f1 in
            known, f1'
          end
      in
      let zs = V.elements (V.diff (Cls.fv_exp f1') (V.of_list [x; y])) in
      (* let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in *)
      let fundef = Cls.FundefM { name = Cls.to_label x; tvs = (new_tvs, List.length tvs'); arg = y; formal_fv = zs; body = f1' } in
      if not @@ List.mem fundef !toplevel then toplevel := fundef :: !toplevel;
      let f2' = toCls_exp known' tvs f2 in
      if V.mem x (Cls.fv_exp f2') then
        if List.length zs = 0 && List.length new_tvs = 0 then Cls.MakeLabel (x, Cls.to_label x, f2')
        else if List.length new_tvs = 0 then Cls.MakeCls (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, f2')
        else if List.length zs = 0 then Cls.MakePolyLabel (x, Cls.to_label x, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
        else Cls.MakePolyCls (x, { Cls.entry = Cls.to_label x; Cls.actual_fv = zs }, { ftvs = tyvar_to_tyarg tvs; offset = List.length tvs' }, f2')
      else f2'

  let toCls kf known = 
    let f = match kf with Exp f -> f | _ -> raise @@ Closure_bug "kf is not exp" in
    toplevel := []; StaticTyManager.clear (); ranges := [];
    toCls_exp known [] f
end

module Cls = struct
  open Syntax.Cls

  let rec replace_var vx vy f = 
    let replace x = if x = vx then vy else x in
    match f with
    | Var x -> Var (replace x)
    | Int i -> Int i
    | Nil -> Nil
    | Add (x, y) -> Add (replace x, replace y)
    | Sub (x, y) -> Sub (replace x, replace y)
    | Mul (x, y) -> Mul (replace x, replace y)
    | Div (x, y) -> Div (replace x, replace y)
    | Mod (x, y) -> Mod (replace x, replace y)
    | Cons (x, y) -> Cons (replace x, replace y)
    | Hd x -> Hd (replace x)
    | Tl x -> Tl (replace x)
    | IfEq (x, y, f1, f2) -> IfEq (replace x, replace y, replace_var vx vy f1, replace_var vx vy f2)
    | IfLte (x, y, f1, f2) -> IfLte (replace x, replace y, replace_var vx vy f1, replace_var vx vy f2)
    | Match (x, ms) -> Match (replace x, List.map (fun (mf, f) -> mf, replace_var vx vy f) ms)
    | AppTy (x, n, tas) -> AppTy (replace x, n, tas)
    | AppDCls (x, (y, k)) -> AppDCls (replace x, (replace y, replace k))
    | AppDDir (l, (y, k)) -> AppDDir (to_label (replace (to_id l)), (replace y, replace k))
    | CApp (x, k) -> CApp (replace x, replace k)
    | CSeq (k1, k2) -> CSeq (replace k1, replace k2)
    | Coercion c -> Coercion c
    | Let (x, f1, f2) -> Let (x, replace_var vx vy f1, replace_var vx vy f2)
    | MakeCls (x, {entry = l; actual_fv = fvs}, f) -> MakeCls (x, {entry=to_label (replace (to_id l)); actual_fv = List.map replace fvs}, replace_var vx vy f)
    | MakeLabel (x, l, f) -> MakeLabel (x, to_label (replace (to_id l)), replace_var vx vy f)
    | MakePolyCls (x, {entry = l; actual_fv = fvs}, ftvs, f) -> MakePolyCls (x, {entry=to_label (replace (to_id l)); actual_fv = List.map replace fvs}, ftvs, replace_var vx vy f)
    | MakePolyLabel (x, l, ftvs, f) -> MakePolyLabel (x, to_label (replace (to_id l)), ftvs, replace_var vx vy f)
    | SetTy _ | Insert _ -> raise @@ Closure_bug "SetTy or Insert appear in replace"
    | AppMCls _ | AppMDir _ -> raise @@ Closure_bug "AppM appear in replace"
    | Cast _ -> raise @@ Closure_bug "Cast appear in replace"

  let rec to_alt ids = function
    | Let (x, Coercion Id, f) -> 
      let f = to_alt (V.add x ids) f in
      if V.mem x (fv_exp f) then raise @@ Closure_error "to_alt: id appear"
      else f
    | Let (x, CSeq (k1, k2), f) ->
      begin match V.mem k1 ids, V.mem k2 ids with
      | true, true -> 
        let f = to_alt (V.add x ids) f in
        if V.mem x (fv_exp f) then raise @@ Closure_error "to_alt: id appear"
        else f
      | true, false -> to_alt ids @@ replace_var x k2 f
      | false, true -> to_alt ids @@ replace_var x k1 f
      | false, false -> Let (x, CSeq (k1, k2), to_alt ids f)
      end
    | Let (x, CApp (y, k), f) when V.mem k ids -> to_alt ids (replace_var x y f)
    | Let (x, f1, f2) -> Let (x, to_alt ids f1, to_alt ids f2)
    | IfEq (x, y, f1, f2) -> IfEq (x, y, to_alt ids f1, to_alt ids f2)
    | IfLte (x, y, f1, f2) -> IfLte (x, y, to_alt ids f1, to_alt ids f2)
    | Match (x, ms) -> Match (x, List.map (fun (mf, f) -> mf, to_alt ids f) ms)
    | AppDCls (x, (y, k)) when V.mem k ids -> AppMCls (x, y)
    | AppDDir (l, (y, k)) when V.mem k ids -> AppMDir (l, y)
    | CApp (x, k) when V.mem k ids -> Var x
    | MakeCls (x, cls, f) -> MakeCls (x, cls, to_alt ids f)
    | MakeLabel (x, l, f) -> MakeLabel (x, l, to_alt ids f)
    | MakePolyCls (x, cls, ftvs, f) -> MakePolyCls (x, cls, ftvs, to_alt ids f)
    | MakePolyLabel (x, l, ftvs, f) -> MakePolyLabel (x, l, ftvs, to_alt ids f)
    | AppMCls _ | AppMDir _ -> raise @@ Closure_bug "AppM appear in to_alt"
    | Cast _ -> raise @@ Closure_bug "Cast appear in to_alt"
    | f -> f

  let rec alt_funs = function
    | h :: t -> 
      begin match h with
      | FundefD {name = l; tvs = (tvs, n); arg = (y, k); formal_fv = ids; body = f } -> 
        FundefM {name = l; tvs = (tvs, n); arg = y; formal_fv = ids; body = to_alt (V.singleton k) f } ::
        FundefD {name = l; tvs = (tvs, n); arg = (y, k); formal_fv = ids; body = to_alt V.empty f } ::
        (alt_funs t)
      | _ -> raise @@ Closure_bug "alt form appear in alt_funs"
      end
    | [] -> []

  let altCls p alt =
    if alt then Prog (!ranges, alt_funs !toplevel, to_alt V.empty p)
    else Prog (!ranges, List.rev !toplevel, p)
end

let toCls_program kf venv ~alt =
  let p = KNorm.toCls kf venv in
  let p = Cls.altCls p alt in
  p

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
      


  
