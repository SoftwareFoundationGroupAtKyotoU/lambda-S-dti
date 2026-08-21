open Syntax
open Syntax.KNorm
open Fv.KNorm

exception Closure_bug of string
exception Closure_error of string

let toplevel = ref []

let rec toCls_exp known tvs args funty = function
  | Var x -> Cls.Var x
  | IConst i -> Cls.Int i
  | FConst f -> Cls.Float f
  | BinOp (x, op, y) -> Cls.BinOp (x, op, y)
  | Nil -> Cls.Nil
  | Cons (x, y) -> Cls.Cons (x, y)
  | Tuple xs -> Cls.Tuple xs
  | Hd x -> Cls.Hd x
  | Tl x -> Cls.Tl x
  | Tget (x, i) -> Tget (x, i)
  | Ref (x, u) -> Cls.Ref (x, u)
  | Deref (x, u) -> Cls.Deref (x, u)
  | Subst (x, y, u) -> Cls.Subst (x, y, u)
  | MakeArray (x, y, u) -> Cls.MakeArray (x, y, u)
  | Get (x, y, u) -> Cls.Get (x, y, u)
  | Put (x, y, z, u) -> Cls.Put (x, y, z, u)
  | Length x -> Cls.Length x
  | MatchExp (x, ms) -> Cls.Match (x, List.map (fun (mf, f) -> mf, toCls_exp known tvs args funty f) ms)
  | IfExp (x, f1, f2) -> Cls.If (x, toCls_exp known tvs args funty f1, toCls_exp known tvs args funty f2)
  | AppDExp (x, (y, z)) when V.mem x known -> Cls.AppDDir (Cls.to_label x, (y, z))
  | AppDExp (x, (y, z)) -> Cls.AppDCls (x, (y, z))
  | AppMExp (x, y) when V.mem x known -> Cls.AppMDir (Cls.to_label x, y)
  | AppMExp (x, y) -> Cls.AppMCls (x, y)
  | AppTy (x, _, tas) -> 
    let zs, outer_tvs_len = Environment.find x args in
    if V.mem x funty then Cls.AppTyFun (x, List.length zs, tas, outer_tvs_len)
    else Cls.AppTy (x, List.length zs, tas, outer_tvs_len)
  | CastExp (x, u1, u2, (r, p)) -> Cast (x, u1, u2, (r, p))
  | CAppExp (x, y) -> Cls.CApp (x, y)
  | CCompExp (x, y) -> Cls.CComp (x, y)
  | CoercionExp c -> Cls.Coercion c
  | LetExp (x, f1, f2) -> 
    let f1 = toCls_exp known tvs args funty f1 in
    let f2 = toCls_exp known tvs args funty f2 in
    Cls.Let (x, f1, f2)
  | LetFunExp (x, tvs', fd, f2) ->
    let v_arg, f1 = match fd with
      | FunB (y, f1) -> V.singleton y, f1
      | FunS ((y, z), f1) -> V.of_list [y; z], f1
      | FunDual _ -> raise @@ Closure_bug "shouldn't apper alt in closure"
      | FunTy f1 -> V.empty, f1
    in
    let k_fv = V.remove x @@ V.diff (fv_exp f1) v_arg in
    let new_tvs = tvs' @ tvs in
    let known', f1' = (* xはknownな関数かを調べる *)
      if not (V.is_empty k_fv) || List.length new_tvs != 0 then
        (* f1の中に自由変数がある、もしくは型引数が空でなければ、xをknownに入れず、f1をknownでclosure変換する *)
        let f1' = toCls_exp known new_tvs args funty f1 in
        known, f1'
      else 
        (* 関数xをknownに入れてよいか確かめるため、backupを作成 *)
        let toplevel_backup = !toplevel in
        let known' = V.add x known in (* xをknownに入れてclosure変換してみる *)
        let f1' = toCls_exp known' new_tvs args funty f1 in
        let zs = V.diff (Fv.Cls.fv_exp f1') v_arg in
        if V.is_empty zs (*&& List.length new_tvs = 0*) then 
          (* closure変換後のf1に自由変数がなければ、xをknownに入れて返す *)
          known', f1'
        else begin
          (* closure変換後のf1に自由変数があれば、xをknownに入れず、closure変換をやり直す *)
          toplevel := toplevel_backup;
          (* Format.fprintf Format.err_formatter "backtracking %s\n" x; *)
          let f1' = toCls_exp known new_tvs args funty f1 in
          known, f1'
        end
    in
    let zs = V.elements (V.diff (Fv.Cls.fv_exp f1') (V.union (V.singleton x) v_arg)) in
    (* let zts = List.map (fun z -> (z, Environment.find z tyenv')) zs in *)
    let fundef, funty = match fd with
      | FunB (y, _) -> Cls.FundefM { name = Cls.to_label x; arg = y; vs = zs; tvs = new_tvs; body = f1' }, funty
      | FunS ((y, z), _) -> Cls.FundefD { name = Cls.to_label x; arg = (y, z); vs = zs; tvs = new_tvs; body = f1' }, funty
      | FunDual _ -> raise @@ Closure_bug "shouldn't apper alt in closure"
      | FunTy _ -> Cls.FundefTy { name = Cls.to_label x; vs = zs; tvs = new_tvs; body = f1' }, V.add x funty
    in
    if not @@ List.mem fundef !toplevel then toplevel := fundef :: !toplevel;
    let f2' = toCls_exp known' tvs (Environment.add x (zs, List.length tvs) args) funty f2 in
    if V.mem x (Fv.Cls.fv_exp f2') then match fd with
      | FunTy _ -> Cls.MakeTyCls (x, { entry = Cls.to_label x; fvs = zs; offset = List.length tvs'; ftvs = tvs }, f2')
      | _ -> Cls.MakeCls (x, { entry = Cls.to_label x; fvs = zs;  offset = List.length tvs'; ftvs = tvs }, f2')
    else f2'

let toCls known args kf = 
  let f = match kf with Exp f -> f | _ -> raise @@ Closure_bug "kf is not exp" in
  toplevel := [];
  let p = toCls_exp known [] args V.empty f in
  Cls.Prog (List.rev !toplevel, p)