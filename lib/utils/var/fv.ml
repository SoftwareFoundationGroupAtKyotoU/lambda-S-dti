open Syntax

let rec fv_matchform = function
  | MatchILit _ | MatchBLit _ | MatchULit | MatchWild | MatchNil -> V.empty
  | MatchVar x -> V.singleton x
  | MatchCons (mf1, mf2) -> V.big_union [fv_matchform mf1; fv_matchform mf2]
  | MatchTuple mfs -> V.big_union (List.map fv_matchform mfs)

module KNorm = struct
  open Syntax.KNorm

  let rec fv_exp = function
    | Var x | Hd x | Tl x  | Tget (x, _) | Ref (x, _) | Deref (x, _) -> V.singleton x
    | IConst _ | Nil -> V.empty
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) | Cons (x, y) | Subst (x, y, _) | MakeArray (x, y, _) | Get (x, y, _) -> V.of_list [x; y]
    | Put (x, y, z, _) -> V.of_list [x; y; z]
    | Tuple xs -> V.of_list xs
    | IfEqExp (x, y, f1, f2) | IfLteExp (x, y, f1, f2) -> V.big_union [V.of_list [x; y]; fv_exp f1; fv_exp f2]
    | MatchExp (x, ms) -> 
      V.big_union (V.singleton x :: List.map (fun (mf, f) -> V.union (fv_matchform mf) (fv_exp f)) ms)
    | AppTy (x, _, _) -> V.singleton x
    | AppMExp (x, y) -> V.of_list [x; y]
    | AppDExp (x, (y, z)) -> V.of_list [x; y; z]
    | CastExp (x, _, _, _) -> V.singleton x
    | CAppExp (x, y) -> V.of_list [x; y]
    | CCompExp (x, y) -> V.of_list [x; y]
    | CoercionExp _ -> V.empty
    | LetExp (x, f1, f2) -> V.union (fv_exp f1) (V.remove x (fv_exp f2))
    | LetFunExp (x, _, fd, f2) -> V.union (V.remove x @@ fv_fd fd) (V.remove x @@ fv_exp f2)
  and fv_fd = function
    | FunB (x, f) -> V.remove x @@ fv_exp f
    | FunS ((x, y), f) -> V.remove x @@ V.remove y @@ fv_exp f
    | FunDual ((x, y), (f1, f2)) -> V.remove x @@ V.remove y @@ V.union (fv_exp f1) (fv_exp f2)
    | FunTy f -> fv_exp f
end

module Cls = struct
  open Syntax.Cls

  let rec fv_exp = function
    | Var x | Hd x | Tl x | Tget (x, _) | Ref (x, _) | Deref (x, _) -> V.singleton x
    | Int _ | Nil -> V.empty
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) | Cons (x, y) | Subst (x, y, _) | MakeArray (x, y, _) | Get (x, y, _) -> V.of_list [x; y]
    | Put (x, y, z, _) -> V.of_list [x; y; z]
    | Tuple xs -> V.of_list xs
    | IfEq (x, y, f1, f2) | IfLte (x, y, f1, f2) -> V.big_union [V.of_list [x; y]; fv_exp f1; fv_exp f2]
    | Match (x, ms) -> 
      V.big_union (V.singleton x :: List.map (fun (mf, f) -> V.union (fv_matchform mf) (fv_exp f)) ms)
    | AppTy (x, _, _, _) -> V.singleton x
    | AppTyFun (x, _, _, _) -> V.singleton x
    | SetTy (_, f) -> fv_exp f
    | AppDDir (_, (y, z)) -> V.of_list [y; z]
    | AppDCls (x, (y, z)) -> V.of_list [x; y; z]
    | AppMDir (_, y) -> V.singleton y
    | AppMCls (x, y) -> V.of_list [x; y]
    | Cast (x, _, _, _) -> V.singleton x
    | CApp (x, y) -> V.of_list [x; y]
    | CComp (x, y) -> V.of_list [x; y]
    | Coercion _ -> V.empty
    | MakeCls (x, { fvs; _ }, f) -> V.remove x (V.union (V.of_list fvs) (fv_exp f))
    | MakeTyCls (x, { fvs; _ }, f) -> V.remove x (V.union (V.of_list fvs) (fv_exp f))
    | Let (x, c, f) -> V.union (fv_exp c) (V.remove x (fv_exp f))
end