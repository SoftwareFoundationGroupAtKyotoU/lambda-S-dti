open Syntax
open Format

exception KNormal_error of string
exception KNormal_bug of string

let subst_type = Typing.subst_type

(* generate variable string for insert_let *)
let counter = ref 0
let genvar x = 
  let v = !counter in
  counter := v + 1;
  Printf.sprintf "%s_%d" x !counter

module LS1 = struct
  open Syntax.LS1

  (* alpha : 変数の名前が被らないように付け替える *)
  let rec alpha_exp idenv = function
    | Var (x, tas) -> Var (Environment.find x idenv, tas)
    | IConst _ | BConst _ | UConst as f -> f
    | BinOp (op, f1, f2) -> BinOp (op, alpha_exp idenv f1, alpha_exp idenv f2)
    | IfExp (f1, f2, f3) ->
      IfExp (alpha_exp idenv f1, alpha_exp idenv f2, alpha_exp idenv f3)
    | FunExp ((x, u), k, f) -> 
      let newx = genvar x in
      let newk = genvar k in
      FunExp ((newx, u), newk, alpha_exp (Environment.add x newx (Environment.add k newk idenv)) f)
    | FixExp _ -> raise @@ KNormal_error "FixExp should not be alpha_exp's argument"
    | AppExp (f1, f2, f3) -> AppExp (alpha_exp idenv f1, alpha_exp idenv f2, alpha_exp idenv f3)
    | CAppExp (f1, f2) -> CAppExp (alpha_exp idenv f1, alpha_exp idenv f2)
    | CSeqExp (f1, f2) -> CSeqExp (alpha_exp idenv f1, alpha_exp idenv f2)
    | LetExp (x, tvs, FixExp ((x', y, u1, u2), k, f1), f2) -> 
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      let newk = genvar k in
      LetExp (newx, tvs, FixExp ((newx, newy, u1, u2), newk, alpha_exp (Environment.add y newy (Environment.add k newk idenv)) f1), alpha_exp idenv f2)
    | LetExp (x, tvs, f1, f2) -> 
      let newx = genvar x in
      LetExp (newx, tvs, alpha_exp idenv f1, alpha_exp (Environment.add x newx idenv) f2)
    | CoercionExp c -> CoercionExp c
    | AppExp_alt _ | FunExp_alt _ | FixExp_alt _ -> raise @@ KNormal_bug "alternative translation yet"

  let alpha_program idenv = function
    | Exp f -> Exp (alpha_exp idenv f), idenv
    | LetDecl (x, tvs, FixExp ((x', y, u1, u2), k, f)) ->
      assert (x = x');
      let newx = genvar x in
      let idenv = Environment.add x newx idenv in
      let newy = genvar y in
      let newk = genvar k in
      LetDecl (newx, tvs, FixExp ((newx, newy, u1, u2), newk, alpha_exp (Environment.add y newy idenv) f)), idenv
    | LetDecl (x, tvs, f) -> 
      let newx = genvar x in
      LetDecl (newx, tvs, alpha_exp idenv f), Environment.add x newx idenv

  let insert_let f (k: id -> KNorm.exp) = match f with
    | KNorm.Var x -> k x
    | _ as f -> 
      let x = genvar "_var" in
      let f' = k x in (* Var以外に自由な型変数への代入などは存在しないので、ここは[]で大丈夫 *)
      KNorm.LetExp (x, f, f') (* todo:考える。とりあえず[] *)
      (*多分大丈夫、applicationにしか不要で、(fun x...) vなら既に代入済み、(fun (x:?)...) vならcast済み*)

  let rec k_normalize_exp tvsenv = function
    | Var (x, tas) -> 
      let tvs = Environment.find x tvsenv in 
      if List.length tas = 0 && List.length tvs = 0 then KNorm.Var x
      else if List.length tas = List.length tvs then KNorm.AppTy (x, tvs, tas)
      else raise @@ KNormal_bug "tas and tvs don't have same length"
    | IConst i -> KNorm.IConst i
    | BConst b -> let i = if b then 1 else 0 in KNorm.IConst i
    | UConst -> KNorm.UConst
    | BinOp (op, f1, f2) as f -> begin match op with
      | Plus -> 
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Add (x, y)
      | Minus ->
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Sub (x, y)
      | Mult -> 
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Mul (x, y)
      | Div -> 
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Div (x, y)
      | Mod -> 
        let f1 = k_normalize_exp tvsenv f1 in
        let f2 = k_normalize_exp tvsenv f2 in
        insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.Mod (x, y)
      | _ -> k_normalize_exp tvsenv (IfExp (f, BConst true, BConst false))
      end
    | IfExp (f1, f2, f3) ->
      let f2' = k_normalize_exp tvsenv f2 in
      let f3' = k_normalize_exp tvsenv f3 in
      begin match f1 with
        | BinOp (op, f1, f2) -> 
          let f1 = k_normalize_exp tvsenv f1 in
          let f2 = k_normalize_exp tvsenv f2 in
          begin match op with
            | Eq -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfEqExp (x, y, f2', f3')
            | Neq -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfEqExp (x, y, f3', f2')
            | Lt -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfLteExp (x, y, IfEqExp (x, y, f3', f2'), f3')
            | Lte -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfLteExp (x, y, f2', f3')
            | Gt -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfLteExp (x, y, f3', f2')
            | Gte -> insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> IfLteExp (x, y, IfEqExp (x, y, f2', f3'), f2')
            | _ -> raise @@ KNormal_bug "if-cond type should bool"
          end
        | Var _ | BConst _ | IfExp _ | AppExp _ | AppExp_alt _ | LetExp _ | CAppExp _ as f ->
          let f = k_normalize_exp tvsenv f in 
          insert_let f @@ fun x -> insert_let (KNorm.IConst 1) @@ fun y -> IfEqExp (x, y, f2', f3')
        | IConst _ | UConst | FunExp _ | FixExp _ | FunExp_alt _ | FixExp_alt _ | CSeqExp _ | CoercionExp _ -> raise @@ KNormal_bug "if-cond type should bool"
      end
    | FunExp ((x, _), k, f) -> 
      let tent_var = genvar "_var" in
      let f = k_normalize_exp (Environment.add x [] @@ Environment.add k [] tvsenv) f in
      KNorm.LetRecExp (tent_var, [], (x, k), f, KNorm.Var tent_var)
    | FixExp _ -> raise @@ KNormal_bug "FixExp should appear in let"
    | AppExp (f1, f2, f3) ->
      let f1 = k_normalize_exp tvsenv f1 in 
      let f2 = k_normalize_exp tvsenv f2 in
      let f3 = k_normalize_exp tvsenv f3 in
      insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> insert_let f3 @@ fun z -> KNorm.AppExp (x, (y, z))
    | CAppExp (f1, f2) -> 
      let f1 = k_normalize_exp tvsenv f1 in
      let f2 = k_normalize_exp tvsenv f2 in 
      insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.CAppExp (x, y)
    | CSeqExp (f1, f2) ->
      let f1 = k_normalize_exp tvsenv f1 in
      let f2 = k_normalize_exp tvsenv f2 in 
      insert_let f1 @@ fun x -> insert_let f2 @@ fun y -> KNorm.CSeqExp (x, y)
    | LetExp (x, tvs, f1, f2) -> 
      begin match f1 with
        | FunExp ((x', _), k, f1) ->
          let f1 = k_normalize_exp (Environment.add x' [] @@ Environment.add k [] tvsenv) f1 in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetRecExp (x, tvs, (x', k), f1, f2)
        | FixExp ((x', y, _, _), k, f1) ->
          assert (x' = x);
          let f1 = k_normalize_exp (Environment.add y [] @@ Environment.add x' [] @@ Environment.add k [] tvsenv) f1 in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetRecExp (x, tvs, (y, k), f1, f2)
        | f ->
          let f1 = k_normalize_exp tvsenv f in
          let f2 = k_normalize_exp (Environment.add x tvs tvsenv) f2 in
          KNorm.LetExp (x, f1, f2)
      end
    | CoercionExp c -> KNorm.CoercionExp c
    | AppExp_alt _ | FunExp_alt _ | FixExp_alt _ -> raise @@ KNormal_bug "alternative translation yet"

  let k_normalize_program tvsenv = function
    | Exp f -> let f = k_normalize_exp tvsenv f in KNorm.Exp f, tvsenv
    | LetDecl (x, tvs, f) -> 
      begin match f with
        | FunExp ((x', _), k, f) ->
          let f = k_normalize_exp (Environment.add x' [] @@ Environment.add k [] tvsenv) f in
          KNorm.LetRecDecl (x, tvs, (x', k), f), Environment.add x tvs tvsenv
        | FixExp ((x', y, _, _), k, f) ->
          assert (x' = x);
          let f = k_normalize_exp (Environment.add y [] @@ Environment.add x' [] @@ Environment.add k [] tvsenv) f in
          KNorm.LetRecDecl (x, tvs, (y, k), f), Environment.add x tvs tvsenv
        | _ as f ->
          let f = k_normalize_exp tvsenv f in 
          KNorm.LetDecl (x, f), Environment.add x tvs tvsenv
      end
end

module KNorm = struct
  open Syntax.KNorm

  let find x idenv = try Environment.find x idenv with Not_found -> x

  (* beta : let x = y in ... となっているようなxをyに置き換える *)
  let rec beta_exp idenv = function
    | Var x -> Var (find x idenv)
    | IConst _ | UConst as f -> f
    | Add (x, y) -> Add (find x idenv, find y idenv)
    | Sub (x, y) -> Sub (find x idenv, find y idenv)
    | Mul (x, y) -> Mul (find x idenv, find y idenv)
    | Div (x, y) -> Div (find x idenv, find y idenv)
    | Mod (x, y) -> Mod (find x idenv, find y idenv)
    | IfEqExp (x, y, f1, f2) ->
      IfEqExp (find x idenv, find y idenv, beta_exp idenv f1, beta_exp idenv f2)
    | IfLteExp (x, y, f1, f2) ->
      IfLteExp (find x idenv, find y idenv, beta_exp idenv f1, beta_exp idenv f2)
    | AppExp (x, (y, z)) -> AppExp (find x idenv, (find y idenv, find z idenv))
    | AppTy (x, tvs, tas) -> AppTy (find x idenv, tvs, tas)
    | CAppExp (x, y) -> CAppExp (find x idenv, find y idenv)
    | CSeqExp (x, y) -> CSeqExp (find x idenv, find y idenv)
    (* | CastExp (r, x, u1, u2, p) -> CastExp (r, find x idenv, u1, u2, p) *)
    | LetExp (x, f1, f2) ->
      let f1 = beta_exp idenv f1 in
      begin match f1 with
        | Var x' -> beta_exp (Environment.add x x' idenv) f2
        | f1 -> LetExp (x, f1, beta_exp idenv f2)
      end
    | LetRecExp (x, tvs, arg, f1, f2) ->
      LetRecExp (x, tvs, arg, beta_exp idenv f1, beta_exp idenv f2)
    | CoercionExp _ as f -> f

  let beta_program idenv = function
    | Exp f -> Exp (beta_exp idenv f), idenv
    | LetDecl (x, f) ->
      let f = beta_exp idenv f in
      begin match f with
      | Var x' as f -> Exp f, Environment.add x x' idenv
      | f -> LetDecl (x, f), idenv
      end
    | LetRecDecl (x, tvs, arg, f) ->
      LetRecDecl (x, tvs, arg, beta_exp idenv f), idenv

  (* assoc : let x = (let y = ... in ... ) in ...というようなネストされたletをlet y = ... in let x = ... in ...という形に平たくする *)
  let rec assoc_exp = function
    | IfEqExp (x, y, f1, f2) -> IfEqExp (x, y, assoc_exp f1, assoc_exp f2)
    | IfLteExp (x, y, f1, f2) -> IfLteExp (x, y, assoc_exp f1, assoc_exp f2)
    (*| CastExp (r, f, u1, u2, p) -> CastExp (r, assoc_exp f, u1, u2, p)*)
    | LetExp (x, f1, f2) ->
      let rec insert = function
        | LetExp (x', f3, f4) -> LetExp (x', f3, insert f4)
        | LetRecExp (x', tvs, arg, f3, f4) -> LetRecExp (x', tvs, arg, f3, insert f4)
        | f1 -> LetExp (x, f1, assoc_exp f2)
      in insert (assoc_exp f1)
    | LetRecExp (x, tvs, arg, f1, f2) ->
      LetRecExp (x, tvs, arg, assoc_exp f1, assoc_exp f2)
    | f -> f
  
  let assoc_program = function
    | Exp f -> Exp (assoc_exp f)
    | LetDecl (x, f) -> LetDecl (x, assoc_exp f)
    | LetRecDecl (x, tvs, arg, f) -> LetRecDecl (x, tvs, arg, assoc_exp f)
end

let kNorm_funs ?(debug=false) (tvsenv, alphaenv, betaenv) f = 
  let f, alphaenv = LS1.alpha_program alphaenv f in
  if debug then fprintf err_formatter "alpha: %a\n" Pp.LS1.pp_program f;
  let f, tvsenv = LS1.k_normalize_program tvsenv f in
  if debug then fprintf err_formatter "k_normalize: %a\n" Pp.KNorm.pp_program f;
  let rec iter betaenv f =
    let fbeta, betaenv = KNorm.beta_program betaenv f in
    let fassoc = KNorm.assoc_program fbeta in
    if f = fassoc then f, (tvsenv, alphaenv, betaenv) else 
      (if debug then fprintf err_formatter "beta: %a\n" Pp.KNorm.pp_program fbeta;
      if debug then fprintf err_formatter "assoc: %a\n" Pp.KNorm.pp_program fassoc;
      iter betaenv fassoc)
  in iter betaenv f