open Syntax

exception Stdlib_bug of string
exception Stdlib_exit of int

let env, tyenv, kfunenvs, kenv = Environment.empty, Environment.empty, (Environment.empty, Environment.empty, Environment.empty), Environment.empty

let is_some_type = tysc_of_ty @@ TyFun (TyDyn, TyBool)

module LS1 = struct 
  open Syntax.LS1

  (* let is_some u = FunV (fun _ -> function
    | Tagged (t, _) when u = tag_to_ty t -> BoolV true
    | Tagged _ -> BoolV false
    | _ -> raise @@ Stdlib_bug "untagged value"
  )*)

  let lib_exit = FunV (fun _ -> function
    | IntV i, _ -> raise @@ Stdlib_exit i
    | _ -> raise @@ Stdlib_bug "exit: unexpected value"
  )

  let lib_print_bool = FunV (fun _ -> function
    | BoolV b, CoercionV c -> 
      print_string @@ string_of_bool b; 
      begin match c with
        | CId _ -> UnitV
        | c -> CoerceV (UnitV, c)
      end
    | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
  )

  let lib_print_int = FunV (fun _ -> function
    | IntV i, CoercionV c -> 
      print_int i;
      begin match c with
        | CId _ -> UnitV
        | c -> CoerceV (UnitV, c)
      end
    | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
  )

  let lib_print_newline = FunV (fun _ -> function
    | UnitV, CoercionV c -> 
      print_newline (); 
      begin match c with
        | CId _ -> UnitV
        | c -> CoerceV (UnitV, c)
      end
    | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
  )
end

module KNorm = struct 
  open Syntax.KNorm

  (*let is_some u = FunV (fun _ -> function
    | Tagged (t, _) when u = tag_to_ty t -> IntV 1
    | Tagged _ -> IntV 0
    | _ -> raise @@ Stdlib_bug "untagged value"
  )*)

  let lib_exit = FunV (fun _ -> function
    | IntV i, _ -> raise @@ Stdlib_exit i
    | _ -> raise @@ Stdlib_bug "exit: unexpected value"
  )

  let lib_print_bool = FunV (fun _ -> function
    | IntV 1, CoercionV c -> 
      print_string "true";
      begin match c with
        | CId _ -> IntV 0
        | c -> CoerceV (IntV 0, c)
      end
    | IntV 0, CoercionV c -> print_string "false";
      begin match c with
        | CId _ -> IntV 0
        | c -> CoerceV (IntV 0, c)
      end
    | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
  )

  let lib_print_int = FunV (fun _ -> function
    | IntV i, CoercionV c -> 
      print_int i;
      begin match c with
        | CId _ -> IntV 0
        | c -> CoerceV (IntV 0, c)
      end
    | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
  )

  let lib_print_newline = FunV (fun _ -> function
    | IntV 0, CoercionV c -> 
      print_newline (); 
      begin match c with
        | CId _ -> IntV 0
        | c -> CoerceV (IntV 0, c)
      end
    | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
  )
end

let implementations = [
  "exit", [], LS1.lib_exit, tysc_of_ty @@ TyFun (TyInt, TyUnit), KNorm.lib_exit;
  (*"is_bool", [], CC.is_some TyBool, is_some_type, KNorm.is_some TyBool;
  "is_int", [], CC.is_some TyInt, is_some_type, KNorm.is_some TyInt;
  "is_unit", [], CC.is_some TyUnit, is_some_type, KNorm.is_some TyUnit;
  "is_fun", [], CC.is_some (TyFun (TyDyn, TyDyn)), is_some_type, KNorm.is_some (TyFun (TyDyn, TyDyn));*)
  "max_int", [], IntV max_int, tysc_of_ty TyInt, IntV max_int;
  "min_int", [], IntV min_int, tysc_of_ty TyInt, IntV min_int;
  "print_bool", [], LS1.lib_print_bool, tysc_of_ty @@ TyFun (TyBool, TyUnit), KNorm.lib_print_bool;
  "print_int", [], LS1.lib_print_int, tysc_of_ty @@ TyFun (TyInt, TyUnit), KNorm.lib_print_int;
  "print_newline", [], LS1.lib_print_newline, tysc_of_ty @@ TyFun (TyUnit, TyUnit), KNorm.lib_print_newline;
]

let env, tyenv, kfunenvs, kenv =
  List.fold_left
    (fun (env, tyenv, (tvsenv, alphaenv, betaenv), kenv) (x, xs, v, u, kv) ->
       Environment.add x (xs, v) env, Environment.add x u tyenv, (Environment.add x [] tvsenv, Environment.add x x alphaenv, Environment.add x x betaenv), Environment.add x kv kenv)
    (env, tyenv, kfunenvs, kenv)
    implementations

let implementations = [
  "let not b = if b then false else true;;";
  "let succ x = x + 1;;";
  "let prec x = x - 1;;";
  "let min x y = if x < y then x else y;;";
  "let max x y = if x > y then x else y;;";
  "let abs x = if x < 0 then -x else x;;";
  "let ignore x = ();;";
]

let env, tyenv, kfunenvs, kenv =
 List.fold_left
    (fun (env, tyenv, kfunenvs, kenv) str ->
      let e = Parser.toplevel Lexer.main @@ Lexing.from_string str in
      let e, u = Typing.ITGL.type_of_program tyenv e in
      let tyenv, e, _ = Typing.ITGL.normalize tyenv e u in
      let new_tyenv, f, _ = Translate.ITGL.translate tyenv e in
      let _ = Typing.LS.type_of_program tyenv f in
      let f = Translate.LS.translate tyenv f in
      (* let env, _, _ = Eval.LS.eval_program env f in *)
      let kf, kfunenvs = KNormal.kNorm_funs kfunenvs f in
      let kenv, _, _ = Eval.KNorm.eval_program kenv kf in
      env, new_tyenv, kfunenvs, kenv)
    (env, tyenv, kfunenvs, kenv)
    implementations

let pervasives = env, tyenv, kfunenvs, kenv