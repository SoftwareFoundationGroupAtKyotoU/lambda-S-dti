open Syntax

exception Stdlib_bug of string
exception Stdlib_exit of int

let is_debug = ref false
let is_alt = ref false

let is_some_type = tysc_of_ty @@ TyFun (TyDyn, TyBool)

module LS1 = struct 
  open Syntax.LS1

  let is_some t = 
    if !is_alt then
      FunV_alt (fun _ -> 
        (function
        | CoerceV (_, CSeq (_, CInj t')) when t = t' -> BoolV true
        | CoerceV _ -> BoolV false
        | _ -> raise @@ Stdlib_bug "not dyn value"),
        (function
        | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> Eval.LS1.coerce ~debug:!is_debug (BoolV true) c'
        | CoerceV _, CoercionV c' -> Eval.LS1.coerce ~debug:!is_debug (BoolV false) c'
        | _ -> raise @@ Stdlib_bug "not dyn value")
      )
    else
      FunV (fun _ -> function
      | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> Eval.LS1.coerce ~debug:!is_debug (BoolV true) c'
      | CoerceV _, CoercionV c' -> Eval.LS1.coerce ~debug:!is_debug (BoolV false) c'
      | _ -> raise @@ Stdlib_bug "not dyn value"
      )

  let lib_exit = 
    if !is_alt then
      FunV_alt (fun _ -> 
      (function
      | IntV i -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"),
      (function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value")
      )
    else 
      FunV (fun _ -> function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"
      )

  let lib_print_bool = 
    if !is_alt then 
      FunV_alt (fun _ -> 
        (function
        | BoolV b -> 
          print_string @@ string_of_bool b;
          UnitV
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"),    
        (function
        | BoolV b, CoercionV c -> 
          print_string @@ string_of_bool b;
          Eval.LS1.coerce ~debug:!is_debug UnitV c
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value")
      )
    else
      FunV (fun _ -> function
      | BoolV b, CoercionV c -> 
        print_string @@ string_of_bool b; 
        Eval.LS1.coerce ~debug:!is_debug UnitV c
      | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
      )

  let lib_print_int = 
    if !is_alt then
      FunV_alt (fun _ -> 
        (function
        | IntV i -> 
          print_int i;
          UnitV
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value"),
        (function
        | IntV i, CoercionV c -> 
          print_int i;
          Eval.LS1.coerce ~debug:!is_debug UnitV c
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value")
      )
    else
      FunV (fun _ -> function
      | IntV i, CoercionV c -> 
        print_int i;
        Eval.LS1.coerce ~debug:!is_debug UnitV c
      | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
      )

  let lib_print_newline = 
    if !is_alt then
      FunV_alt (fun _ -> 
        (function
        | UnitV -> 
          print_newline (); 
          UnitV
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"),
        (function
        | UnitV, CoercionV c -> 
          print_newline (); 
          Eval.LS1.coerce ~debug:!is_debug UnitV c
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value")
      )
    else 
      FunV (fun _ -> function
      | UnitV, CoercionV c -> 
        print_newline (); 
        Eval.LS1.coerce ~debug:!is_debug UnitV c
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
end

module KNorm = struct 
  open Syntax.KNorm

  let is_some t = 
    if !is_alt then
      FunV_alt (fun _ -> 
        (function
        | CoerceV (_, CSeq (_, CInj t')) when t = t' -> IntV 1
        | CoerceV _ -> IntV 0
        | _ -> raise @@ Stdlib_bug "not dyn value"),
        (function
        | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> Eval.KNorm.coerce ~debug:!is_debug (IntV 1) c'
        | CoerceV _, CoercionV c' -> Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c'
        | _ -> raise @@ Stdlib_bug "not dyn value")
      )
    else
      FunV (fun _ -> function
      | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> Eval.KNorm.coerce ~debug:!is_debug (IntV 1) c'
      | CoerceV _, CoercionV c' -> Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c'
      | _ -> raise @@ Stdlib_bug "not dyn value"
      )

  let lib_exit = 
    if !is_alt then
      FunV_alt (fun _ -> 
      (function
      | IntV i -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"),
      (function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value")
      )
    else 
      FunV (fun _ -> function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"
      )

  let lib_print_bool = 
    if !is_alt then 
      FunV_alt (fun _ -> 
        (function
        | IntV 0 -> 
          print_string "false";
          IntV 0
        | IntV 1 -> 
          print_string "true";
          IntV 0
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"),    
        (function
        | IntV 0, CoercionV c -> 
          print_string "false";
          Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c
        | IntV 1, CoercionV c -> 
          print_string "true";
          Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value")
      )
    else
      FunV (fun _ -> function
      | IntV 0, CoercionV c -> 
        print_string "false"; 
        Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c
      | IntV 1, CoercionV c -> 
        print_string "true"; 
        Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c
      | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
      )

  let lib_print_int = 
    if !is_alt then
      FunV_alt (fun _ -> 
        (function
        | IntV i -> 
          print_int i;
          IntV 0
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value"),
        (function
        | IntV i, CoercionV c -> 
          print_int i;
          Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value")
      )
    else
      FunV (fun _ -> function
      | IntV i, CoercionV c -> 
        print_int i;
        Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c
      | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
      )

  let lib_print_newline = 
    if !is_alt then
      FunV_alt (fun _ -> 
        (function
        | IntV 0 -> 
          print_newline (); 
          IntV 0
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"),
        (function
        | IntV 0, CoercionV c -> 
          print_newline (); 
          Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value")
      )
    else 
      FunV (fun _ -> function
      | IntV 0, CoercionV c -> 
        print_newline (); 
        Eval.KNorm.coerce ~debug:!is_debug (IntV 0) c
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
end

let pervasives ~alt:alt ~debug:debug ~compile:compile = 
  is_alt := alt;
  is_debug := debug;
  let env, tyenv, kfunenvs, kenv = Environment.empty, Environment.empty, (Environment.empty, Environment.empty, Environment.empty), Environment.empty in
  let implementations_direct = [
    "exit", [], LS1.lib_exit, tysc_of_ty @@ TyFun (TyInt, TyUnit), KNorm.lib_exit;
    "is_bool", [], LS1.is_some B, is_some_type, KNorm.is_some B;
    "is_int", [], LS1.is_some I, is_some_type, KNorm.is_some I;
    "is_unit", [], LS1.is_some U, is_some_type, KNorm.is_some U;
    "is_fun", [], LS1.is_some Ar, is_some_type, KNorm.is_some Ar;
    "is_list", [], LS1.is_some Li, is_some_type, KNorm.is_some Li;
    "max_int", [], IntV max_int, tysc_of_ty TyInt, IntV max_int;
    "min_int", [], IntV min_int, tysc_of_ty TyInt, IntV min_int;
    "print_bool", [], LS1.lib_print_bool, tysc_of_ty @@ TyFun (TyBool, TyUnit), KNorm.lib_print_bool;
    "print_int", [], LS1.lib_print_int, tysc_of_ty @@ TyFun (TyInt, TyUnit), KNorm.lib_print_int;
    "print_newline", [], LS1.lib_print_newline, tysc_of_ty @@ TyFun (TyUnit, TyUnit), KNorm.lib_print_newline;
  ] in
  let env, tyenv, kfunenvs, kenv =
    List.fold_left
      (fun (env, tyenv, (tvsenv, alphaenv, betaenv), kenv) (x, xs, v, u, kv) ->
         Environment.add x (xs, v) env, Environment.add x u tyenv, (Environment.add x [] tvsenv, Environment.add x x alphaenv, Environment.add x x betaenv), Environment.add x kv kenv)
      (env, tyenv, kfunenvs, kenv)
      implementations_direct
  in 
  let implementations_eval = [
    "let not b = if b then false else true;;";
    "let succ x = x + 1;;";
    "let prec x = x - 1;;";
    "let min x y = if x < y then x else y;;";
    "let max x y = if x > y then x else y;;";
    "let abs x = if x < 0 then -x else x;;";
    "let ignore x = ();;";
  ] in
  let env, tyenv, kfunenvs', kenv =
    List.fold_left
      (fun (env, tyenv, kfunenvs, kenv) str ->
        let e = Parser.toplevel Lexer.main @@ Lexing.from_string str in
        let e, u = Typing.ITGL.type_of_program tyenv e in
        let tyenv, e, _ = Typing.ITGL.normalize tyenv e u in
        let new_tyenv, f, _ = Translate.ITGL.translate tyenv e in
        let _ = Typing.LS.type_of_program tyenv f in
        let f = 
          if alt then Translate.LS.translate_alt tyenv f
          else Translate.LS.translate tyenv f
        in let env, _, _ = Eval.LS1.eval_program env f in
        let kf, kfunenvs = KNormal.kNorm_funs kfunenvs f in
        let kenv, _, _ = Eval.KNorm.eval_program kenv kf in
        env, new_tyenv, kfunenvs, kenv)
      (env, tyenv, kfunenvs, kenv)
      implementations_eval
  in
  let kfunenvs = 
    if compile then
      let kfunenvs = List.fold_left (fun (t, a, b) -> fun x -> Environment.add x [] t, Environment.add x x a, Environment.add x x b) kfunenvs ["not"; "succ"; "prec"; "min"; "max"] in
      let kfunenvs = List.fold_left (fun (t, a, b) -> fun (x, y) -> Environment.add y [] t, Environment.add x y a, Environment.add y y b) kfunenvs ["abs", "abs_ml"] in
      List.fold_left (fun (t, a, b) -> fun x -> Environment.add x [0, ref None] t, Environment.add x x a, Environment.add x x b) kfunenvs ["ignore"]
    else 
      kfunenvs'
  in
  env, tyenv, kfunenvs, kenv

let venv = List.fold_left (fun vs -> fun x -> Cls.V.add x vs) Cls.V.empty ["print_int"; "print_bool"; "print_newline"; "not"; "succ"; "prec"; "min"; "max"; "abs"; "ignore"]