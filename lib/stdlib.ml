open Syntax
open Config
open Type_utils

exception Stdlib_bug of string
exception Stdlib_exit of int

(* let is_debug = ref false
let is_alt = ref false
let is_B = ref false *)

let is_some_type = tysc_of_ty @@ TyFun (TyDyn, TyBool)

(* module CC = struct 
  open Syntax.CC

  let is_some t = 
    FunBV (fun _ -> function
    | Tagged (t', _) when t = t' -> BoolV true
    | Tagged _ -> BoolV false
    | _ -> raise @@ Stdlib_bug "untagged value"
    )

  let lib_exit = 
    FunV (fun _ -> function
    | IntV i -> raise @@ Stdlib_exit i
    | _ -> raise @@ Stdlib_bug "exit: unexpected value"
    )

  let lib_print_bool = 
    FunV (fun _ -> function
    | BoolV b -> print_string @@ string_of_bool b; UnitV
    | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
    )

  let lib_print_int = 
    FunV (fun _ -> function
    | IntV i -> print_int i; UnitV
    | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
    )

  let lib_print_newline = 
    FunV (fun _ -> function
    | UnitV -> print_newline (); UnitV
    | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
    )

  let lib_read_int =
    FunV (fun _ -> function
    | UnitV -> let i = read_int () in IntV i
    | _ -> raise @@ Stdlib_bug "read_int: unexpected value"
    )
end *)

module CC = struct 
  open Syntax.CC

  let coerce_consume ~config v c = 
    let v, psi = Eval.CC.coerce ~config v c [] in
    Eval.CC.consume ~config psi;
    v

  let is_some t ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | Tagged (t', _) when t = t' -> BoolV true
      | Tagged _ -> BoolV false
      | _ -> raise @@ Stdlib_bug "untagged value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | CoerceV (_, CSeq (_, CInj t')) when t = t' -> BoolV true
        | CoerceV _ -> BoolV false
        | _ -> raise @@ Stdlib_bug "not dyn value"),
        (function
        | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> coerce_consume ~config (BoolV true) c'
        | CoerceV _, CoercionV c' -> coerce_consume ~config (BoolV false) c'
        | _ -> raise @@ Stdlib_bug "not dyn value")
      )
    else
      FunSV (fun _ -> function
      | CoerceV (_, CSeq (_, CInj t')), CoercionV c' when t = t' -> coerce_consume ~config (BoolV true) c'
      | CoerceV _, CoercionV c' -> coerce_consume ~config (BoolV false) c'
      | _ -> raise @@ Stdlib_bug "not dyn value"
      )

  let lib_exit ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | IntV i -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
      (function
      | IntV i -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"),
      (function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | IntV i, _ -> raise @@ Stdlib_exit i
      | _ -> raise @@ Stdlib_bug "exit: unexpected value"
      )

  let lib_print_bool ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | BoolV b -> print_string @@ string_of_bool b; UnitV
      | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
      )
    else if config.alt then 
      FunDualV (fun _ -> 
        (function
        | BoolV b -> 
          print_string @@ string_of_bool b;
          UnitV
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"),    
        (function
        | BoolV b, CoercionV c -> 
          print_string @@ string_of_bool b;
          coerce_consume ~config UnitV c
        | _ -> raise @@ Stdlib_bug "print_bool: unexpected value")
      )
    else
      FunSV (fun _ -> function
      | BoolV b, CoercionV c -> 
        print_string @@ string_of_bool b; 
        coerce_consume ~config UnitV c
      | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
      )

  let lib_print_int ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | IntV i -> print_int i; UnitV
      | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | IntV i -> 
          print_int i;
          UnitV
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value"),
        (function
        | IntV i, CoercionV c -> 
          print_int i;
          coerce_consume ~config UnitV c
        | _ -> raise @@ Stdlib_bug "print_int: unexpected value")
      )
    else
      FunSV (fun _ -> function
      | IntV i, CoercionV c -> 
        print_int i;
        coerce_consume ~config UnitV c
      | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
      )

  let lib_print_newline ~config = 
    if config.intoB then
      FunBV (fun _ -> function
      | UnitV -> print_newline (); UnitV
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | UnitV -> 
          print_newline (); 
          UnitV
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"),
        (function
        | UnitV, CoercionV c -> 
          print_newline (); 
          coerce_consume ~config UnitV c
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | UnitV, CoercionV c -> 
        print_newline (); 
        coerce_consume ~config UnitV c
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )

  let lib_read_int ~config =
    if config.intoB then
      FunBV (fun _ -> function
      | UnitV -> let i = read_int () in IntV i
      | _ -> raise @@ Stdlib_bug "read_int: unexpected value"
      )
    else if config.alt then
      FunDualV (fun _ -> 
        (function
        | UnitV -> 
          let i = read_int () in 
          IntV i
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"),
        (function
        | UnitV, CoercionV c -> 
          let i = read_int () in
          coerce_consume ~config (IntV i) c
        | _ -> raise @@ Stdlib_bug "print_newline: unexpected value")
      )
    else 
      FunSV (fun _ -> function
      | UnitV, CoercionV c -> 
        let i = read_int () in
        coerce_consume ~config (IntV i) c
      | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
      )
end

let implementations_direct ~config = [
    "exit", CC.lib_exit ~config, tysc_of_ty @@ TyFun (TyInt, TyUnit);
    "is_bool", CC.is_some B ~config, is_some_type;
    "is_int", CC.is_some I ~config, is_some_type;
    "is_unit", CC.is_some U ~config, is_some_type;
    "is_fun", CC.is_some Ar ~config, is_some_type;
    "is_list", CC.is_some Li ~config, is_some_type;
    "max_int", IntV max_int, tysc_of_ty TyInt;
    "min_int", IntV min_int, tysc_of_ty TyInt;
    "print_bool", CC.lib_print_bool ~config, tysc_of_ty @@ TyFun (TyBool, TyUnit);
    "print_int", CC.lib_print_int ~config, tysc_of_ty @@ TyFun (TyInt, TyUnit);
    "print_newline", CC.lib_print_newline ~config, tysc_of_ty @@ TyFun (TyUnit, TyUnit);
    "read_int", CC.lib_read_int ~config, tysc_of_ty @@ TyFun (TyUnit, TyInt);
  ]

let implementations_eval = [
    "let not b = if b then false else true;;";
    "let succ x = x + 1;;";
    "let prec x = x - 1;;";
    "let min x y = if x < y then x else y;;";
    "let max x y = if x > y then x else y;;";
    "let abs x = if x < 0 then -x else x;;";
    "let ignore x = ();;";
  ]

let pervasives ~config =
  let config = { config with debug = false } in
  let env, tyenv, kfunenvs = Environment.empty, Environment.empty, (Environment.empty, Environment.empty, Environment.empty) in
  let env, tyenv, kfunenvs =
    List.fold_left
      (fun (env, tyenv, (tvsenv, alphaenv, betaenv)) (x, v, u) ->
        Environment.add x v env, Environment.add x u tyenv, (Environment.add x [] tvsenv, Environment.add x x alphaenv, Environment.add x x betaenv))
      (env, tyenv, kfunenvs)
      (implementations_direct ~config)
  in
  let env, tyenv, kfunenvs' =
    List.fold_left
      (fun (env, tyenv, kfunenvs) str ->
        let e = Parser.toplevel Lexer.main @@ Lexing.from_string str in
        let e, u = Typing.ITGL.type_of_program tyenv e in
        let tyenv, e, _ = Normalize.ITGL.normalize tyenv e u in
        let new_tyenv, f, _ = Translate.ITGL.translate ~config tyenv e in
        let _ = Typing.CC.type_of_program tyenv f in
        let f, _ = Translate.CC.translate ~config tyenv f in
        let _ = Typing.CC.type_of_program tyenv f in
        let env, _, _ = Eval.CC.eval_program ~config env f in
        let _, kfunenvs = KNormal.kNorm_funs kfunenvs f in
        env, new_tyenv, kfunenvs)
      (env, tyenv, kfunenvs)
      implementations_eval
  in
  let kfunenvs = 
    if config.compile then
      let kfunenvs = List.fold_left (fun (t, a, b) -> fun x -> Environment.add x [] t, Environment.add x x a, Environment.add x x b) kfunenvs ["not"; "succ"; "prec"; "min"; "max"] in
      (* C言語で既に定義されている関数 *)
      let kfunenvs = List.fold_left (fun (t, a, b) -> fun (x, y) -> Environment.add y [] t, Environment.add x y a, Environment.add y y b) kfunenvs ["abs", "abs_ml"] in
      (* 多相性のある関数 *)
      List.fold_left (fun (t, a, b) -> fun x -> Environment.add x [0, ref None] t, Environment.add x x a, Environment.add x x b) kfunenvs ["ignore"]
    else 
      kfunenvs'
  in
  env, tyenv, kfunenvs

let venv = List.fold_left (fun vs -> fun x -> V.add x vs) V.empty ["print_int"; "print_bool"; "print_newline"; "read_int"; "not"; "succ"; "prec"; "min"; "max"; "abs"; "ignore"]