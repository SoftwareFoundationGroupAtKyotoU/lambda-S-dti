open Syntax
open Config
open Type_utils

exception Stdlib_bug of string
exception Stdlib_exit of int

let is_some_type = tysc_of_ty @@ TyFun (TyDyn, TyBool)

module CC = struct
  open Syntax.CC

  let lift1 ~config (core : value -> value) : value =
    if config.intoB then
      FunBV (fun _ v -> core v)
    else if config.alt then
      FunDualV (fun _ ->
        (fun v -> core v),
        (function
          | v, CoercionV c -> Eval.CC.toplevel_coerce ~config (core v) c
          | _ -> raise @@ Stdlib_bug "lift1: expected coercion argument"))
    else
      FunSV (fun _ -> function
        | v, CoercionV c -> Eval.CC.toplevel_coerce ~config (core v) c
        | _ -> raise @@ Stdlib_bug "lift1: expected coercion argument")

  let core_is_some ~config t v =
    if config.intoB then
      match v with
      | Tagged (t', _) when t = t' -> BoolV true
      | Tagged _ -> BoolV false
      | _ -> raise @@ Stdlib_bug "untagged value"
    else
      match v with
      | CoerceV (_, CSeq (_, CInj t')) when t = t' -> BoolV true
      | CoerceV _ -> BoolV false
      | _ -> raise @@ Stdlib_bug "not dyn value"
  let lib_is_some t ~config = lift1 ~config (core_is_some ~config t)

  let core_exit = function
    | IntV i -> raise @@ Stdlib_exit i
    | _ -> raise @@ Stdlib_bug "exit: unexpected value"
  let lib_exit ~config = lift1 ~config core_exit

  let core_print_bool = function
    | BoolV b -> print_string @@ string_of_bool b; UnitV
    | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
  let lib_print_bool ~config = lift1 ~config core_print_bool

  let core_print_int = function
    | IntV i -> print_int i; UnitV
    | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
  let lib_print_int ~config = lift1 ~config core_print_int

  let core_print_float = function
    | FloatV f -> print_float f; UnitV
    | _ -> raise @@ Stdlib_bug "print_float: unexpected value"
  let lib_print_float ~config = lift1 ~config core_print_float

  let core_print_newline = function
    | UnitV -> print_newline (); UnitV
    | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
  let lib_print_newline ~config = lift1 ~config core_print_newline

  let core_read_int = function
    | UnitV -> let i = read_int () in IntV i
    | _ -> raise @@ Stdlib_bug "read_int: unexpected value"
  let lib_read_int ~config = lift1 ~config core_read_int

  let core_read_float = function
    | UnitV -> let f = read_float () in FloatV f
    | _ -> raise @@ Stdlib_bug "read_float: unexpected value"
  let lib_read_float ~config = lift1 ~config core_read_float

  let core_float_of_int = function
    | IntV i -> FloatV (float_of_int i)
    | _ -> raise @@ Stdlib_bug "float_of_int: unexpected value"
  let lib_float_of_int ~config = lift1 ~config core_float_of_int

  let core_int_of_float = function
    | FloatV f -> IntV (int_of_float f)
    | _ -> raise @@ Stdlib_bug "int_of_float: unexpected value"
  let lib_int_of_float ~config = lift1 ~config core_int_of_float

  let lib_max_int ~config:_ = IntV max_int
  let lib_min_int ~config:_ = IntV min_int
end

type impl =
  | Native of (config:Config.t -> Syntax.CC.value) * tysc
  | ITGL of string

(* TODO: erase CUnimplemented *)
type c_backing =
  | CImpl of string
  | CUnimplemented

type builtin = { name : string; impl : impl; c_backing : c_backing }

let builtins : builtin list = [
    { name = "exit";          impl = Native (CC.lib_exit, tysc_of_ty @@ TyFun (TyInt, TyUnit));           c_backing = CUnimplemented };
    { name = "is_int";        impl = Native (CC.lib_is_some I, is_some_type);                             c_backing = CUnimplemented };
    { name = "is_bool";       impl = Native (CC.lib_is_some B, is_some_type);                             c_backing = CUnimplemented };
    { name = "is_unit";       impl = Native (CC.lib_is_some U, is_some_type);                             c_backing = CUnimplemented };
    { name = "is_float";      impl = Native (CC.lib_is_some F, is_some_type);                             c_backing = CUnimplemented };
    { name = "is_fun";        impl = Native (CC.lib_is_some Fn, is_some_type);                            c_backing = CUnimplemented };
    { name = "is_list";       impl = Native (CC.lib_is_some Li, is_some_type);                            c_backing = CUnimplemented };
    { name = "max_int";       impl = Native (CC.lib_max_int, tysc_of_ty TyInt);                           c_backing = CImpl "max_int" };
    { name = "min_int";       impl = Native (CC.lib_min_int, tysc_of_ty TyInt);                           c_backing = CImpl "min_int" };
    { name = "print_bool";    impl = Native (CC.lib_print_bool, tysc_of_ty @@ TyFun (TyBool, TyUnit));    c_backing = CImpl "print_bool" };
    { name = "print_int";     impl = Native (CC.lib_print_int, tysc_of_ty @@ TyFun (TyInt, TyUnit));      c_backing = CImpl "print_int" };
    { name = "print_float";   impl = Native (CC.lib_print_float, tysc_of_ty @@ TyFun (TyFloat, TyUnit));  c_backing = CImpl "print_float" };
    { name = "print_newline"; impl = Native (CC.lib_print_newline, tysc_of_ty @@ TyFun (TyUnit, TyUnit)); c_backing = CImpl "print_newline" };
    { name = "read_int";      impl = Native (CC.lib_read_int, tysc_of_ty @@ TyFun (TyUnit, TyInt));       c_backing = CImpl "read_int" };
    { name = "read_float";    impl = Native (CC.lib_read_float, tysc_of_ty @@ TyFun (TyUnit, TyFloat));   c_backing = CImpl "read_float" };
    { name = "float_of_int";  impl = Native (CC.lib_float_of_int, tysc_of_ty @@ TyFun (TyInt, TyFloat));  c_backing = CImpl "float_of_int" };
    { name = "int_of_float";  impl = Native (CC.lib_int_of_float, tysc_of_ty @@ TyFun (TyFloat, TyInt));  c_backing = CImpl "int_of_float" };
    { name = "not";           impl = ITGL "let not b = if b then false else true;;";                      c_backing = CImpl "not_ml" };
    { name = "succ";          impl = ITGL "let succ x = x + 1;;";                                         c_backing = CImpl "succ" };
    { name = "prec";          impl = ITGL "let prec x = x - 1;;";                                         c_backing = CImpl "prec" };
    { name = "min";           impl = ITGL "let min x y = if x < y then x else y;;";                       c_backing = CImpl "min" };
    { name = "max";           impl = ITGL "let max x y = if x > y then x else y;;";                       c_backing = CImpl "max" };
    { name = "abs";           impl = ITGL "let abs x = if x < 0 then -x else x;;";                        c_backing = CImpl "abs_ml" };
    { name = "ignore";        impl = ITGL "let ignore x = ();;";                                          c_backing = CImpl "ignore" };
  ]

let pervasives ~config =
  let initial_envs = Environment.empty, Environment.empty in
  let add_to_envs (env, tyenv) builtin = match builtin.impl with
    | Native (f, tysc) ->
      if config.compile && builtin.c_backing = CUnimplemented then
        env, tyenv
      else
        Environment.add builtin.name (f ~config) env, Environment.add builtin.name tysc tyenv
    | ITGL str ->
      let e = Parser.toplevel Lexer.main @@ Lexing.from_string str in
      let e, u = Typing.ITGL.type_of_program tyenv e in
      let tyenv, e, _ = Normalize.ITGL.normalize tyenv e u in
      let new_tyenv, f, _ = Translate.ITGL.translate ~config tyenv e in
      let _ = Typing.CC.type_of_program tyenv f in
      let f, _ = Translate.CC.translate ~config tyenv f in
      let _ = Typing.CC.type_of_program tyenv f in
      let env, _, _ = Eval.CC.eval_program ~config env f in
      env, new_tyenv
  in
  let env, tyenv = List.fold_left add_to_envs initial_envs builtins in
  let pick_tvs name = match Environment.find name tyenv with TyScheme (tvs, _) -> tvs in
  let initial_compile_env = (Environment.empty, Environment.empty, Environment.empty), V.empty, Environment.empty in
  let add_to_compile_env ((tvsenv, alphaenv, betaenv), known, args) builtin = match builtin.c_backing with
    | CImpl cname -> (Environment.add builtin.name (pick_tvs builtin.name) tvsenv, Environment.add builtin.name cname alphaenv, Environment.add cname cname betaenv), V.add cname known, Environment.add cname ([], 0) args
    | CUnimplemented -> (tvsenv, alphaenv, betaenv), known, args
  in
  let compile_env = List.fold_left add_to_compile_env initial_compile_env builtins in
  env, tyenv, compile_env