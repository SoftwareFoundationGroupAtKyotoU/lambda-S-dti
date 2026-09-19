open Syntax
open Type_utils
open Types_lib

let core_float_of_int = function
  | CC.IntV i -> CC.FloatV (float_of_int i)
  | _ -> raise @@ Stdlib_bug "float_of_int: unexpected value"
let lib_float_of_int ~config = Prim_lib.lift1 ~config core_float_of_int

let core_int_of_float = function
  | CC.FloatV f -> CC.IntV (int_of_float f)
  | _ -> raise @@ Stdlib_bug "int_of_float: unexpected value"
let lib_int_of_float ~config = Prim_lib.lift1 ~config core_int_of_float

let core_char_of_int = function
  | CC.IntV i -> CC.CharV (Char.chr i)
  | _ -> raise @@ Stdlib_bug "char_of_int: unexpected value"
let lib_char_of_int ~config = Prim_lib.lift1 ~config core_char_of_int

let core_int_of_char = function
  | CC.CharV c -> CC.IntV (Char.code c)
  | _ -> raise @@ Stdlib_bug "int_of_char: unexpected value"
let lib_int_of_char ~config = Prim_lib.lift1 ~config core_int_of_char

let builtins : builtin list = [
    { name = "float_of_int";  impl = Native (lib_float_of_int, tysc_of_ty @@ TyFun (TyInt, TyFloat));  c_backing = CImpl "float_of_int" };
    { name = "int_of_float";  impl = Native (lib_int_of_float, tysc_of_ty @@ TyFun (TyFloat, TyInt));  c_backing = CImpl "int_of_float" };
    { name = "char_of_int";   impl = Native (lib_char_of_int, tysc_of_ty @@ TyFun (TyInt, TyChar));   c_backing = CImpl "char_of_int" };
    { name = "int_of_char";   impl = Native (lib_int_of_char, tysc_of_ty @@ TyFun (TyChar, TyInt));   c_backing = CImpl "int_of_char" };
    { name = "not";           impl = ITGL "let not b = if b then false else true;;";                      c_backing = CImpl "not_ml" };
    { name = "ignore";        impl = ITGL "let ignore x = ();;";                                          c_backing = CImpl "ignore" };
  ]
