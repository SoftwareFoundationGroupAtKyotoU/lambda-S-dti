open Syntax
open Type_utils
open Types

let core_float_of_int = function
  | CC.IntV i -> CC.FloatV (float_of_int i)
  | _ -> raise @@ Stdlib_bug "float_of_int: unexpected value"
let lib_float_of_int ~config = Prim.lift1 ~config core_float_of_int

let core_int_of_float = function
  | CC.FloatV f -> CC.IntV (int_of_float f)
  | _ -> raise @@ Stdlib_bug "int_of_float: unexpected value"
let lib_int_of_float ~config = Prim.lift1 ~config core_int_of_float

let core_char_of_int = function
  | CC.IntV i -> CC.CharV (Char.chr i)
  | _ -> raise @@ Stdlib_bug "char_of_int: unexpected value"
let lib_char_of_int ~config = Prim.lift1 ~config core_char_of_int

let core_int_of_char = function
  | CC.CharV c -> CC.IntV (Char.code c)
  | _ -> raise @@ Stdlib_bug "int_of_char: unexpected value"
let lib_int_of_char ~config = Prim.lift1 ~config core_int_of_char

let lib_max_int ~config:_ = CC.IntV max_int
let lib_min_int ~config:_ = CC.IntV min_int

let builtins : builtin list = [
    { name = "max_int";       impl = Native (lib_max_int, tysc_of_ty TyInt);                           c_backing = CImpl "max_int" };
    { name = "min_int";       impl = Native (lib_min_int, tysc_of_ty TyInt);                           c_backing = CImpl "min_int" };
    { name = "float_of_int";  impl = Native (lib_float_of_int, tysc_of_ty @@ TyFun (TyInt, TyFloat));  c_backing = CImpl "float_of_int" };
    { name = "int_of_float";  impl = Native (lib_int_of_float, tysc_of_ty @@ TyFun (TyFloat, TyInt));  c_backing = CImpl "int_of_float" };
    { name = "char_of_int";   impl = Native (lib_char_of_int, tysc_of_ty @@ TyFun (TyInt, TyChar));   c_backing = CImpl "char_of_int" };
    { name = "int_of_char";   impl = Native (lib_int_of_char, tysc_of_ty @@ TyFun (TyChar, TyInt));   c_backing = CImpl "int_of_char" };
    { name = "not";           impl = ITGL "let not b = if b then false else true;;";                      c_backing = CImpl "not_ml" };
    { name = "succ";          impl = ITGL "let succ x = x + 1;;";                                         c_backing = CImpl "succ" };
    { name = "prec";          impl = ITGL "let prec x = x - 1;;";                                         c_backing = CImpl "prec" };
    { name = "min";           impl = ITGL "let min x y = if x < y then x else y;;";                       c_backing = CImpl "min" };
    { name = "max";           impl = ITGL "let max x y = if x > y then x else y;;";                       c_backing = CImpl "max" };
    { name = "abs";           impl = ITGL "let abs x = if x < 0 then -x else x;;";                        c_backing = CImpl "abs_ml" };
    { name = "ignore";        impl = ITGL "let ignore x = ();;";                                          c_backing = CImpl "ignore" };
  ]
