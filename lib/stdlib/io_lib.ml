open Syntax
open Type_utils
open Types_lib

let core_exit = function
  | CC.IntV i -> raise @@ Stdlib_exit i
  | _ -> raise @@ Stdlib_bug "exit: unexpected value"
let lib_exit ~config = Prim_lib.lift1 ~config core_exit

let core_print_bool = function
  | CC.BoolV b -> print_string @@ string_of_bool b; CC.UnitV
  | _ -> raise @@ Stdlib_bug "print_bool: unexpected value"
let lib_print_bool ~config = Prim_lib.lift1 ~config core_print_bool

let core_print_int = function
  | CC.IntV i -> print_int i; CC.UnitV
  | _ -> raise @@ Stdlib_bug "print_int: unexpected value"
let lib_print_int ~config = Prim_lib.lift1 ~config core_print_int

let core_print_float = function
  | CC.FloatV f -> print_float f; CC.UnitV
  | _ -> raise @@ Stdlib_bug "print_float: unexpected value"
let lib_print_float ~config = Prim_lib.lift1 ~config core_print_float

let core_print_char = function
  | CC.CharV c -> print_char c; CC.UnitV
  | _ -> raise @@ Stdlib_bug "print_char: unexpected value"
let lib_print_char ~config = Prim_lib.lift1 ~config core_print_char

let core_print_string = function
  | CC.StringV s -> print_string s; CC.UnitV
  | _ -> raise @@ Stdlib_bug "print_string: unexpected value"
let lib_print_string ~config = Prim_lib.lift1 ~config core_print_string

let core_print_newline = function
  | CC.UnitV -> print_newline (); CC.UnitV
  | _ -> raise @@ Stdlib_bug "print_newline: unexpected value"
let lib_print_newline ~config = Prim_lib.lift1 ~config core_print_newline

let core_read_int = function
  | CC.UnitV -> let i = read_int () in CC.IntV i
  | _ -> raise @@ Stdlib_bug "read_int: unexpected value"
let lib_read_int ~config = Prim_lib.lift1 ~config core_read_int

let core_read_float = function
  | CC.UnitV -> let f = read_float () in CC.FloatV f
  | _ -> raise @@ Stdlib_bug "read_float: unexpected value"
let lib_read_float ~config = Prim_lib.lift1 ~config core_read_float

let core_read_char = function
  | CC.UnitV -> let c = input_char stdin in CC.CharV c
  | _ -> raise @@ Stdlib_bug "read_char: unexpected value"
let lib_read_char ~config = Prim_lib.lift1 ~config core_read_char

let builtins : builtin list = [
    { name = "exit";          impl = Native (lib_exit, tysc_of_ty @@ TyFun (TyInt, TyUnit));           c_backing = CUnimplemented };
    { name = "print_bool";    impl = Native (lib_print_bool, tysc_of_ty @@ TyFun (TyBool, TyUnit));    c_backing = CImpl "print_bool" };
    { name = "print_int";     impl = Native (lib_print_int, tysc_of_ty @@ TyFun (TyInt, TyUnit));      c_backing = CImpl "print_int" };
    { name = "print_float";   impl = Native (lib_print_float, tysc_of_ty @@ TyFun (TyFloat, TyUnit));  c_backing = CImpl "print_float" };
    { name = "print_char";    impl = Native (lib_print_char, tysc_of_ty @@ TyFun (TyChar, TyUnit));     c_backing = CImpl "print_char" };
    { name = "print_string";  impl = Native (lib_print_string, tysc_of_ty @@ TyFun (TyString, TyUnit)); c_backing = CImpl "print_string" };
    { name = "print_newline"; impl = Native (lib_print_newline, tysc_of_ty @@ TyFun (TyUnit, TyUnit)); c_backing = CImpl "print_newline" };
    { name = "read_int";      impl = Native (lib_read_int, tysc_of_ty @@ TyFun (TyUnit, TyInt));       c_backing = CImpl "read_int" };
    { name = "read_float";    impl = Native (lib_read_float, tysc_of_ty @@ TyFun (TyUnit, TyFloat));   c_backing = CImpl "read_float" };
    { name = "read_char";     impl = Native (lib_read_char, tysc_of_ty @@ TyFun (TyUnit, TyChar));     c_backing = CUnimplemented };
  ]
