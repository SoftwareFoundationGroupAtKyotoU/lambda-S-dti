open Syntax
open Type_utils
open Types_lib

let core_random_init = function
  | CC.IntV i -> Random.init i; CC.UnitV
  | _ -> raise @@ Stdlib_bug "random_init: unexpected value"
let lib_random_init ~config = Prim_lib.lift1 ~config core_random_init

let core_random_int = function
  | CC.IntV bound -> CC.IntV (Random.int bound)
  | _ -> raise @@ Stdlib_bug "random_int: unexpected value"
let lib_random_int ~config = Prim_lib.lift1 ~config core_random_int

let core_random_float = function
  | CC.FloatV bound -> CC.FloatV (Random.float bound)
  | _ -> raise @@ Stdlib_bug "random_float: unexpected value"
let lib_random_float ~config = Prim_lib.lift1 ~config core_random_float

let builtins : builtin list = [
    { name = "random_init";  impl = Native (lib_random_init, tysc_of_ty @@ TyFun (TyInt, TyUnit));     c_backing = CUnimplemented };
    { name = "random_int";   impl = Native (lib_random_int, tysc_of_ty @@ TyFun (TyInt, TyInt));       c_backing = CUnimplemented };
    { name = "random_float"; impl = Native (lib_random_float, tysc_of_ty @@ TyFun (TyFloat, TyFloat)); c_backing = CUnimplemented };
  ]
