open Syntax
open Config
open Type_utils
open Types

let is_some_type = tysc_of_ty @@ TyFun (TyDyn, TyBool)

let core_is_some ~config t v =
  if config.intoB then
    match v with
    | CC.Tagged (t', _) when t = t' -> CC.BoolV true
    | CC.Tagged _ -> CC.BoolV false
    | _ -> raise @@ Stdlib_bug "untagged value"
  else
    match v with
    | CC.CoerceV (_, CSeq (_, CInj t')) when t = t' -> CC.BoolV true
    | CC.CoerceV _ -> CC.BoolV false
    | _ -> raise @@ Stdlib_bug "not dyn value"
let lib_is_some t ~config = Prim.lift1 ~config (core_is_some ~config t)

let builtins : builtin list = [
    { name = "is_int";        impl = Native (lib_is_some I, is_some_type);   c_backing = CUnimplemented };
    { name = "is_bool";       impl = Native (lib_is_some B, is_some_type);   c_backing = CUnimplemented };
    { name = "is_unit";       impl = Native (lib_is_some U, is_some_type);   c_backing = CUnimplemented };
    { name = "is_float";      impl = Native (lib_is_some F, is_some_type);   c_backing = CUnimplemented };
    { name = "is_fun";        impl = Native (lib_is_some Fn, is_some_type);  c_backing = CUnimplemented };
    { name = "is_list";       impl = Native (lib_is_some Li, is_some_type);  c_backing = CUnimplemented };
  ]
