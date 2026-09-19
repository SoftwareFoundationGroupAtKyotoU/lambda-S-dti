open Syntax

exception Stdlib_bug of string
exception Stdlib_exit of int

type impl =
  | Native of (config:Config.t -> Syntax.CC.value) * tysc
  | ITGL of string

(* TODO: erase CUnimplemented *)
type c_backing =
  | CImpl of string
  | CUnimplemented

type builtin = { name : string; impl : impl; c_backing : c_backing }
