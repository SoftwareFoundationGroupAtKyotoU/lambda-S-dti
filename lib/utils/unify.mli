open Syntax

exception Unify_error of string

val unify : constr -> unit

val unify_dom : ty -> ty

val unify_cod : ty -> ty

val unify_lelm : ty -> ty

val unify_telm : int -> ty -> ty list

val unify_cont : ty -> ty

val unify_meet : ty -> ty -> ty