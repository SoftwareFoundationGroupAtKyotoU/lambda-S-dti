open Syntax

exception Unify_error of string

val unify : constr -> unit

val unify_meet : ty -> ty -> ty