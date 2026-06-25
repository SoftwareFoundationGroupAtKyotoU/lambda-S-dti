open Syntax

exception Coercion_bug of string

val is_d : coercion -> bool

val make_s_coercion : monotonic:bool -> ty -> (Utils.Error.range * polarity) -> ty -> coercion

val compose : config:Config.t -> coercion -> coercion -> coercion
