open Syntax

val normalize_type : ty -> ty

module ITGL : sig
	open Syntax.ITGL
	val normalize : tysc Environment.t -> program -> ty -> (tysc Environment.t * program * ty)
end

val normalize_coercion : monotonic:bool -> coercion -> coercion