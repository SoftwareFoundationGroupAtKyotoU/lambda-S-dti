open Syntax

exception Translation_bug of string

module ITGL : sig
	open Syntax.ITGL
	val make_s_coercion : monotonic:bool -> ty -> (Utils.Error.range * polarity) -> ty -> coercion
	val make_static_middle_coercion : monotonic:bool -> (Utils.Error.range * polarity) -> ty -> (Utils.Error.range * polarity) -> coercion
	val translate : config:Config.t -> tysc Environment.t -> program -> (tysc Environment.t * CC.program * ty)
end

module CC : sig
	open Syntax.CC

	val translate : config:Config.t -> tysc Environment.t -> program -> (program * ty)
end
