open Syntax

module ITGL : sig
	open Syntax.ITGL
	val translate : tysc Environment.t -> program -> (tysc Environment.t * LS.program * ty)
end

module LS : sig
	open Syntax.LS

	val translate : tysc Environment.t -> program -> LS1.program

	(* val to_se : program -> program *)
end
