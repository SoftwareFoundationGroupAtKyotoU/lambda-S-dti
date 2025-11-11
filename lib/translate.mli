open Syntax

exception Translation_bug of string

module ITGL : sig
	open Syntax.ITGL
	val translate : tysc Environment.t -> program -> (tysc Environment.t * LS.program * ty)
end

module LS : sig
	open Syntax.LS

	val translate : tysc Environment.t -> program -> LS1.program
	val translate_alt : tysc Environment.t -> program -> LS1.program
end

module KNorm : sig
	open Syntax.KNorm

	val translate : program -> KNorm1.program
	val translate_alt : program -> KNorm1.program
end