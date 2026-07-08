open Syntax

exception Translation_bug of string

module ITGL : sig
	open Syntax.ITGL
	val translate : config:Config.t -> tysc Environment.t -> program -> (tysc Environment.t * CC.program * ty)
end

module CC : sig
	open Syntax.CC

	val translate : config:Config.t -> tysc Environment.t -> program -> (program * ty)
end

module Cls : sig
	open Syntax.Cls

	val altCls : config:Config.t -> program -> program
end
