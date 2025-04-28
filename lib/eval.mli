open Syntax
open Utils.Error

exception Blame of range * polarity
exception KBlame of range * polarity

exception Eval_bug of string

module LS1 : sig
  open Syntax.LS1
  
  val eval_program : ?debug:bool -> (tyvar list * value) Environment.t -> program -> (tyvar list * value) Environment.t * id * value

  val compose : ?debug:bool -> coercion -> coercion -> coercion
end 

module KNorm : sig
  open Syntax.KNorm

  val eval_program : ?debug:bool -> value Environment.t -> program -> value Environment.t * id * value
end

