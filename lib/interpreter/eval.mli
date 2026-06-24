open Syntax

exception Eval_bug of string

val compose : config:Config.t -> coercion -> coercion -> coercion

val tag_of_ty : ty -> tag

module CC : sig
  open Syntax.CC
  
  val eval_program : config:Config.t -> value Environment.t -> program -> value Environment.t * id * value
  
  val coerce : config:Config.t -> value -> coercion -> ((value * ty) ref * ty) list -> (value * ((value * ty) ref * ty) list)

  val consume :  config:Config.t ->((value * ty) ref * ty) list -> unit
end 

module KNorm : sig
  open Syntax.KNorm

  val eval_program : config:Config.t -> value Environment.t -> program -> value Environment.t * id * value
  
  val coerce : config:Config.t -> value -> coercion -> value
end

