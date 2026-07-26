open Syntax

exception Eval_bug of string

module CC : sig
  open Syntax.CC
  
  val eval_program : config:Config.t -> value Environment.t -> program -> value Environment.t * id * value
  
  val coerce : config:Config.t -> value -> coercion -> (value * ty) list -> (value * (value * ty) list)

  val consume :  config:Config.t ->(value * ty) list -> unit
end 


