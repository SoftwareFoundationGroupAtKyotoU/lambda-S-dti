open Syntax

(** Type error in the given program. *)
exception Type_error of string
exception Type_bug of string

val type_of_binop : binop -> ty * ty * ty

module ITGL : sig
  open Syntax.ITGL

  val type_of_meet: ty -> ty -> ty

  val is_pure_value : tysc Environment.t -> exp -> bool
  val type_of_program : tysc Environment.t -> program -> (program * ty)

  val closure_tyvars1 : ty -> tysc Environment.t -> exp -> tyvar list
end

val type_of_coercion : coercion -> ty

module CC : sig
  open Syntax.CC

  val type_of_program : tysc Environment.t -> program -> ty
end
