open Syntax

(** Type error in the given program. *)
exception Type_error of string
exception Type_bug of string

val type_of_binop : binop -> ty * ty * ty

val type_of_mf : matchform -> id list -> ty * id list

val env_of_mf : tysc Environment.t -> ty ->  matchform -> tysc Environment.t

module ITGL : sig
  open Syntax.ITGL

  val is_pure_value : tysc Environment.t -> exp -> bool
  val type_of_program : tysc Environment.t -> program -> (program * ty)

  val closure_tyvars1 : ty -> tysc Environment.t -> exp -> tyvar list
end

val type_of_coercion : coercion -> ty

module CC : sig
  open Syntax.CC

  val type_of_program : tysc Environment.t -> program -> ty
end
