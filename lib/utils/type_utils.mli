open Syntax

exception Type_utils_bug of string

val is_base_type : ty -> bool

val is_static_type : ty -> bool

val is_ground : ty -> bool

val is_equal : ty -> ty -> bool

val is_consistent : ty -> ty -> bool

(** Returns a fresh type variable. *)
val fresh_tyvar : unit -> ty

val tyarg_to_ty : Syntax.tyarg -> ty

val tysc_of_ty : ty -> tysc

val tag_of_ty : ty -> tag

val type_of_tag : tag -> ty