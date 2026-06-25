open Syntax

(* [X:->u] *)
type substitution = tyvar * ty
(* if S = [X1:->X2], [X2:->u1], then S(X1)=u1 *)
type substitutions = substitution list

val subst_type : substitutions -> ty -> ty

val subst_coercion : monotonic:bool -> substitutions -> coercion -> coercion

val subst_mf : substitutions -> matchform -> matchform

module CC : sig
	open Syntax.CC
	val subst_exp : monotonic:bool -> substitutions -> exp -> exp
end

module KNorm : sig
	open Syntax.KNorm
	val subst_exp : monotonic:bool -> substitutions -> exp -> exp
end