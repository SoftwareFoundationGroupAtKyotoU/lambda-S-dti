open Syntax

exception Type_utils_bug of string

(* for ty *)

(** Returns true if the given argument is a ground type. Othewise returns false. *)
let rec is_ground = function
  | TyInt | TyBool | TyUnit -> true (* base type *)
  | TyFun (TyDyn, TyDyn) -> true    (* ★ → ★ *)
  | TyList TyDyn -> true
  | TyTuple us -> List.fold_left (fun b u -> b && u = TyDyn) true us
  | TyRef TyDyn -> true
  | TyVar (_, { contents = Some u }) -> is_ground u
  | _ -> false

(* check whether the given argument belongs to ι *)
let rec is_base_type = function
  | TyBool | TyInt | TyUnit -> true
  | TyVar (_, { contents = Some u }) -> is_base_type u
  | _ -> false

(* u1 ~ u2 *)
let rec is_consistent u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some u1 }), u2
  | u1, TyVar (_, { contents = Some u2 }) ->
    is_consistent u1 u2
  | TyBool, TyBool | TyInt, TyInt | TyUnit, TyUnit -> true
  | TyVar (a1, _), TyVar (a2, _) when a1 = a2 -> true
  | TyDyn, _ | _, TyDyn -> true
  | TyFun (u11, u12), TyFun (u21, u22) ->
    (is_consistent u11 u21) && (is_consistent u12 u22)
  | TyList u1, TyList u2 -> is_consistent u1 u2
  | TyTuple us1, TyTuple us2 ->
    begin try
      List.fold_left2 (fun b u1 u2 -> b && is_consistent u1 u2) true us1 us2
    with Invalid_argument _ -> false end
  | TyRef u1, TyRef u2 -> is_consistent u1 u2
  | _ -> false

let rec is_equal u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some u1 }), u2
  | u1, TyVar (_, { contents = Some u2 }) -> is_equal u1 u2
  | TyDyn, TyDyn
  | TyBool, TyBool
  | TyInt, TyInt
  | TyUnit, TyUnit -> true
  | TyVar (a1, _), TyVar (a2, _) when a1 = a2 -> true
  | TyFun (u11, u12), TyFun (u21, u22) ->
    (is_equal u11 u21) && (is_equal u12 u22)
  | TyList u1, TyList u2 -> is_equal u1 u2
  | TyTuple us1, TyTuple us2 -> List.fold_left2 (fun b u1 u2 -> b && u1 = u2) true us1 us2
  | TyRef u1, TyRef u2 -> is_equal u1 u2
  | _ -> false

let rec is_static_type = function
  | TyDyn -> false
  | TyVar (_, { contents = Some u }) -> is_static_type u
  | TyFun (u1, u2) -> (is_static_type u1) && (is_static_type u2)
  | TyList u -> is_static_type u
  | TyTuple us -> List.fold_left (fun b u -> b && is_static_type u) true us
  | TyRef u -> is_static_type u
  | _ -> true

let fresh_tyvar =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1;
    TyVar (!counter, ref None)
  in body

(* for tysc *)

(* creates monomorphic typescheme *)
let tysc_of_ty u = TyScheme ([], u) 

(* When you're sure that this tyarg does not contain ν
 * you can convert it to ty *)
let tyarg_to_ty = function
  | Ty u -> u
  | TyNu -> raise @@ Type_utils_bug "failed to cast tyarg to ty"

(* for tag *)
let type_of_tag = function
  | I -> TyInt
  | B -> TyBool
  | U -> TyUnit
  | Fn -> TyFun (TyDyn, TyDyn)
  | Li -> TyList TyDyn
  | Tp n -> TyTuple (List.init n (fun _ -> TyDyn))
  | Rf -> TyRef TyDyn

let rec tag_of_ty = function
  | TyInt -> I
  | TyBool -> B
  | TyUnit -> U
  | TyFun (TyDyn, TyDyn) -> Fn
  | TyList TyDyn -> Li
  | TyTuple us ->
    if List.fold_left (fun b u -> b && u = TyDyn) true us then Tp (List.length us) else assert false
  | TyRef TyDyn -> Rf
  | TyVar (_, {contents = Some u}) -> tag_of_ty u
  | _ -> assert false
