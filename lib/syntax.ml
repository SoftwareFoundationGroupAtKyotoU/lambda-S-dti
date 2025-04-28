open Utils.Error

(** Identifier used for names of variables. *)
type id = string

(** Module used to implement environment and type environment. *)
module Environment = Map.Make (
  struct
    type t = id
    let compare (x : id) y = compare x y
  end
  )

type binop = Plus | Minus | Mult | Div | Mod | Eq | Neq | Lt | Lte | Gt | Gte

type ty =
  | TyDyn
  | TyVar of tyvar
  | TyInt
  | TyBool
  | TyUnit
  | TyFun of ty * ty
and
(* int value is used to identify type variables.
 * ty option ref value is used to implement instantiation.
 * Some u means this variable is instantiated with u. *)
  tyvar = int * ty option ref

type tysc = TyScheme of tyvar list * ty

let tysc_of_ty u = TyScheme ([], u)

(** Returns true if the given argument is a ground type. Othewise returns false. *)
let is_ground = function
  | TyInt | TyBool | TyUnit -> true
  | TyFun (u1, u2) when u1 = TyDyn && u2 = TyDyn -> true
  | _ -> false

let rec is_base_type = function
  | TyBool | TyInt | TyUnit -> true
  | TyVar (_, { contents = Some u }) -> is_base_type u
  | _ -> false

  let rec is_consistent u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some u1 }), u2
  | u1, TyVar (_, { contents = Some u2 }) ->
    is_consistent u1 u2
  | TyDyn, TyDyn
  | TyBool, TyBool
  | TyInt, TyInt
  | TyUnit, TyUnit
  | _, TyDyn
  | TyDyn, _ -> true
  | TyVar (a1, _), TyVar (a2, _) when a1 = a2 -> true
  | TyFun (u11, u12), TyFun (u21, u22) ->
    (is_consistent u11 u21) && (is_consistent u12 u22)
  | _ -> false

(* Set of type variables used for let polymorphism *)

(** Module for a set of type variables. *)
module TV = struct
  include Set.Make (
    struct
      type t = tyvar
      let compare (a1, _ : tyvar) (a2, _) = compare a1 a2
    end
    )
  let big_union vars = List.fold_right union vars empty
end

(** Returns a set of free type variables in a given type. *)
let rec ftv_ty: ty -> TV.t = function
  | TyVar (_, { contents = None } as x) -> TV.singleton x
  | TyVar (_, { contents = Some u }) -> ftv_ty u
  | TyFun (u1, u2) -> TV.union (ftv_ty u1) (ftv_ty u2)
  | _ -> TV.empty

let ftv_tysc: tysc -> TV.t = function
  | TyScheme (xs, u) -> TV.diff (ftv_ty u) (TV.of_list xs)

let ftv_tyenv (env: tysc Environment.t): TV.t =
  Environment.fold (fun _ us vars -> TV.union vars (ftv_tysc us)) env TV.empty

type tyarg = Ty of ty | TyNu

type polarity = Pos | Neg

(** Returns the negation of the given polarity. *)
let neg = function Pos -> Neg | Neg -> Pos

type tag = I | B | U | Ar | V of tyvar

(* type coercion =
  | CInj of tag
  | CProj of tag * (range * polarity)
  | CFun of coercion * coercion
  | CId of ty
  | CSeq of coercion * coercion
  | CFail of tag * (range * polarity) * tag *)

type coercion =
  | CInj of ty
  | CProj of ty * (range * polarity)
  | CFun of coercion * coercion
  | CId of ty
  | CSeq of coercion * coercion
  | CFail of ty * (range * polarity) * ty

let is_d = function
  | CSeq (CId u, CInj _) when u <> TyDyn -> true
  | CSeq (CFun _, CInj _)
  | CFun _ -> true
  | _ -> false

let rec ftv_coercion = function
  | CInj u -> ftv_ty u
  | CProj (u, _) -> ftv_ty u
  | CFun (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CId u -> ftv_ty u
  | CSeq (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CFail (u1, _, u2) -> TV.union (ftv_ty u1) (ftv_ty u2)

(** Syntax of the surface language, the ITGL with extensions. *)
module ITGL = struct
  type constr =
    | CEqual of ty * ty
    | CConsistent of ty * ty

  type exp =
    | Var of range * id * ty list ref
    | IConst of range * int
    | BConst of range * bool
    | UConst of range
    | BinOp of range * binop * exp * exp
    | AscExp of range * exp * ty
    | IfExp of range * exp * exp * exp
    | FunEExp of range * id * ty * exp
    | FunIExp of range * id * ty * exp
    | FixEExp of range * id * id * ty * ty * exp
    | FixIExp of range * id * id * ty * ty * exp
    | AppExp of range * exp * exp
    | LetExp of range * id * exp * exp

  let range_of_exp = function
    | Var (r, _, _)
    | IConst (r, _)
    | BConst (r, _)
    | UConst r
    | AscExp (r, _, _)
    | BinOp (r, _, _, _)
    | IfExp (r, _, _, _)
    | FunEExp (r, _, _, _)
    | FunIExp (r, _, _, _)
    | FixEExp (r, _, _, _, _, _)
    | FixIExp (r, _, _, _, _, _)
    | AppExp (r, _, _)
    | LetExp (r, _, _, _) -> r

  let rec tv_exp: exp -> TV.t = function
    | Var _
    | IConst _
    | BConst _
    | UConst _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | AscExp (_, e, u) -> TV.union (tv_exp e) (ftv_ty u)
    | IfExp (_, e1, e2, e3) -> TV.big_union @@ List.map tv_exp [e1; e2; e3]
    | FunEExp (_, _, u, e)
    | FunIExp (_, _, u, e) -> TV.union (ftv_ty u) (tv_exp e)
    | FixEExp (_, _, _, u1, _, e)
    | FixIExp (_, _, _, u1, _, e) -> TV.union (ftv_ty u1) (tv_exp e)
    | AppExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | LetExp (_, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)

  let rec ftv_exp: exp -> TV.t = function
    | Var _
    | IConst _
    | BConst _
    | UConst _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | AscExp (_, e, u) -> TV.union (ftv_exp e) (ftv_ty u)
    | IfExp (_, e1, e2, e3) -> TV.big_union @@ List.map ftv_exp [e1; e2; e3]
    | FunEExp (_, _, u, e) -> TV.union (ftv_ty u) (ftv_exp e)
    | FunIExp (_, _, _, e) -> ftv_exp e
    | FixEExp (_, _, _, u1, _, e) -> TV.union (ftv_ty u1) (ftv_exp e)
    | FixIExp (_, _, _, _, _, e) -> ftv_exp e
    | AppExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | LetExp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)

  type program =
    | Exp of exp
    | LetDecl of id * exp
end

(** Syntax of the blame calculus with dynamic type inference. *)
module LS = struct
  type exp =
    | Var of id * tyarg list
    | IConst of int
    | BConst of bool
    | UConst
    | BinOp of binop * exp * exp
    | IfExp of exp * exp * exp
    | FunExp of id * ty * exp
    | FixExp of id * id * ty * ty * exp
    | AppExp of exp * exp
    | CAppExp of exp * coercion
    | LetExp of id * tyvar list * exp * exp

  let (*rec*) is_value = function
    | Var _
    | IConst _
    | BConst _
    | UConst
    | FunExp _
    | FixExp _ -> true
    (*| CoercionExp (_, v, TyFun _, TyFun _, _) when is_value v -> true
    | CoercionExp (_, v, g, TyDyn, _) when is_value v && is_ground g -> true*)
    | _ -> false 

  let ftv_tyarg = function
    | Ty ty -> ftv_ty ty
    | TyNu -> TV.empty

  let rec ftv_exp: exp -> TV.t = function
    | Var (_, us) -> List.fold_right TV.union (List.map ftv_tyarg us) TV.empty
    | IConst _
    | BConst _
    | UConst -> TV.empty
    | BinOp (_, f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | IfExp (f1, f2, f3) ->
      List.fold_right TV.union (List.map ftv_exp [f1; f2; f3]) TV.empty
    | FunExp (_, u, e) -> TV.union (ftv_ty u) (ftv_exp e)
    | FixExp (_, _, u1, _, f) -> TV.union (ftv_ty u1) (ftv_exp f)
    | AppExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | CAppExp (f, c) ->
      TV.union (ftv_exp f) (ftv_coercion c)
    | LetExp (_, xs, f1, f2) ->
      TV.union (TV.diff (ftv_exp f1) (TV.of_list xs)) (ftv_exp f2)

  type program =
    | Exp of exp
    | LetDecl of id * tyvar list * exp
  
  type value =
    | IntV of int
    | BoolV of bool
    | UnitV
    | FunV of ((tyvar list * ty list) -> value -> value)
    | CoerceV of value * coercion
end

module LS1 = struct
  type exp =
    | Var of id * tyarg list
    | IConst of int
    | BConst of bool
    | UConst
    | BinOp of binop * exp * exp
    | IfExp of exp * exp * exp
    | FunExp of (id * ty) * id * exp
    | FixExp of (id * id * ty * ty) * id * exp
    | AppExp of exp * exp * exp
    | CAppExp of exp * exp
    | CSeqExp of exp * exp
    | LetExp of id * tyvar list * exp * exp
    | CoercionExp of coercion

  let (*rec*) is_value = function
    | Var _
    | IConst _
    | BConst _
    | UConst
    | FunExp _
    | FixExp _
    | CoercionExp _ -> true
    (*| CoercionExp (_, v, TyFun _, TyFun _, _) when is_value v -> true
    | CoercionExp (_, v, g, TyDyn, _) when is_value v && is_ground g -> true*)
    | _ -> false

  let ftv_tyarg = function
    | Ty ty -> ftv_ty ty
    | TyNu -> TV.empty

  let rec ftv_exp: exp -> TV.t = function
    | Var (_, us) -> List.fold_right TV.union (List.map ftv_tyarg us) TV.empty
    | IConst _
    | BConst _
    | UConst -> TV.empty
    | BinOp (_, f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | IfExp (f1, f2, f3) ->
      List.fold_right TV.union (List.map ftv_exp [f1; f2; f3]) TV.empty
    | FunExp ((_, u), _, e) -> TV.union (ftv_ty u) (ftv_exp e)
    | FixExp ((_, _, u1, _), _, f) -> TV.union (ftv_ty u1) (ftv_exp f)
    | AppExp (f1, f2, f3) -> TV.union (ftv_exp f1) (TV.union (ftv_exp f2) (ftv_exp f3))
    | CAppExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | CSeqExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | LetExp (_, xs, f1, f2) ->
      TV.union (TV.diff (ftv_exp f1) (TV.of_list xs)) (ftv_exp f2)
    | CoercionExp c -> ftv_coercion c

  type program =
    | Exp of exp
    | LetDecl of id * tyvar list * exp

  (*let tag_to_ty = function
    | I -> TyInt
    | B -> TyBool
    | U -> TyUnit
    | Ar -> TyFun (TyDyn, TyDyn)*)

  type value =
    | IntV of int
    | BoolV of bool
    | UnitV
    | FunV of ((tyvar list * ty list) -> (value * value) -> value)
    | CoerceV of value * coercion
    | CoercionV of coercion
end

module KNorm = struct
  type exp =
    | Var of id
    | IConst of int
    | UConst
    | Add of id * id
    | Sub of id * id
    | Mul of id * id
    | Div of id * id
    | Mod of id * id
    | IfEqExp of id * id * exp * exp
    | IfLteExp of id * id * exp * exp
    | AppExp of id * id
    | AppTy of id * tyvar list * tyarg list
    | CastExp of range * id * ty * ty * polarity
    | LetExp of id * ty * exp * exp
    | LetRecExp of id * ty * tyvar list * (id * ty) * exp * exp

  type program =
    | Exp of exp
    | LetDecl of id * ty * exp
    | LetRecDecl of id * ty * tyvar list * (id * ty) * exp

  type tag = I | B | U | Ar

  let tag_to_ty = function
    | I -> TyInt
    | B -> TyBool
    | U -> TyUnit
    | Ar -> TyFun (TyDyn, TyDyn)

  type value =
    | IntV of int
    | UnitV
    | FunV of ((tyvar list * ty list) -> value -> value)
    | Tagged of tag * value
end

module Cls = struct
  exception Cls_syntax_bug of string

  type label = string

  let to_label (x:id) = (x:label)

  type closure = { entry : label; actual_fv : id list }

  type ftv = { ftvs : tyarg list; offset : int }

  type exp =
    | Var of id
    | Int of int
    | Unit
    | Add of id * id
    | Sub of id * id
    | Mul of id * id
    | Div of id * id
    | Mod of id * id
    | IfEq of id * id * exp * exp
    | IfLte of id * id * exp * exp
    | AppTy of id * int * tyarg list
    | MakeCls of id * ty * closure * exp
    | AppCls of id * id
    | AppDir of label * id
    | Cast of id * ty * ty * range * polarity
    | Let of id * ty * exp * exp
    | MakeLabel of id * ty * label * exp
    | MakePolyLabel of id * ty * label * ftv * exp
    | MakePolyCls of id * ty * closure * ftv * exp
    | SetTy of tyvar * exp
    | Insert of id * exp

  type fundef = { name : label * ty; tvs : tyvar list * int; arg : id * ty; formal_fv : (id * ty) list; body : exp }

  module V = struct
    include Set.Make (
      struct
        type t = id
        let compare (a1:id) a2 = compare a1 a2
      end
      )
    let big_union vars = List.fold_right union vars empty
  end

  let rec fv = function
    | Var id -> V.singleton id
    | Int _ | Unit -> V.empty
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) -> V.of_list [x; y]
    | IfEq (x, y, f1, f2) | IfLte (x, y, f1, f2) -> V.big_union [V.of_list [x; y]; fv f1; fv f2]
    | AppTy (x, _, _) -> V.singleton x
    | SetTy (_, f) -> fv f
    | AppDir (_, y) -> V.singleton y
    | AppCls (x, y) -> V.of_list [x; y]
    | Cast (x, _, _, _, _) -> V.singleton x
    | MakeLabel (x, _, _, f) -> V.remove x (fv f)
    | MakePolyLabel (x, _, _, _, f) -> V.remove x (fv f)
    | MakeCls (x, _, { entry = _; actual_fv = vs }, f) -> V.remove x (V.union (V.of_list vs) (fv f))
    | MakePolyCls (x, _, { entry = _; actual_fv = vs }, _, f) -> V.remove x (V.union (V.of_list vs) (fv f))
    | Let (x, _, c, f) -> V.union (fv c) (V.remove x (fv f))
    | Insert _ -> raise @@ Cls_syntax_bug "Insert was applied to fv"

  type program = Prog of TV.t * fundef list * exp

end