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
  | TyList of ty
and tyvar = int * ty option ref
(* int value is used to identify type variables.
 * ty option ref value is used to implement instantiation.
 * Some u means this variable is instantiated with u. *)
  
type tysc = TyScheme of tyvar list * ty

(* creates monomorphic typescheme *)
let tysc_of_ty u = TyScheme ([], u) 

(** Returns true if the given argument is a ground type. Othewise returns false. *)
let rec is_ground = function
  | TyInt | TyBool | TyUnit -> true (* base type *)
  | TyFun (TyDyn, TyDyn) -> true    (* ★ → ★ *)
  | TyList TyDyn -> true
  | TyVar (_, { contents = Some u }) -> is_ground u
  | _ -> false

let rec is_base_type = function
  | TyBool | TyInt | TyUnit -> true
  | TyVar (_, { contents = Some u }) -> is_base_type u
  | _ -> false

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
  | _ -> false

(* Set of type variables used for let polymorphism *)
(* Module for a set of type variables. *)
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
  | TyVar (_, { contents = None } as tv) -> TV.singleton tv
  | TyVar (_, { contents = Some u }) -> ftv_ty u
  | TyFun (u1, u2) -> TV.union (ftv_ty u1) (ftv_ty u2)
  | TyList u -> ftv_ty u
  | _ -> TV.empty

let ftv_tysc: tysc -> TV.t = function
  | TyScheme (xs, u) -> TV.diff (ftv_ty u) (TV.of_list xs)

let ftv_tyenv (env: tysc Environment.t): TV.t =
  Environment.fold (fun _ us vars -> TV.union vars (ftv_tysc us)) env TV.empty

type tyarg = Ty of ty | TyNu

type matchform = (*match式でmatchさせることのできる形の種類を定義*)
  | MatchVar of id * ty                      (*変数でmatchさせるMatchVar*)
  (* | MatchAsc of matchform * ty *)
  | MatchILit of int                    (*整数とmatchするMatchILit*)
  | MatchBLit of bool                   (*bool値とmatchするMatchBLit*)
  | MatchULit
  | MatchNil of ty                (*空列とmatchするMatchEmptyList*)
  | MatchCons of matchform * matchform  (*リストとmatchするMatchList*)
  | MatchWild of ty

let rec tv_matchform : matchform -> TV.t = function
  | MatchVar (_, u) -> ftv_ty u
  | MatchILit _ | MatchBLit _ | MatchULit | MatchWild _ -> TV.empty
  | MatchNil u -> ftv_ty u
  (* | MatchAsc (mf, u) -> TV.union (tv_matchform mf) (ftv_ty u) *)
  | MatchCons (mf1, mf2) -> TV.union (tv_matchform mf1) (tv_matchform mf2)

let rec ftv_matchform : matchform -> TV.t = function
  | MatchVar _ | MatchILit _ | MatchBLit _ | MatchULit | MatchWild _ -> TV.empty
  | MatchNil _ -> TV.empty
  (* | MatchAsc (mf, u) -> TV.union (ftv_matchform mf) (ftv_ty u) *)
  | MatchCons (mf1, mf2) -> TV.union (ftv_matchform mf1) (ftv_matchform mf2)

type polarity = Pos | Neg

(** Returns the negation of the given polarity. *)
let neg = function Pos -> Neg | Neg -> Pos

type tag = I | B | U | Ar | Li

type coercion =
  | CInj of tag
  | CProj of tag * (range * polarity)
  | CTvInj of tyvar * (range * polarity)
  | CTvProj of tyvar * (range * polarity)
  | CTvProjInj of tyvar * (range * polarity) * (range * polarity)
  | CFun of coercion * coercion
  | CList of coercion
  | CId of ty
  | CSeq of coercion * coercion
  | CFail of tag * (range * polarity) * tag

let is_d = function
  | CSeq (CId u, CInj _) when u <> TyDyn -> true
  | CSeq (CFun _, CInj _)
  | CSeq (CList _, CInj _)
  | CFun _ 
  | CList _ -> true (* TODO : CFun (s, t) when s <> CId _ or t <> CId _ *)
  | _ -> false

let rec ftv_coercion = function
  | CInj _ | CProj _ -> TV.empty
  | CTvInj (tv, _) | CTvProj (tv, _) | CTvProjInj (tv, _, _) -> TV.singleton tv
  | CFun (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CList c -> ftv_coercion c
  | CId u -> ftv_ty u
  | CSeq (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CFail _ -> TV.empty

let type_of_tag = function
  | I -> TyInt
  | B -> TyBool
  | U -> TyUnit
  | Ar -> TyFun (TyDyn, TyDyn)
  | Li -> TyList TyDyn

let rec tag_of_ty = function
  | TyInt -> I
  | TyBool -> B
  | TyUnit -> U
  | TyFun (TyDyn, TyDyn) -> Ar
  | TyList TyDyn -> Li
  | TyVar (_, {contents = Some u}) -> tag_of_ty u
  | _ -> assert false
  (* | _ -> raise @@ Type_bug "tag_of_ty: invalid type" *)

exception Blame of range * polarity

(** Syntax of the surface language, the ITGL with extensions. *)
module ITGL = struct
  (* for typing *)
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
    | MatchExp of range * exp * (matchform * exp) list
    | LetExp of range * id * exp * exp
    | NilExp of range * ty
    | ConsExp of range * exp * exp

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
    | MatchExp (r, _, _)
    | LetExp (r, _, _, _) 
    | NilExp (r, _) 
    | ConsExp (r, _, _) -> r
    
  (* for polymorphic let declaration *)
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
    | MatchExp (_, e, ms) -> TV.union (tv_exp e) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (tv_matchform mf) (tv_exp e)) ms)
    | LetExp (_, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | NilExp (_, u) -> ftv_ty u
    | ConsExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)

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
    | MatchExp (_, e, ms) -> TV.union (ftv_exp e) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (ftv_matchform mf) (ftv_exp e)) ms)
    | LetExp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | NilExp _ -> TV.empty
    | ConsExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)

  type program =
    | Exp of exp
    | LetDecl of id * exp
end

(** Syntax of the blame calculus with dynamic type inference. *)
module CC = struct
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
    | CastExp of exp * ty * ty * (range * polarity)
    | MatchExp of exp * (matchform * exp) list
    | LetExp of id * tyvar list * exp * exp
    | NilExp of ty
    | ConsExp of exp * exp

  (* let rec is_value = function
    | Var _
    | IConst _
    | BConst _
    | UConst
    | FunExp _
    | FixExp _ 
    | NilExp _ -> true
    | CastExp (_, v, TyFun _, TyFun _, _) -> is_value v
    | CastExp (_, v, TyList _, TyList _, _) -> is_value v
    | CastExp (_, v, g, TyDyn, _) -> is_value v && is_ground g
    | ConsExp (v1, v2) -> is_value v1 && is_value v2
    | _ -> false  *)

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
    | CAppExp (f, c) -> TV.union (ftv_exp f) (ftv_coercion c)
    | CastExp (f, u1, u2, _) -> TV.union (ftv_exp f) @@ TV.union (ftv_ty u1) (ftv_ty u2)
    | MatchExp (f, ms) ->
      TV.union (ftv_exp f) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (ftv_matchform mf) (ftv_exp e)) ms)
    | LetExp (_, xs, f1, f2) ->
      TV.union (TV.diff (ftv_exp f1) (TV.of_list xs)) (ftv_exp f2)
    | NilExp _ -> TV.empty
    | ConsExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)

  type program =
    | Exp of exp
    | LetDecl of id * tyvar list * exp
  
  type value =
    | IntV of int
    | BoolV of bool
    | UnitV
    | FunV of ((tyvar list * ty list) -> value -> value)
    | Tagged of tag * value
    | NilV
    | ConsV of value * value
end

module LS1 = struct
  type exp =
    | Var of id * tyarg list
    | IConst of int
    | BConst of bool
    | UConst
    | BinOp of binop * exp * exp
    | IfExp of exp * exp * exp
    | FunSExp of (id * ty) * id * exp
    | FixSExp of (id * id * ty * ty) * id * exp
    | AppDExp of exp * exp * exp
    | CAppExp of exp * exp
    | CSeqExp of exp * exp
    | MatchExp of exp * (matchform * exp) list
    | LetExp of id * tyvar list * exp * exp
    | CoercionExp of coercion
    | NilExp of ty
    | ConsExp of exp * exp
    | FunAExp of (id * ty) * id * (exp * exp)
    | FixAExp of (id * id * ty * ty) * id * (exp * exp)
    | AppMExp of exp * exp

  (* let rec is_value = function
    | Var _
    | IConst _
    | BConst _
    | UConst
    | FunExp _
    | FixExp _
    | CoercionExp _ 
    | FunExp_alt _
    | FixExp_alt _ -> true
    (*| CoercionExp (_, v, TyFun _, TyFun _, _) when is_value v -> true
    | CoercionExp (_, v, g, TyDyn, _) when is_value v && is_ground g -> true*)
    | _ -> false *)

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
    | FunSExp ((_, u), _, f) -> TV.union (ftv_ty u) (ftv_exp f)
    | FixSExp ((_, _, u1, _), _, f) -> TV.union (ftv_ty u1) (ftv_exp f)
    | AppDExp (f1, f2, f3) -> TV.union (ftv_exp f1) (TV.union (ftv_exp f2) (ftv_exp f3))
    | CAppExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | CSeqExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | MatchExp (f, ms) ->
      TV.union (ftv_exp f) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (ftv_matchform mf) (ftv_exp e)) ms)
    | LetExp (_, xs, f1, f2) ->
      TV.union (TV.diff (ftv_exp f1) (TV.of_list xs)) (ftv_exp f2)
    | CoercionExp c -> ftv_coercion c
    | NilExp _ -> TV.empty
    | ConsExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | FunAExp ((_, u), _, (f1, f2)) -> TV.union (ftv_ty u) @@ TV.union (ftv_exp f1) (ftv_exp f2)
    | FixAExp ((_, _, u1, _), _, (f1, f2)) -> TV.union (ftv_ty u1) @@ TV.union (ftv_exp f1) (ftv_exp f2)
    | AppMExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)

  type program =
    | Exp of exp
    | LetDecl of id * tyvar list * exp

  type value =
    | IntV of int
    | BoolV of bool
    | UnitV
    | FunSV of ((tyvar list * ty list) -> (value * value) -> value)
    | CoerceV of value * coercion
    | CoercionV of coercion
    | NilV
    | ConsV of value * value
    | FunAV of ((tyvar list * ty list) -> ((value -> value) * ((value * value) -> value)))
end

module KNorm = struct
  type exp =
    | Var of id
    | IConst of int
    | Add of id * id
    | Sub of id * id
    | Mul of id * id
    | Div of id * id
    | Mod of id * id
    | Nil
    | Cons of id * id
    | Hd of id
    | Tl of id
    | IfEqExp of id * id * exp * exp
    | IfLteExp of id * id * exp * exp
    | AppMExp of id * id
    | AppDExp of id * (id * id)
    | AppTy of id * tyvar list * tyarg list
    | CAppExp of id * id
    | CastExp of id * ty * ty * (range * polarity)
    | CSeqExp of id * id
    | MatchExp of id * (matchform * exp) list
    | CoercionExp of coercion
    | LetExp of id * exp * exp
    | LetRecSExp of id * tyvar list * (id * id) * exp * exp
    | LetRecAExp of id * tyvar list * (id * id) * (exp * exp) * exp
    | LetRecBExp of id * tyvar list * id * exp * exp

  type program =
    | Exp of exp
    | LetDecl of id * exp
    | LetRecSDecl of id * tyvar list * (id * id) * exp
    | LetRecADecl of id * tyvar list * (id * id) * (exp * exp)
    | LetRecBDecl of id * tyvar list * id * exp

  type value =
    | IntV of int
    | NilV
    | ConsV of value * value
    | Tagged of tag * value
    | CoerceV of value * coercion
    | CoercionV of coercion
    | FunSV of ((tyvar list * ty list) -> (value * value) -> value)
    | FunAV of ((tyvar list * ty list) -> ((value -> value) * ((value * value) -> value)))
    | FunBV of ((tyvar list * ty list) -> value -> value)
end

module Cls = struct
  exception Cls_syntax_bug of string

  type label = string

  let to_label (x:id) = (x:label)

  let to_id (x:label) = (x:id)

  type closure = { entry : label; actual_fv : id list }

  type ftv = { ftvs : tyarg list; offset : int }

  type coercion =
  | Id
  | SeqInj of coercion * tag
  | SeqProj of tag * (int * polarity) * coercion
  | TvInj of tyvar * (int * polarity)
  | TvProj of tyvar * (int * polarity)
  | Fun of coercion * coercion
  | List of coercion

  type exp =
    | Var of id
    | Int of int
    | Nil
    | Add of id * id
    | Sub of id * id
    | Mul of id * id
    | Div of id * id
    | Mod of id * id
    | Cons of id * id
    | Hd of id
    | Tl of id
    | IfEq of id * id * exp * exp
    | IfLte of id * id * exp * exp
    | Match of id * (matchform * exp) list
    | AppTy of id * int * tyarg list
    | AppDCls of id * (id * id)
    | AppDDir of label * (id * id)
    | AppMCls of id * id
    | AppMDir of label * id
    | Cast of id * ty * ty * (int * polarity)
    | CApp of id * id
    | CSeq of id * id
    | Coercion of coercion
    | Let of id * exp * exp
    | MakeCls of id * closure * exp
    | MakeLabel of id * label * exp
    | MakePolyLabel of id * label * ftv * exp
    | MakePolyCls of id * closure * ftv * exp
    | SetTy of tyvar * exp
    | Insert of id * exp

  type fundef = 
    | FundefD of { name : label ; tvs : tyvar list * int; arg : id * id; formal_fv : id list; body : exp }
    | FundefM of { name : label ; tvs : tyvar list * int; arg : id; formal_fv : id list; body : exp }
    
  module V = struct
    include Set.Make (
      struct
        type t = id
        let compare (a1:id) a2 = compare a1 a2
      end
      )
    let big_union vars = List.fold_right union vars empty
  end

  let rec fv_mf = function
    | MatchILit _ | MatchBLit _ | MatchULit | MatchWild _ | MatchNil _ -> V.empty
    | MatchVar (x, _) -> V.singleton x
    | MatchCons (mf1, mf2) -> V.big_union [fv_mf mf1; fv_mf mf2]

  let rec fv = function
    | Var x | Hd x | Tl x  -> V.singleton x
    | Int _ | Nil -> V.empty
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) | Cons (x, y) -> V.of_list [x; y]
    | IfEq (x, y, f1, f2) | IfLte (x, y, f1, f2) -> V.big_union [V.of_list [x; y]; fv f1; fv f2]
    | Match (x, ms) -> 
      V.big_union (V.singleton x :: List.map (fun (mf, f) -> V.union (fv_mf mf) (fv f)) ms)
    | AppTy (x, _, _) -> V.singleton x
    | SetTy (_, f) -> fv f
    | AppDDir (_, (y, z)) -> V.of_list [y; z]
    | AppDCls (x, (y, z)) -> V.of_list [x; y; z]
    | AppMDir (_, y) -> V.singleton y
    | AppMCls (x, y) -> V.of_list [x; y]
    | Cast (x, _, _, _) -> V.singleton x
    | CApp (x, y) -> V.of_list [x; y]
    | CSeq (x, y) -> V.of_list [x; y]
    | Coercion _ -> V.empty
    | MakeLabel (x, _, f) -> V.remove x (fv f)
    | MakePolyLabel (x, _, _, f) -> V.remove x (fv f)
    | MakeCls (x, { entry = _; actual_fv = vs }, f) -> V.remove x (V.union (V.of_list vs) (fv f))
    | MakePolyCls (x, { entry = _; actual_fv = vs }, _, f) -> V.remove x (V.union (V.of_list vs) (fv f))
    | Let (x, c, f) -> V.union (fv c) (V.remove x (fv f))
    | Insert _ -> raise @@ Cls_syntax_bug "Insert was applied to fv"

  type program = Prog of TV.t * range list * fundef list * exp

end