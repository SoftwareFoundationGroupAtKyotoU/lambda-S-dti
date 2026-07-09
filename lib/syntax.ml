open Utils.Error

(* === Definitions for id === *)

(** Identifier used for names of variables. *)
type id = string

(** Module used to implement value environment and type environment. *)
(* Mapping from id *)
module Environment = Map.Make (
  struct
    type t = id
    let compare (x : id) y = compare x y
  end
  )

(* Set of id *)
module V = struct
  include Set.Make (
    struct
      type t = id
      let compare (a1:id) a2 = compare a1 a2
    end
    )
  let big_union vars = List.fold_right union vars empty
end

(* === Definitions for ty === *)

type ty =
  | TyDyn
  | TyVar of tyvar
  | TyInt
  | TyBool
  | TyUnit
  | TyFun of ty * ty
  | TyList of ty
  | TyTuple of ty list
  | TyRef of ty
  | TyCoercion of ty * ty
and tyvar = int * ty option ref
(* int value is used to identify type variables.
 * ty option ref value is used to implement instantiation.
 * Some u means this variable is instantiated with u. *)

type constr =
  | CEqual of ty * ty
  | CConsistent of ty * ty
  
type tysc = TyScheme of tyvar list * ty

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

type tyarg = Ty of ty | TyNu

(* === Definitions for binop === *)

type binop = Plus | Minus | Mult | Div | Mod | Eq | Neq | Lt | Lte | Gt | Gte

(* === Definitions for matchform === *)

type matchform = (*match式でmatchさせることのできる形の種類を定義*)
  | MatchVar of id * ty                      (*変数でmatchさせるMatchVar*)
  (* | MatchAsc of matchform * ty *)
  | MatchILit of int                    (*整数とmatchするMatchILit*)
  | MatchBLit of bool                   (*bool値とmatchするMatchBLit*)
  | MatchULit
  | MatchNil of ty                (*空列とmatchするMatchEmptyList*)
  | MatchCons of matchform * matchform  (*リストとmatchするMatchList*)
  | MatchTuple of matchform list
  | MatchWild of ty

(* === Definitions for coercion === *)

type polarity = Pos | Neg

(** Returns the negation of the given polarity. *)
let neg = function Pos -> Neg | Neg -> Pos

type tag = I | B | U | Ar | Li | Tp of int | Rf

type coercion =
  | CInj of tag
  | CProj of tag * (range * polarity)
  | CTvInj of tyvar * (range * polarity)
  | CTvProj of tyvar * (range * polarity)
  | CTvProjInj of tyvar * (range * polarity) * (range * polarity)
  | CFun of coercion * coercion
  | CList of coercion
  | CTuple of coercion list
  | CRef of coercion * coercion
  | CMRef of ty * ty
  | CId of ty
  | CSeq of coercion * coercion
  | CFail of tag * (range * polarity) * tag

exception Blame of range * polarity

(** Syntax of the surface language, the ITGL with extensions. *)
module ITGL = struct
  type anotated =
    | Impl
    | Expl

  type exp =
    | Var of range * id * ty list ref
    | IConst of range * int
    | BConst of range * bool
    | UConst of range
    | BinOp of range * binop * exp * exp
    | AscExp of range * exp * ty
    | IfExp of range * exp * exp * exp
    | FunExp of range * (id * anotated * ty) * exp
    | FixExp of range * id * (id * anotated * ty) * ty * exp
    | AppExp of range * exp * exp
    | MatchExp of range * exp * (matchform * exp) list
    | LetExp of range * id * exp * exp
    | NilExp of range * ty
    | ConsExp of range * exp * exp
    | TupleExp of range * exp list
    | RefExp of range * exp
    | DerefExp of range * exp
    | SubstExp of range * exp * exp

  let range_of_exp = function
    | Var (r, _, _)
    | IConst (r, _)
    | BConst (r, _)
    | UConst r
    | AscExp (r, _, _)
    | BinOp (r, _, _, _)
    | IfExp (r, _, _, _)
    | FunExp (r, _, _)
    | FixExp (r, _, _, _, _)
    | AppExp (r, _, _)
    | MatchExp (r, _, _)
    | LetExp (r, _, _, _) 
    | NilExp (r, _) 
    | ConsExp (r, _, _)
    | TupleExp (r, _)
    | RefExp (r, _) 
    | DerefExp (r, _)
    | SubstExp (r, _, _) -> r

  type program =
    | Exp of exp
    | LetDecl of id * exp
end

(** Syntax of the blame calculus with dynamic type inference. *)
module CC = struct
  exception Occur_LS1 of string

  type exp =
    | Var of id * tyarg list
    | IConst of int
    | BConst of bool
    | UConst
    | FunExp of tyvar list * fundef
    | FixExp of tyvar list * fixdef
    | CoercionExp of coercion
    | BinOp of binop * exp * exp
    | IfExp of exp * exp * exp
    | AppMExp of exp * exp
    | AppDExp of exp * (exp * exp)
    | LetExp of id * exp * exp
    | NilExp of ty
    | ConsExp of exp * exp
    | MatchExp of exp * (matchform * exp) list
    | TupleExp of exp list
    | RefExp of exp * ty
    | DerefExp of exp * ty option
    | SubstExp of exp * exp * ty option
    | CastExp of exp * ty * ty * (range * polarity)
    | CAppExp of exp * exp
    | CCompExp of exp * exp
  and fundef =
    | FunB of (id * ty) * exp
    | FunS of (id * ty) * (id * ty) * exp
    | FunDual of (id * ty) * (id * ty) * (exp * exp)
    | FunTy of exp
  and fixdef =
    | FixB of id * (id * ty) * ty * exp
    | FixS of id * (id * ty) * ty * (id * ty) * exp
    | FixDual of id * (id * ty) * ty * (id * ty) * (exp * exp)

  type program =
    | Exp of exp
    | LetDecl of id * exp
  
  type value =
    | IntV of int
    | BoolV of bool
    | UnitV
    | FunBV of (ty list -> value -> value)
    | FunSV of (ty list -> (value * value) -> value)
    | FunDualV of (ty list -> ((value -> value) * ((value * value) -> value)))
    | FunTyV of (ty list -> value)
    | CoercionV of coercion
    | NilV
    | ConsV of value * value
    | TupleV of value list
    | RefV of (value * ty) ref
    | Tagged of tag * value
    | CoerceV of value * coercion
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
    | Tuple of id list
    | Tget of id * int
    | Ref of id * ty
    | Deref of id * ty option
    | Subst of id * id * ty option
    | IfEqExp of id * id * exp * exp
    | IfLteExp of id * id * exp * exp
    | AppMExp of id * id
    | AppDExp of id * (id * id)
    | AppTy of id * tyvar list * tyarg list
    | CAppExp of id * id
    | CastExp of id * ty * ty * (range * polarity)
    | CCompExp of id * id
    | MatchExp of id * (matchform * exp) list
    | CoercionExp of coercion
    | LetExp of id * exp * exp
    | LetFunExp of id * tyvar list * fundef * exp
  and fundef =
    | FunB of id * exp
    | FunS of (id * id) * exp
    | FunDual of (id * id) * (exp * exp)
    | FunTy of exp

  type program =
    | Exp of exp
    | LetDecl of id * exp
    | LetFunDecl of id * tyvar list * fundef
end

module Cls = struct
  type label = string

  let to_label (x:id) = (x:label)

  let to_id (x:label) = (x:id)

  type closure = { entry : label; fvs : id list; offset : int; ftvs : tyvar list }
  (* offsetはzsとftvsの間にいくつの型変数が入るのか *)

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
    | Tuple of id list
    | Hd of id
    | Tl of id
    | Tget of id * int
    | Ref of id * ty
    | Deref of id * ty option
    | Subst of id * id * ty option
    | IfEq of id * id * exp * exp
    | IfLte of id * id * exp * exp
    | Match of id * (matchform * exp) list
    | AppTy of id * int * tyarg list * int (* 1つめのintはidの中身の自由変数の個数、2つめのintはtyarg listには含まれない外側からの型変数の個数 *)
    | AppTyFun of id * int * tyarg list * int
    | AppDCls of id * (id * id)
    | AppDDir of label * (id * id)
    | AppMCls of id * id
    | AppMDir of label * id
    | Cast of id * ty * ty * (range * polarity)
    | CApp of id * id
    | CComp of id * id
    | Coercion of coercion
    | Let of id * exp * exp
    | MakeCls of id * closure * exp
    | MakeTyCls of id * closure * exp
    | SetTy of tyvar * exp

  type fundef = 
    | FundefD  of { name : label; arg : id * id; vs : id list; tvs : tyvar list; body : exp }
    | FundefM  of { name : label; arg : id;      vs : id list; tvs : tyvar list; body : exp }
    | FundefTy of { name : label;                vs : id list; tvs : tyvar list; body : exp }

  type program = Prog of fundef list * exp

end

module C = struct
  type ty = 
    | INT | VOID | PTR of ty
    | VALUE | FUN | LST | TPL | REF | CRC
    | RANGE | TY

  type exp =
    | Var of id
    | Dot of exp * id
    | Arrow of exp * id
    | Cast of ty * exp
    | Index of exp * int
    | Int of int
    | Str of string
    | Add of exp * exp
    | Sub of exp * exp
    | Mul of exp * exp
    | Div of exp * exp
    | Mod of exp * exp
    | Eq of exp * exp
    | Lte of exp * exp
    | App of exp * exp list
    | Addr of id
    | Null
    | Malloc of ty * exp
    | Sizeof of ty
    | Struct of (id * exp) list
    | Array of exp list
    (* | Cons of id * id *)
    (* | Tuple of id list *)
    (* | Hd of id *)
    (* | Tl of id *)
    (* | Tget of id * int *)
    (* | Ref of id * ty
    | Deref of id * ty option
    | Subst of id * id * ty option *)

  type lval =
    | LVar of id
    | LDot of lval * id
    | LArrow of lval * id
    | LCast of ty * lval
    | LIndex of lval * int
    | LDeref of lval

  type spec = No | Static

  type stm =
    | SDecl of ty * id * exp option
    | SAssign of lval * exp
    | SReturn of exp
    | SIf of exp * stm list * stm list
    (* | Match of id * (matchform * exp) list *)

  type func_sig = {
    ret_ty: ty;
    fname: id;
    params: (ty * id) list;
  }

  type toplevel =
    | Include of string
    | Decl of spec * ty * id * exp option
    | FunDecl of spec * func_sig
    | FunDef of spec * func_sig * stm list
end