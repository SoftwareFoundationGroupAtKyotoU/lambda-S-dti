open Format
open Syntax

exception Syntax_error

(* === utils === *)

let with_paren flag ppf_e ppf e =
  fprintf ppf (if flag then "(%a)" else "%a") ppf_e e

(* === pp for ty === *)

let rec level_ty = function
  | TyVar (_, { contents = Some u }) -> level_ty u
  | TyDyn | TyVar _ | TyInt | TyBool | TyUnit | TyFloat -> 100
  | TyList _ | TyRef _ | TyArray _ -> 90
  | TyTuple _ -> 80
  | TyFun _ | TyCoercion _ -> 70

let gt_ty u1 u2 = level_ty u1 > level_ty u2

let gte_ty u1 u2 = level_ty u1 >= level_ty u2

(* util for pp_ty and pp_ty2 *)
let pp_ty_main ppf ~pp_tyvar u =
  let rec pp_ty ppf = function
    | TyDyn -> pp_print_string ppf "?"
    | TyVar (_, { contents = Some u }) -> pp_ty ppf u
    | TyVar tv -> pp_tyvar ppf tv
    | TyInt -> pp_print_string ppf "int"
    | TyBool -> pp_print_string ppf "bool"
    | TyUnit -> pp_print_string ppf "unit"
    | TyFloat -> pp_print_string ppf "float"
    | TyFun (u1, u2) as u ->
      fprintf ppf "%a -> %a"
        (with_paren (gte_ty u u1) pp_ty) u1
        pp_ty u2
    | TyList u' as u -> fprintf ppf "%a list" (with_paren (gt_ty u u') pp_ty) u'
    | TyTuple us as u ->
      let pp_sep ppf () = fprintf ppf " * " in
      let pp_list ppf types = pp_print_list (fun ppf u' -> (with_paren (gte_ty u u') pp_ty) ppf u') ppf types ~pp_sep:pp_sep in
      fprintf ppf "%a"
        pp_list us
    | TyRef u' as u -> fprintf ppf "%a ref" (with_paren (gt_ty u u') pp_ty) u'
    | TyArray u' as u -> fprintf ppf "%a array" (with_paren (gt_ty u u') pp_ty) u'
    | TyCoercion (u1, u2) ->
      fprintf ppf "%a ~> %a"
        (with_paren (gte_ty u u1) pp_ty) u1
        (with_paren (gte_ty u u2) pp_ty) u2
  in
  pp_ty ppf u

(** Pretty-printer for types. Show the raw index of a type variable (e.g., 'x123->'x124). *)
let pp_ty ppf u =
  let pp_tyvar ppf (a, _) = fprintf ppf "'x%d" a in
  pp_ty_main ppf ~pp_tyvar u

(** Pretty-printer for types. Type variables are renamed (e.g., 'a->'b). *)
let pp_ty2 ppf u =
  let tyvars = ref [] in
  let pp_tyvar ppf (a, _) =
    let rec index_of_tyvar pos = function
      | [] -> tyvars := !tyvars @ [a]; pos
      | a' :: rest -> if a = a' then pos else index_of_tyvar (pos + 1) rest
    in
    let pp_tyvar_of_index ppf i =
      let j = i / 26 in
      let k = i mod 26 in
      let s = String.make 1 @@ char_of_int @@ (int_of_char 'a') + k in
      let t = if j = 0 then "" else string_of_int j in
      fprintf ppf "'%s%s" s t
    in
    pp_tyvar_of_index ppf @@ index_of_tyvar 0 !tyvars
  in
  pp_ty_main ppf ~pp_tyvar u

let pp_constr ppf = function
  | CEqual (u1, u2) ->
    fprintf ppf "%a =.= %a" pp_ty u1 pp_ty u2
  | CConsistent (u1, u2) ->
    fprintf ppf "%a ~.~ %a" pp_ty u1 pp_ty u2

(* === pp for binop === *)

(* TODO: replace to level *)
let gt_binop op1 op2 = match op1, op2 with
  | (Plus | Minus | Mult | Div | Mod | FPlus | FMinus | FMult | FDiv), (Eq | Neq | Lt | Lte | Gt | Gte)
  | (Mult | Div | Mod | FMult | FDiv), (Plus | Minus | FPlus | FMinus) -> true
  | _ -> false

let gte_binop op1 op2 = match op1, op2 with
  | (Eq | Neq | Lt | Lte | Gt | Gte), (Eq | Neq | Lt | Lte | Gt | Gte)
  | (Mult | Div | Mod | FMult | FDiv), (Mult | Div | Mod | FMult | FDiv)
  | (Plus | Minus | FPlus | FMinus), (Plus | Minus | FPlus | FMinus) -> true
  | _ -> gt_binop op1 op2

let pp_binop ppf op =
  pp_print_string ppf begin
    match op with
    | Plus -> "+"
    | Minus -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Mod -> "mod"
    | And -> "&&"
    | Or -> "||"
    | Eq -> "="
    | Neq -> "<>"
    | Lt -> "<"
    | Lte -> "<="
    | Gt -> ">"
    | Gte -> ">="
    | FPlus -> "+."
    | FMinus -> "-."
    | FMult -> "*."
    | FDiv -> "/."
    | FEq -> "=."
    | FNeq -> "<>."
    | FLt -> "<."
    | FLte -> "<=."
    | FGt -> ">."
    | FGte -> ">=."
  end

(* === pp for variables === *)

let pp_print_var ppf (x, ys) =
  if List.length ys = 0 then
    fprintf ppf "%s" x
  else
    let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf types = pp_print_list pp_ty ppf types ~pp_sep:pp_sep in
    fprintf ppf "%s[%a]"
      x
      pp_list ys

let pp_tyarg ppf = function
  | Ty u -> pp_ty ppf u
  | TyNu -> pp_print_string ppf "ν"

let pp_print_tas ppf tas =
  let pp_sep ppf () = fprintf ppf "," in
  let pp_list ppf types = pp_print_list pp_tyarg ppf types ~pp_sep:pp_sep in
  fprintf ppf "%a"
    pp_list tas

(* === pp for let === *)

let pp_tyabses ppf tyvars =
  if List.length tyvars = 0 then
    fprintf ppf ""
  else
    let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf types = pp_print_list pp_ty ppf types ~pp_sep:pp_sep in
    fprintf ppf "fun %a -> " pp_list @@ List.map (fun x -> TyVar x) tyvars

(* === pp for matchform === *)

let gte_matchform mf1 mf2 = match mf1, mf2 with
  | MatchCons _, MatchCons _ -> true
  | MatchTuple _, MatchTuple _ -> true
  | _ -> false

let rec pp_matchform ppf = function
  (* | MatchVar (x, u) -> fprintf ppf "(%s: %a)" x pp_ty u *)
  | MatchVar x -> fprintf ppf "%s" x
  (* | MatchAsc (mf, u) -> fprintf ppf "(%a : %a)" pp_matchform mf pp_ty u *)
  | MatchILit i -> pp_print_int ppf i
  | MatchBLit b -> pp_print_bool ppf b
  | MatchULit -> pp_print_string ppf "()"
  (* | MatchNil u -> fprintf ppf "([] : %a)" pp_ty (TyList u) *)
  | MatchNil -> fprintf ppf "[]"
  | MatchCons (mf1, mf2) as mf -> 
    fprintf ppf "%a :: %a"
      (with_paren (gte_matchform mf mf1) pp_matchform) mf1
      pp_matchform mf2
  | MatchTuple mfs as mf ->
    let pp_sep ppf () = fprintf ppf ", " in
    let pp_list ppf matches = pp_print_list (fun ppf mf' -> (with_paren (gte_matchform mf mf') pp_matchform) ppf mf') ppf matches ~pp_sep:pp_sep in
    fprintf ppf "(%a)"
      pp_list mfs
  | MatchWild -> pp_print_string ppf "_"

(* === pp for coercion === *)

let pp_tag ppf = function
  | I -> pp_print_string ppf "int"
  | F -> pp_print_string ppf "float"
  | B -> pp_print_string ppf "bool"
  | U -> pp_print_string ppf "unit"
  | Fn -> pp_print_string ppf "(? -> ?)"
  | Li -> pp_print_string ppf "[?]"
  | Tp n ->
    let rec pp_dyn_tuple ppf i =
      if i = 1 then fprintf ppf "?"
      else fprintf ppf "? * %a" pp_dyn_tuple (i - 1)
    in
    fprintf ppf "(%a)"
      pp_dyn_tuple n
  | Rf -> pp_print_string ppf ":?:"
  | Ar -> pp_print_string ppf "[|?|]"

let level_coercion = function
  | CInj _ | CProj _ | CTvInj _ | CTvProj _ | CTvProjInj _ | CId _ | CFail _ -> 100
  | CList _ | CRef _ | CMRef _ | CArray _ | CMArray _ -> 80
  | CTuple _ -> 60
  | CFun _ -> 40
  | CSeq _ -> 0

let gt_coercion c1 c2 = level_coercion c1 > level_coercion c2

let gte_coercion c1 c2 = level_coercion c1 >= level_coercion c2

let pp_coercion_main ppf ~pp_ty c = 
  let rec pp_coercion ppf = function
    | CInj t -> 
      fprintf ppf "%a!"
        pp_tag t
    | CProj (t, _) ->
      fprintf ppf "%a?p"
        pp_tag t
    | CTvInj ((_, {contents = None} as tv), _) ->
      fprintf ppf "%a!p"
        pp_ty (TyVar tv)
    | CTvProj ((_, {contents = None} as tv), _) ->
      fprintf ppf "%a?p"
        pp_ty (TyVar tv)
    | CTvProjInj ((_, {contents = None} as tv), _, _) ->
      fprintf ppf "?p%a!q"
        pp_ty (TyVar tv)
    | CTvInj (tv, _) ->
      fprintf ppf "|%a|!"
        pp_ty (TyVar tv)
    | CTvProj (tv, _) ->
      fprintf ppf "|%a|?"
        pp_ty (TyVar tv)
    | CTvProjInj (tv, _, _) ->
      fprintf ppf "?|%a|!"
        pp_ty (TyVar tv)
    | CFun (c1, c2) as c ->
      fprintf ppf "%a->%a"
        (with_paren (gte_coercion c c1) pp_coercion) c1
        (with_paren (gte_coercion c c2) pp_coercion) c2
    | CList c ->
      fprintf ppf "[%a]"
        pp_coercion c
    | CTuple cs as c ->
      let pp_sep ppf () = fprintf ppf "*" in
      let pp_list ppf crcs = pp_print_list (fun ppf c' -> (with_paren (gte_coercion c c') pp_coercion) ppf c') ppf crcs ~pp_sep:pp_sep in
      fprintf ppf "%a"
        pp_list cs
    | CRef (c1, c2) ->
      fprintf ppf "ref(%a,%a)"
        pp_coercion c1
        pp_coercion c2
    | CMRef (_, u) ->
      fprintf ppf "mref(%a)"
        pp_ty u
    | CArray (c1, c2) ->
      fprintf ppf "array(%a,%a)"
        pp_coercion c1
        pp_coercion c2
    | CMArray (_, u) ->
      fprintf ppf "marray(%a)"
        pp_ty u
    | CId u ->
      fprintf ppf "id{%a}" 
        pp_ty u
    | CSeq (c1, c2) ->
      fprintf ppf "%a;%a"
        pp_coercion c1
        pp_coercion c2
    | CFail (t1, _, t2) ->
      fprintf ppf "⊥{%a,p,%a}"
        pp_tag t1
        pp_tag t2
  in
  pp_coercion ppf c

let pp_coercion ppf c =
  pp_coercion_main ppf ~pp_ty:pp_ty c

let pp_coercion2 ppf c = 
  pp_coercion_main ppf ~pp_ty:pp_ty2 c

module ITGL = struct
  open Syntax.ITGL

  let level_exp = function
    | Var _ | IConst _ | BConst _ | UConst _ | FConst _ | NilExp _ | TupleExp _ | AscExp _ -> 100
    | DerefExp _ | GetExp _ -> 90
    | AppExp _ | RefExp _ | MakeArrayExp _ | LengthExp _ -> 80
    | BinOp (_, (Mult | Div | Mod | FMult | FDiv), _, _) -> 70
    | BinOp (_, (Plus | Minus | FPlus | FMinus), _, _) -> 60
    | ConsExp _ -> 50
    | BinOp (_, (Eq | Neq | Lt | Lte | Gt | Gte | FEq | FNeq | FLt | FLte | FGt | FGte), _, _) -> 40
    | BinOp (_, And, _, _) -> 35
    | BinOp (_, Or, _, _) -> 30
    | SubstExp _ | PutExp _ -> 20
    | IfExp _ | FunExp _ | FixExp _ | LetExp _ | MatchExp _ -> 10
  
  let gt_exp e1 e2 =
    level_exp e1 > level_exp e2

  let gte_exp e1 e2 =
    level_exp e1 >= level_exp e2

  let rec pp_exp ppf = function
    | Var (_, x, ys) -> pp_print_var ppf (x, !ys)
    | IConst (_, i) -> pp_print_int ppf i
    | BConst (_, b) -> pp_print_bool ppf b
    | UConst _ -> pp_print_string ppf "()"
    | FConst (_, f) -> pp_print_float ppf f
    | BinOp (_, op, e1, e2) as e ->
      fprintf ppf "%a %a %a"
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_binop op
        (with_paren (gt_exp e e2) pp_exp) e2
    | AscExp (_, e1, u) ->
      fprintf ppf "(%a : %a)"
        pp_exp e1
        pp_ty u
    | IfExp (_, e1, e2, e3) as e ->
      fprintf ppf "if %a then %a else %a"
        (with_paren (gt_exp e e1) pp_exp) e1
        (with_paren (gt_exp e e2) pp_exp) e2
        (with_paren (gt_exp e e3) pp_exp) e3
    | FunExp (_, (x1, _, u1), e) ->
      fprintf ppf "fun (%s: %a) -> %a"
        x1
        pp_ty u1
        pp_exp e
    | FixExp (_, x, (y, _, u1), u2, e) ->
      fprintf ppf "fix %s (%s: %a): %a = %a"
        x
        y
        pp_ty u1
        pp_ty u2
        pp_exp e
    | AppExp (_, e1, e2) as e ->
      fprintf ppf "%a %a"
        (with_paren (gt_exp e e1) pp_exp) e1
        (with_paren (gte_exp e e2) pp_exp) e2
    | MatchExp (_, e1, ms) as e ->
      fprintf ppf "match %a with%a"
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (ms, e)
    | LetExp (_, x, e1, e2) as e ->
      fprintf ppf "let %s = %a in %a"
        x
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_exp e2
    | NilExp _ -> pp_print_string ppf "[]"
    | ConsExp (_, e1, e2) as e ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_exp e e1) pp_exp) e1
        (with_paren (gt_exp e e2) pp_exp) e2
    | TupleExp (_, es) ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf exps = pp_print_list pp_exp ppf exps ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list es
    | RefExp (_, e') as e ->
      fprintf ppf "ref %a" (with_paren (gte_exp e e') pp_exp) e'
    | DerefExp (_, e') as e ->
      fprintf ppf "!%a" (with_paren (gt_exp e e') pp_exp) e'  
    | SubstExp (_, e1, e2) as e ->
      fprintf ppf "%a := %a" (with_paren (gte_exp e e1) pp_exp) e1 (with_paren (gt_exp e e2) pp_exp) e2
    | MakeArrayExp (_, e1, e2) as e ->
      fprintf ppf "Array.make %a %a" (with_paren (gte_exp e e1) pp_exp) e1 (with_paren (gte_exp e e2) pp_exp) e2
    | GetExp (_, e1, e2) as e ->
      fprintf ppf "%a.(%a)" (with_paren (gt_exp e e1) pp_exp) e1 pp_exp e2
    | PutExp (_, e1, e2, e3) as e ->
      fprintf ppf "%a.(%a) <- %a" (with_paren (gt_exp e e1) pp_exp) e1 pp_exp e2 (with_paren (gt_exp e e3) pp_exp) e3
    | LengthExp (_, e') as e ->
      fprintf ppf "Array.length %a" (with_paren (gte_exp e e') pp_exp) e'

  and pp_match ppf = function
    | ((mf, e1) :: m, e) -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (m, e)
    | ([], _) -> fprintf ppf ""

  let pp_program ppf = function
    | Exp e -> pp_exp ppf e
    | LetDecl (x, e) ->
      fprintf ppf "let %s = %a"
        x
        pp_exp e
end

module CC = struct
  open Syntax.CC

  let level_exp = function
    | Var _ | IConst _ | BConst _ | UConst | FConst _ | NilExp _ | TupleExp _ | CoercionExp _ -> 100
    | CCompExp _ -> 95
    | DerefExp _ | GetExp _ -> 90
    | AppDExp _ | AppMExp _ | RefExp _ | MakeArrayExp _ | LengthExp _ -> 80
    | CAppExp _ -> 75
    | BinOp ((Mult | Div | Mod | FMult | FDiv), _, _) -> 70
    | BinOp ((Plus | Minus | FPlus | FMinus), _, _) -> 60
    | ConsExp _ -> 50
    | BinOp ((Eq | Neq | Lt | Lte | Gt | Gte | FEq | FNeq | FLt | FLte | FGt | FGte), _, _) -> 40
    | BinOp (And, _, _) -> 35
    | BinOp (Or, _, _) -> 30
    | SubstExp _ | PutExp _ -> 20
    | CastExp _ -> 15
    | IfExp _ | FunExp _ | FixExp _ | LetExp _ | MatchExp _ -> 10
  
  let gt_exp e1 e2 =
    level_exp e1 > level_exp e2

  let gte_exp e1 e2 =
    level_exp e1 >= level_exp e2

  let pp_print_var ppf (x, ys) =
    if List.length ys = 0 then
      fprintf ppf "%s" x
    else
      let pp_sep ppf () = fprintf ppf "," in
      let pp_list ppf types = pp_print_list pp_tyarg ppf types ~pp_sep:pp_sep in
      fprintf ppf "%s[%a]"
        x
        pp_list ys

  let rec pp_exp ppf = function
    | Var (x, ys) -> pp_print_var ppf (x, ys)
    | IConst i -> pp_print_int ppf i
    | BConst b -> pp_print_bool ppf b
    | UConst -> pp_print_string ppf "()"
    | FConst f -> pp_print_float ppf f
    | BinOp (op, f1, f2) as f ->
      fprintf ppf "%a %a %a"
        (with_paren (gt_exp f f1) pp_exp) f1
        pp_binop op
        (with_paren (gt_exp f f2) pp_exp) f2
    | IfExp (f1, f2, f3) as f ->
      fprintf ppf "if %a then %a else %a"
        (with_paren (gt_exp f f1) pp_exp) f1
        (with_paren (gt_exp f f2) pp_exp) f2
        (with_paren (gt_exp f f3) pp_exp) f3
    | FunExp (xs, fund) ->
      fprintf ppf "%a%a"
        pp_tyabses xs
        pp_fund fund
    | FixExp (xs, fixd) ->
      fprintf ppf "%a%a"
        pp_tyabses xs
        pp_fixd fixd
    | AppMExp (f1, f2) as f ->
      fprintf ppf "%a %a"
        (with_paren (gt_exp f f1) pp_exp) f1
        (with_paren (gte_exp f f2) pp_exp) f2
    | AppDExp (f1, (f2, f3)) as f ->
      fprintf ppf "%a (%a, %a)"
        (with_paren (gt_exp f f1) pp_exp) f1
        pp_exp f2
        pp_exp f3
    | CAppExp (f1, f2) as f ->
        fprintf ppf "%a<%a>"
          (with_paren (gt_exp f f1) pp_exp) f1
          pp_exp f2
    | CCompExp (f1, f2) ->
        fprintf ppf "%a;;%a"
          pp_exp f1
          pp_exp f2
    | CastExp (f1, u1, u2, _) as f ->
      begin match f1 with
      | CastExp _ ->
        fprintf ppf "%a => %a"
          (with_paren (gt_exp f f1) pp_exp) f1
          pp_ty u2
      | _ ->
        fprintf ppf "%a: %a => %a"
          (with_paren (gt_exp f f1) pp_exp) f1
          pp_ty u1
          pp_ty u2
      end
    | MatchExp (e1, ms) as e ->
      fprintf ppf "match %a with%a"
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (ms, e)
    | LetExp (x, f1, f2) as f ->
      fprintf ppf "let %s = %a in %a"
        x
        (with_paren (gt_exp f f1) pp_exp) f1
        pp_exp f2
    | CoercionExp c ->
      fprintf ppf "%a"
        pp_coercion c
    | NilExp _ -> pp_print_string ppf "[]"
    | ConsExp (f1, f2) as f ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_exp f f1) pp_exp) f1
        (with_paren (gt_exp f f2) pp_exp) f2
    | TupleExp fs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf exps = pp_print_list pp_exp ppf exps ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list fs
    | RefExp (f', u) as f ->
      fprintf ppf "ref %a@%a"
        (with_paren (gte_exp f f') pp_exp) f'
        pp_ty u
    | DerefExp (f', None) as f ->
      fprintf ppf "!%a"
        (with_paren (gte_exp f f') pp_exp) f'
    | DerefExp (f', Some u) as f ->
      fprintf ppf "!%a@%a"
        (with_paren (gt_exp f f') pp_exp) f'
        pp_ty u
    | SubstExp (f1, f2, None) as f ->
      fprintf ppf "%a := %a"
        (with_paren (gte_exp f f1) pp_exp) f1
        (with_paren (gte_exp f f2) pp_exp) f2
    | SubstExp (f1, f2, Some u) as f ->
      fprintf ppf "%a := %a@%a"
        (with_paren (gte_exp f f1) pp_exp) f1
        (with_paren (gte_exp f f2) pp_exp) f2
        pp_ty u
    | MakeArrayExp (f1, f2, u) as f ->
      fprintf ppf "Array.make %a %a@%a"
        (with_paren (gte_exp f f1) pp_exp) f1
        (with_paren (gte_exp f f2) pp_exp) f2
        pp_ty u
    | GetExp (f1, f2, None) as f ->
      fprintf ppf "%a.(%a)"
        (with_paren (gte_exp f f1) pp_exp) f1
        pp_exp f2
    | GetExp (f1, f2, Some u) as f ->
      fprintf ppf "%a.(%a)@%a"
        (with_paren (gt_exp f f1) pp_exp) f1
        pp_exp f2
        pp_ty u
    | PutExp (f1, f2, f3, None) as f ->
      fprintf ppf "%a.(%a) <- %a"
        (with_paren (gte_exp f f1) pp_exp) f1
        pp_exp f2
        (with_paren (gte_exp f f3) pp_exp) f3
    | PutExp (f1, f2, f3, Some u) as f ->
      fprintf ppf "%a.(%a) <- %a@%a"
        (with_paren (gte_exp f f1) pp_exp) f1
        pp_exp f2
        (with_paren (gte_exp f f3) pp_exp) f3
        pp_ty u
    | LengthExp f' as f ->
      fprintf ppf "Array.length %a"
        (with_paren (gte_exp f f') pp_exp) f'
  and pp_match ppf = function
    | ((mf, e1) :: m, e) -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (m, e)
    | ([], _) -> fprintf ppf ""
  and pp_fund ppf = function
    | FunB ((y, u), e) ->
      fprintf ppf "fun (%s: %a) -> %a"
        y
        pp_ty u
        pp_exp e
    | FunS ((y, u), (k, uk), e) ->
      fprintf ppf "fun (%s: %a, %s: %a) -> %a"
        y
        pp_ty u
        k
        pp_ty uk
        pp_exp e
    | FunDual ((y, u), (k, uk), (e1, e2)) ->
      fprintf ppf "fun (%s: %a, %s: %a) -> (%a | %a)"
        y
        pp_ty u
        k
        pp_ty uk
        pp_exp e1
        pp_exp e2
    | FunTy e ->
      fprintf ppf "%a"
        pp_exp e
  and pp_fixd ppf = function
    | FixB (x, (y, u1), u2, e) ->
      fprintf ppf "fix %s (%s: %a): %a = %a"
        x y
        pp_ty u1
        pp_ty u2
        pp_exp e
    | FixS (x, (y, u1), u2, (k, uk), e) ->
      fprintf ppf "fix %s (%s: %a, %s: %a): %a = %a"
        x y
        pp_ty u1
        k
        pp_ty uk
        pp_ty u2
        pp_exp e
    | FixDual (x, (y, u1), u2, (k, uk), (e1, e2)) ->
      fprintf ppf "fix %s (%s: %a, %s: %a): %a = (%a | %a)"
        x y
        pp_ty u1
        k
        pp_ty uk
        pp_ty u2
        pp_exp e1
        pp_exp e2

  let pp_program ppf = function
    | Exp e -> pp_exp ppf e
    | LetDecl (x, f) ->
      fprintf ppf "let %s = %a"
        x
        pp_exp f

  let gt_value v1 v2 = match v1, v2 with
    | (IntV _ | BoolV _ | UnitV | FloatV _ | FunBV _ | FunSV _ | FunDualV _ | FunTyV _ | NilV | TupleV _ | RefV _ | ArrayV _ | CoercionV _ | Tagged _ | CoerceV _ | CastFunV _ | CastListV _ | CastTupleV _ | CastRefV _ | CastArrayV _), ConsV _ -> true
    | (IntV _ | BoolV _ | UnitV | FloatV _ | FunBV _ | FunSV _ | FunDualV _ | FunTyV _ | NilV | TupleV _ | RefV _ | ArrayV _ | CoercionV _), (Tagged _ | CoerceV _ | CastFunV _ | CastListV _ | CastTupleV _ | CastRefV _ | CastArrayV _) -> true
    | _ -> false

  let gte_value v1 v2 = match v1, v2 with
    | (FunBV _ | FunSV _ | FunDualV _ | FunTyV _ ), (FunBV _ | FunSV _ | FunDualV _ | FunTyV _) -> true
    | Tagged _, Tagged _ -> true
    | CoerceV _, CoerceV _ -> true
    | CastFunV _, CastFunV _ -> true
    | CastListV _, CastListV _ -> true
    | CastTupleV _, CastTupleV _ -> true
    | CastRefV _, CastRefV _ -> true
    | ConsV _, ConsV _ -> true
    | TupleV _, TupleV _ -> true
    | RefV _, RefV _ -> true
    | ArrayV _, ArrayV _ -> true
    | _ -> gt_value v1 v2

  let pp_value_main ppf ~pp_ty ~pp_coercion v =
    let rec pp_value refl ppf = function 
      | IntV i -> pp_print_int ppf i
      | BoolV b -> pp_print_bool ppf b
      | UnitV -> pp_print_string ppf "()"
      | FloatV f -> pp_print_float ppf f
      | FunBV _ | FunSV _ | FunDualV _ | FunTyV _ -> pp_print_string ppf "<fun>"
      | CoercionV c ->
        fprintf ppf "%a"
          pp_coercion c
      | NilV -> pp_print_string ppf "[]"
      | ConsV (v1, v2) as v ->
        fprintf ppf "%a :: %a"
          (with_paren (gte_value v v1) @@ pp_value refl) v1
          (with_paren (gt_value v v2) @@ pp_value refl) v2
      | TupleV vs ->
        let pp_sep ppf () = fprintf ppf ", " in
        let pp_list ppf vals = pp_print_list (pp_value refl) ppf vals ~pp_sep:pp_sep in
        fprintf ppf "(%a)"
          pp_list vs
      | RefV { contents = (v', u) } as v ->
        if List.mem v refl then fprintf ppf "<cycle>"
        else
          fprintf ppf "{ contents = %a, %a }"
            (pp_value (v :: refl)) v'
            pp_ty u
      | ArrayV { contents = (vs, u) } as v ->
        if List.mem v refl then fprintf ppf "<cycle>"
        else
          fprintf ppf "[| %a, %a |]"
            (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ") (pp_value (v :: refl))) (Array.to_list vs)
            pp_ty u
      | Tagged (t, v) ->
        begin match v with
        | CastFunV _ | CastListV _ | CastTupleV _ | CastRefV _ | CastArrayV _ ->
          fprintf ppf "%a => ?"
            (pp_value refl) v
        | _ -> 
          fprintf ppf "%a: %a => ?"
            (pp_value refl) v
            pp_tag t
        end
      | CastFunV (v1, u11, u12, u21, u22, _) as v ->
        begin match v1 with
        | CastFunV _ ->
          fprintf ppf "%a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyFun (u21, u22))
        | _ ->
          fprintf ppf "%a: %a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyFun (u11, u12))
            pp_ty (TyFun (u21, u22))
        end
      | CastListV (v1, u1, u2, _) as v ->
        begin match v1 with
        | CastListV _ ->
          fprintf ppf "%a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyList u2)
        | _ ->
          fprintf ppf "%a: %a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyList u1)
            pp_ty (TyList u2)
        end
      | CastTupleV (v1, us1, us2, _) as v ->
        begin match v1 with
        | CastTupleV _ ->
          fprintf ppf "%a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyTuple us2)
        | _ ->
          fprintf ppf "%a: %a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyTuple us1)
            pp_ty (TyTuple us2)
        end
      | CastRefV (v1, u1, u2, _) as v ->
        begin match v1 with
        | CastRefV _ ->
          fprintf ppf "%a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyRef u2)
        | _ ->
          fprintf ppf "%a: %a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyRef u1)
            pp_ty (TyRef u2)
        end
      | CastArrayV (v1, u1, u2, _) as v ->
        begin match v1 with
        | CastArrayV _ ->
          fprintf ppf "%a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyArray u2)
        | _ ->
          fprintf ppf "%a: %a => %a"
            (with_paren (gt_value v v1) @@ pp_value refl) v1
            pp_ty (TyArray u1)
            pp_ty (TyArray u2)
        end
      | CoerceV (v1, c) as v ->
        fprintf ppf "%a<<%a>>"
          (with_paren (gt_value v v1) @@ pp_value refl) v1
          pp_coercion c
    in
    pp_value [] ppf v

  let pp_value ppf v = pp_value_main ppf ~pp_ty ~pp_coercion v

  let pp_value2 ppf v = pp_value_main ppf ~pp_ty:pp_ty2 ~pp_coercion:pp_coercion2 v
end

module KNorm = struct 
  open Syntax.KNorm

  let gt_exp e e1 = match e, e1 with
    | (IfExp _ | MatchExp _), (LetExp _ | LetFunExp _) -> true
    | _ -> false
  
  let gte_exp e e1 = match e, e1 with
    | (LetExp _ | LetFunExp _) , (LetExp _ | LetFunExp _) -> true
    | IfExp _, IfExp _ -> true
    | MatchExp _, MatchExp _ -> true
    | _ -> gt_exp e e1

  let rec pp_exp ppf = function
    | Var x -> pp_print_string ppf x
    | IConst i -> pp_print_int ppf i
    | FConst f -> pp_print_float ppf f
    | Nil -> pp_print_string ppf "[]"
    | BinOp (x, op, y) -> fprintf ppf "%s %a %s" x pp_binop op y
    | Cons (x, y) -> fprintf ppf "%s :: %s" x y
    | Tuple xs -> 
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf exps = pp_print_list pp_print_string ppf exps ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list xs
    | Tget (x, i) -> fprintf ppf "tget(%s, %d)" x i
    | Hd x -> fprintf ppf "hd(%s)" x
    | Tl x -> fprintf ppf "tl(%s)" x
    | Ref (x, u) -> fprintf ppf "ref %s@%a" x pp_ty u
    | Deref (x, None) -> fprintf ppf "!%s" x
    | Deref (x, Some u) -> fprintf ppf "!%s@%a" x pp_ty u
    | Subst (x, y, None) -> fprintf ppf "%s := %s" x y
    | Subst (x, y, Some u) -> fprintf ppf "%s := %s@%a" x y pp_ty u
    | MakeArray (x, y, u) -> fprintf ppf "Make.array %s %s@%a" x y pp_ty u
    | Get (x, y, None) -> fprintf ppf "%s.(%s)" x y
    | Get (x, y, Some u) -> fprintf ppf "%s.(%s)@%a" x y pp_ty u
    | Put (x, y, z, None) -> fprintf ppf "%s.(%s) <- %s" x y z
    | Put (x, y, z, Some u) -> fprintf ppf "%s.(%s) <- %s@%a" x y z pp_ty u
    | Length x -> fprintf ppf "Array.length %s" x
    | IfExp (x, e1, e2) ->
      fprintf ppf "if %s then %a else %a"
        x
        pp_exp e1
        pp_exp e2
    | MatchExp (x, ms) as e ->
      fprintf ppf "match %s with%a"
        x        
        pp_match (ms, e)
    | AppMExp (x, y) ->
      fprintf ppf "%s %s" x y
    | AppDExp (x, (y, z)) -> 
      fprintf ppf "%s (%s, %s)" x y z
    | AppTy (x, _, tas) ->
      fprintf ppf "%s[%a]"
        x
        pp_print_tas tas
    | CAppExp (x, y) ->
      fprintf ppf "%s<%s>" x y
    | CastExp (x, u1, u2, _) ->
      fprintf ppf "%s: %a => %a"
        x
        pp_ty u1
        pp_ty u2
    | CCompExp (x, y) -> 
      fprintf ppf "%s;;%s" x y
    | LetExp (x, e1, e2) as e ->
      fprintf ppf "let %s = %a in %a"
        x
        (with_paren (gt_exp e e1) pp_exp) e1
        pp_exp e2
    | CoercionExp c ->
      pp_coercion ppf c
    | LetFunExp (x, tvs, fd, e2) -> 
      fprintf ppf "let %s = %a%a in %a"
        x
        pp_tyabses tvs
        pp_fd fd
        pp_exp e2
  and pp_fd ppf = function
    | FunB (y, e1) -> 
      fprintf ppf "fun %s -> %a"
        y
        pp_exp e1
    | FunS ((y, k), e1) ->
      fprintf ppf "fun (%s, %s) -> %a"
        y
        k
        pp_exp e1
    | FunDual ((y, k), (e1, e2)) ->
      fprintf ppf "fun (%s, %s) -> (%a | %a)"
        y
        k
        pp_exp e1
        pp_exp e2
    | FunTy e1 ->
      fprintf ppf "%a"
        pp_exp e1
  and pp_match ppf = function
    | ((mf, e1) :: m, e) -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (m, e)
    | ([], _) -> fprintf ppf ""
    
  let pp_program ppf = function
    | Exp e -> pp_exp ppf e
    | LetDecl (x, e) ->
      fprintf ppf "let %s = %a"
        x
        pp_exp e
    | LetFunDecl (x, tvs, fd) ->
        fprintf ppf "let %s = %a%a"
          x
          pp_tyabses tvs
          pp_fd fd
end

module Cls = struct
  open Syntax.Cls

  let pp_tyabses ppf tyvars =
    if List.length tyvars = 0 then
      fprintf ppf ""
    else
      let pp_sep ppf () = fprintf ppf "," in
      let pp_list ppf types = pp_print_list pp_ty ppf types ~pp_sep:pp_sep in
      fprintf ppf "[%a] " pp_list @@ List.map (fun x -> TyVar x) tyvars
  
  let pp_cls ppf { entry; fvs; offset; ftvs } =
    let pp_sep ppf () = fprintf ppf "," in
    fprintf ppf "%s[%a,%d,%a]"
      entry
      (pp_print_list ~pp_sep:pp_sep pp_print_string) fvs
      offset
      (pp_print_list ~pp_sep:pp_sep (fun ppf (a, _) -> fprintf ppf "'x%d" a)) ftvs

  let rec pp_exp ppf = function
    | Var x -> pp_print_string ppf x
    | Int i -> pp_print_int ppf i
    | Float f -> pp_print_float ppf f
    | Nil -> pp_print_string ppf "[]"
    | BinOp (x, op, y) -> fprintf ppf "%s %a %s" x pp_binop op y
    | Cons (x, y) -> fprintf ppf "%s :: %s" x y
    | Tuple xs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vars = pp_print_list pp_print_string ppf vars ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list xs
    | Hd x -> fprintf ppf "hd(%s)" x
    | Tl x -> fprintf ppf "tl(%s)" x
    | Tget (x, i) -> fprintf ppf "tget(%s, %i)" x i
    | Ref (x, u) -> fprintf ppf "ref %s@%a" x pp_ty u
    | Deref (x, None) -> fprintf ppf "!%s" x
    | Deref (x, Some u) -> fprintf ppf "!%s@%a" x pp_ty u
    | Subst (x, y, None) -> fprintf ppf "%s := %s" x y
    | Subst (x, y, Some u) -> fprintf ppf "%s := %s@%a" x y pp_ty u
    | MakeArray (x, y, u) -> fprintf ppf "Make.array %s %s@%a" x y pp_ty u
    | Get (x, y, None) -> fprintf ppf "%s.(%s)" x y
    | Get (x, y, Some u) -> fprintf ppf "%s.(%s)@%a" x y pp_ty u
    | Put (x, y, z, None) -> fprintf ppf "%s.(%s) <- %s" x y z
    | Put (x, y, z, Some u) -> fprintf ppf "%s.(%s) <- %s@%a" x y z pp_ty u
    | Length x -> fprintf ppf "Array.length %s" x
    | If (x, e1, e2) ->
      fprintf ppf "if %s then %a else %a"
        x
        pp_exp e1
        pp_exp e2
    | Match (x, ms) ->
      fprintf ppf "match %s with%a"
        x        
        pp_match ms
    | AppDCls (x, (y, z)) -> fprintf ppf "%s:cls (%s, %s)" x y z
    | AppDDir (l, (y, z)) -> fprintf ppf "%s:label (%s, %s)" l y z
    | AppMCls (x, y) -> fprintf ppf "%s:cls_alt %s" x y
    | AppMDir (l, y) -> fprintf ppf "%s:label_alt %s" l y
    | AppTy (x, _, tas, _) | AppTyFun (x, _, tas, _) ->
      fprintf ppf "%s[%a]"
        x
        pp_print_tas tas
    | SetTy ((i, { contents = None }), f) ->
      fprintf ppf "set _ty%d = TYVAR in %a"
        i
        pp_exp f
    | SetTy ((i, { contents = Some (TyFun (u1, u2)) }), f) ->
      fprintf ppf "set _tyfun%d = TYFUN(%a, %a) in %a"
        i
        pp_ty u1
        pp_ty u2
        pp_exp f
    | SetTy ((i, { contents = Some (TyList u) }), f) ->
      fprintf ppf "set _tylist%d = TYLIST(%a) in %a"
        i
        pp_ty u
        pp_exp f
    | SetTy ((i, { contents = Some (TyTuple us) }), f) ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf tys = pp_print_list pp_ty ppf tys ~pp_sep:pp_sep in
      fprintf ppf "set _tylist%d = TYTUPLE(%a) in %a"
        i
        pp_list us
        pp_exp f
    | SetTy _ -> raise @@ Syntax_error
    | Cast (x, u1, u2, _) ->
        fprintf ppf "%s: %a => %a"
          x
          pp_ty u1
          pp_ty u2
    | CApp (x, y) ->
      fprintf ppf "%s<%s>" x y
    | CComp (x, y) ->
      fprintf ppf "%s;;%s" x y
    | Coercion c ->
      fprintf ppf "%a"
        pp_coercion c
    | MakeCls (x, cls, f) ->
      fprintf ppf "cls %s = %a in %a"
        x
        pp_cls cls
        pp_exp f
    | MakeTyCls (x, cls, f) ->
      fprintf ppf "tcls %s = %a in %a"
        x
        pp_cls cls
        pp_exp f
    | Let (x, f1, f2) ->
        fprintf ppf "let %s = %a in %a"
          x
          pp_exp f1
          pp_exp f2
  and pp_match ppf = function
    | (mf, e) :: m -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        pp_exp e
        pp_match m
    | [] -> fprintf ppf ""

  let pp_fv ppf x =
    fprintf ppf "%s"
      x

  let pp_print_fv ppf fvl =
    let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf fvs = pp_print_list pp_fv ppf fvs ~pp_sep:pp_sep in
    fprintf ppf "%a"
      pp_list fvl

  let pp_fundef ppf fundef = match fundef with
  | FundefD { name; arg = (y, z); vs; tvs; body } ->
    if List.length vs = 0 then
      fprintf ppf "let rec %s %a(%s, %s) = %a"
        name
        pp_tyabses tvs
        y
        z
        pp_exp body
    else
      fprintf ppf "let rec %s %a(%s, %s) = %a (fv:%a)"
        name
        pp_tyabses tvs
        y
        z
        pp_exp body
        pp_print_fv vs
  | FundefM { name; arg = y; vs; tvs; body } -> 
    if List.length vs = 0 then
      fprintf ppf "let rec %s %a%s = %a"
        name
        pp_tyabses tvs
        y
        pp_exp body
    else
      fprintf ppf "let rec %s %a%s = %a (fv:%a)"
        name
        pp_tyabses tvs
        y
        pp_exp body
        pp_print_fv vs
  | FundefTy { name; vs = vs; tvs; body } ->
    if List.length vs = 0 then
      fprintf ppf "let %s %a= %a"
        name
        pp_tyabses tvs
        pp_exp body
    else
      fprintf ppf "let %s %a= %a (fv:%a)"
        name
        pp_tyabses tvs
        pp_exp body
        pp_print_fv vs
  let pp_toplevel ppf toplevel =
    let pp_sep ppf () = fprintf ppf "\n" in
    let pp_list ppf defs = pp_print_list pp_fundef ppf defs ~pp_sep:pp_sep in
    fprintf ppf "%a"
      pp_list toplevel

  let pp_program ppf = function
    | Prog (toplevel, cf) ->
      if List.length toplevel = 0 
        then 
          fprintf ppf "exp:\n%a"
            pp_exp cf
        else
          fprintf ppf "%a\nexp:\n%a"
            pp_toplevel toplevel
            pp_exp cf
end

module C = struct
  open Syntax.C

  let sep_newline ppf () = pp_print_string ppf "\n"
  let sep_comma ppf () = pp_print_string ppf ", "

  let rec pp_ty ppf = function
    | INT -> pp_print_string ppf "int"
    | VOID -> pp_print_string ppf "void"
    | PTR t -> fprintf ppf "%a*" pp_ty t
    | ARRAY t -> fprintf ppf "%a[]" pp_ty t
    | VALUE -> pp_print_string ppf "value"
    | FUN -> pp_print_string ppf "fun"
    | LST -> pp_print_string ppf "lst"
    | TPL -> pp_print_string ppf "tpl"
    | TPL_RAW -> pp_print_string ppf "tpl_raw"
    | ARR -> pp_print_string ppf "arr"
    | ARR_RAW -> pp_print_string ppf "arr_raw"
    | REF -> pp_print_string ppf "ref"
    | CRC -> pp_print_string ppf "crc"
    | RANGE -> pp_print_string ppf "range"
    | TY -> pp_print_string ppf "ty"

  let pp_preop ppf = function
    | Not -> fprintf ppf "!"
    | Deref -> fprintf ppf "*"

  let pp_postop ppf = function
    | Incr -> fprintf ppf "++"

  let pp_binop ppf = function
    | Plus -> fprintf ppf "+"
    | Minus -> fprintf ppf "-"
    | Mult -> fprintf ppf "*"
    | Div -> fprintf ppf "/"
    | Mod -> fprintf ppf "%%"
    | And -> fprintf ppf "&&"
    | Or -> fprintf ppf "||"
    | Eq -> fprintf ppf "=="
    | Neq -> fprintf ppf "!="
    | Lte -> fprintf ppf "<="
    | Lt -> fprintf ppf "<"
    | Gte -> fprintf ppf ">="
    | Gt -> fprintf ppf ">"
    | FPlus -> fprintf ppf "+"
    | FMinus -> fprintf ppf "-"
    | FMult -> fprintf ppf "*"
    | FDiv -> fprintf ppf "/"
    | FEq -> fprintf ppf "=="
    | FNeq -> fprintf ppf "!="
    | FLte -> fprintf ppf "<="
    | FLt -> fprintf ppf "<"
    | FGte -> fprintf ppf ">="
    | FGt -> fprintf ppf ">"

  let rec pp_exp ppf = function
    | Var x -> pp_print_string ppf x
    | Dot (e, x) -> fprintf ppf "%a.%s" pp_exp e x
    | Arrow (e, x) -> fprintf ppf "%a->%s" pp_exp e x
    | Cast (t, e) -> fprintf ppf "((%a)%a)" pp_ty t pp_exp e
    | Index (e1, e2) -> fprintf ppf "%a[%a]" pp_exp e1 pp_exp e2
    | Int i -> pp_print_int ppf i
    | Float f -> pp_print_float ppf f
    | Str s -> fprintf ppf "\"%s\"" s
    | PreOp (op, e) -> fprintf ppf "%a(%a)" pp_preop op pp_exp e
    | PostOp (e, op) -> fprintf ppf "%a%a" pp_exp e pp_postop op 
    | BinOp (e1, op, e2) -> fprintf ppf "%a %a %a" pp_exp e1 pp_binop op pp_exp e2
    | App (e, es) -> fprintf ppf "%a(%a)" pp_exp e (pp_print_list ~pp_sep:sep_comma pp_exp) es
    | Addr x -> fprintf ppf "&%s" x
    | Null -> pp_print_string ppf "NULL"
    | Malloc (t, e) -> fprintf ppf "(%a)GC_MALLOC(%a)" pp_ty t pp_exp e
    | Sizeof t -> fprintf ppf "sizeof(%a)" pp_ty t
    | Struct l ->
      let pp_content ppf (x, e) = fprintf ppf ".%s = %a" x pp_exp e in
      fprintf ppf "{ %a }" (pp_print_list ~pp_sep:sep_comma pp_content) l
    | Array es ->
      fprintf ppf "{ %a }" (pp_print_list ~pp_sep:sep_comma pp_exp) es

  let rec pp_stm ppf = function
    | SDecl (t, x, None) -> fprintf ppf "%a %s;" pp_ty t x
    | SDecl (t, x, Some e) -> fprintf ppf "%a %s = %a;" pp_ty t x pp_exp e
    | SAssign (e1, e2) -> fprintf ppf "%a = %a;" pp_exp e1 pp_exp e2
    | SReturn e -> fprintf ppf "return %a;" pp_exp e
    | SIf (e, s1, [SIf _ as s2]) ->
      fprintf ppf "if (%a){\n%a\n} else %a"
        pp_exp e
        (pp_print_list ~pp_sep:sep_newline pp_stm) s1
        pp_stm s2
    | SIf (e, s1, s2) ->
      fprintf ppf "if (%a){\n%a\n} else {\n%a\n}"
        pp_exp e
        (pp_print_list ~pp_sep:sep_newline pp_stm) s1
        (pp_print_list ~pp_sep:sep_newline pp_stm) s2
    | SFor ((s, e1, e2), ss) ->
      fprintf ppf "for (%a %a; %a){\n%a\n}"
        pp_stm s
        pp_exp e1
        pp_exp e2
        (pp_print_list ~pp_sep:sep_newline pp_stm) ss
    | SExp e -> fprintf ppf "%a;" pp_exp e

  let pp_spec ppf = function
    | Static -> pp_print_string ppf "static "
    | No -> pp_print_string ppf ""  
    
  let pp_toplevel ppf = function
    | Include s -> fprintf ppf "#include %s\n" s
    | Decl (spec, t, x, None) -> fprintf ppf "%a%a %s;\n" pp_spec spec pp_ty t x
    | Decl (spec, t, x, Some e) -> fprintf ppf "%a%a %s = %a;\n" pp_spec spec pp_ty t x pp_exp e
    | FunDecl (spec, { ret_ty; fname; params }) ->
      fprintf ppf "%a%a %s(%a);\n"
        pp_spec spec pp_ty ret_ty fname
        (pp_print_list ~pp_sep:sep_comma pp_ty) (List.map fst params)
    | FunDef (spec, { ret_ty; fname; params }, body) ->
      let pp_param ppf (t, x) = fprintf ppf "%a %s" pp_ty t x in
      fprintf ppf "%a%a %s(%a){\n%a\n}\n"
        pp_spec spec pp_ty ret_ty fname
        (pp_print_list ~pp_sep:sep_comma pp_param) params
        (pp_print_list ~pp_sep:sep_newline pp_stm) body
  
  let pp_program ppf program =
    let pp_sep ppf () = pp_print_string ppf "\n" in
    pp_print_list ~pp_sep pp_toplevel ppf program
end
