open Format
open Syntax

exception Syntax_error

(* === utils === *)

let with_paren flag ppf_e ppf e =
  fprintf ppf (if flag then "(%a)" else "%a") ppf_e e

(* === pp for ty === *)

let rec level_ty = function
  | TyVar (_, { contents = Some u }) -> level_ty u
  | TyDyn | TyVar _ | TyInt | TyBool | TyUnit -> 100
  | TyList _ | TyRef _ -> 90
  | TyTuple _ -> 80
  | TyFun _ -> 70

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

(* === pp for binop === *)

(* TODO: delete later *)
let gt_binop op1 op2 = match op1, op2 with
  | (Plus | Minus | Mult | Div | Mod), (Eq | Neq | Lt | Lte | Gt | Gte)
  | (Mult | Div | Mod), (Plus | Minus) -> true
  | _ -> false

let gte_binop op1 op2 = match op1, op2 with
  | (Eq | Neq | Lt | Lte | Gt | Gte), (Eq | Neq | Lt | Lte | Gt | Gte)
  | (Mult | Div | Mod), (Mult | Div | Mod)
  | (Plus | Minus), (Plus | Minus) -> true
  | _ -> gt_binop op1 op2

let pp_binop ppf op =
  pp_print_string ppf begin
    match op with
    | Plus -> "+"
    | Minus -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Mod -> "mod"
    | Eq -> "="
    | Neq -> "<>"
    | Lt -> "<"
    | Lte -> "<="
    | Gt -> ">"
    | Gte -> ">="
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
  | MatchVar (x, _) -> fprintf ppf "%s" x
  (* | MatchAsc (mf, u) -> fprintf ppf "(%a : %a)" pp_matchform mf pp_ty u *)
  | MatchILit i -> pp_print_int ppf i
  | MatchBLit b -> pp_print_bool ppf b
  | MatchULit -> pp_print_string ppf "()"
  (* | MatchNil u -> fprintf ppf "([] : %a)" pp_ty (TyList u) *)
  | MatchNil _ -> fprintf ppf "[]"
  | MatchCons (mf1, mf2) as mf -> 
    fprintf ppf "%a :: %a"
      (with_paren (gte_matchform mf mf1) pp_matchform) mf1
      pp_matchform mf2
  | MatchTuple mfs as mf ->
    let pp_sep ppf () = fprintf ppf ", " in
    let pp_list ppf matches = pp_print_list (fun ppf mf' -> (with_paren (gte_matchform mf mf') pp_matchform) ppf mf') ppf matches ~pp_sep:pp_sep in
    fprintf ppf "(%a)"
      pp_list mfs
  | MatchWild _ -> pp_print_string ppf "_"

(* === pp for coercion === *)

let pp_tag ppf = function
  | I -> pp_print_string ppf "int"
  | B -> pp_print_string ppf "bool"
  | U -> pp_print_string ppf "unit"
  | Ar -> pp_print_string ppf "(? -> ?)"
  | Li -> pp_print_string ppf "[?]"
  | Tp n ->
    let rec pp_dyn_tuple ppf i =
      if i = 1 then fprintf ppf "?"
      else fprintf ppf "? * %a" pp_dyn_tuple (i - 1)
    in
    fprintf ppf "(%a)"
      pp_dyn_tuple n
  | Rf -> pp_print_string ppf ":?:"

let level_coercion = function
  | CInj _ | CProj _ | CTvInj _ | CTvProj _ | CTvProjInj _ | CId _ | CFail _ -> 100
  | CList _ | CRef _ -> 80
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
    | CRef _ -> raise Syntax_error
  in
  pp_coercion ppf c

let pp_coercion ppf c =
  pp_coercion_main ppf ~pp_ty:pp_ty c

let pp_coercion2 ppf c = 
  pp_coercion_main ppf ~pp_ty:pp_ty2 c

module ITGL = struct
  open Syntax.ITGL

  let pp_constr ppf = function
    | CEqual (u1, u2) ->
      fprintf ppf "%a =.= %a" pp_ty u1 pp_ty u2
    | CConsistent (u1, u2) ->
      fprintf ppf "%a ~.~ %a" pp_ty u1 pp_ty u2

  let level_exp = function
    | Var _ | IConst _ | BConst _ | UConst _ | NilExp _ | TupleExp _ | AscExp _ -> 100
    | DerefExp _ -> 90
    | AppExp _ | RefExp _ -> 80
    | BinOp (_, (Mult | Div | Mod), _, _) -> 70
    | BinOp (_, (Plus | Minus), _, _) -> 60
    | ConsExp _ -> 50
    | BinOp (_, (Eq | Neq | Lt | Lte | Gt | Gte), _, _) -> 40
    | SubstExp _ -> 20
    | IfExp _ | FunExp _ | FixExp _ | LetExp _ | MatchExp _ -> 10
  
  let gt_exp e1 e2 =
    level_exp e1 > level_exp e2

  let gte_exp e1 e2 =
    level_exp e1 >= level_exp e2

  let rec pp_exp ppf = function
    | Var (_, x, ys) -> pp_print_var ppf (x, !ys)
    | BConst (_, b) -> pp_print_bool ppf b
    | IConst (_, i) -> pp_print_int ppf i
    | UConst _ -> pp_print_string ppf "()"
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
    | Var _ | IConst _ | BConst _ | UConst | NilExp _ | TupleExp _ | CoercionExp _ -> 100
    | CSeqExp _ -> 95
    | DerefExp _ | DerefAnotExp _ -> 90
    | AppDExp _ | AppMExp _ | RefExp _ -> 80
    | CAppExp _ -> 75
    | BinOp ((Mult | Div | Mod), _, _) -> 70
    | BinOp ((Plus | Minus), _, _) -> 60
    | ConsExp _ -> 50
    | BinOp ((Eq | Neq | Lt | Lte | Gt | Gte), _, _) -> 40
    | SubstExp _ | SubstAnotExp _ -> 20
    | CastExp _ -> 15
    | IfExp _ | FunBExp _ | FunSExp _ | FunDualExp _ | FixBExp _ | FixSExp _ | FixDualExp _ | FunTyExp _ | LetExp _ | MatchExp _ -> 10
  
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
    | BConst b -> pp_print_bool ppf b
    | IConst i -> pp_print_int ppf i
    | UConst -> pp_print_string ppf "()"
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
    | FunBExp (xs, (x1, u1), f) ->
      fprintf ppf "%afun (%s: %a) -> %a"
        pp_tyabses xs
        x1
        pp_ty u1
        pp_exp f
    | FixBExp (xs, (x, y, u1, u2), f) ->
      fprintf ppf "%afix %s (%s: %a): %a = %a"
        pp_tyabses xs
        x
        y
        pp_ty u1
        pp_ty u2
        pp_exp f
    | FunSExp (xs, (x1, u1), c, f) ->
      fprintf ppf "%afun ((%s: %a), %s) -> %a"
        pp_tyabses xs
        x1
        pp_ty u1
        c
        pp_exp f
    | FixSExp (xs, (x, y, u1, u2), c, f) ->
      fprintf ppf "%afix %s ((%s: %a), %s): %a = %a"
        pp_tyabses xs
        x
        y
        pp_ty u1
        c
        pp_ty u2
        pp_exp f
    | FunDualExp (xs, (x1, u1), c, (f1, f2)) ->
      fprintf ppf "%afun ((%s: %a), %s) -> (%a | %a)"
        pp_tyabses xs
        x1
        pp_ty u1
        c
        pp_exp f1
        pp_exp f2
    | FixDualExp (xs, (x, y, u1, u2), c, (f1, f2)) ->
      fprintf ppf "%afix %s ((%s: %a), %s): %a = (%a | %a)"
        pp_tyabses xs
        x
        y
        pp_ty u1
        c
        pp_ty u2
        pp_exp f1
        pp_exp f2
    | FunTyExp (xs, f) ->
      fprintf ppf "%a%a"
        pp_tyabses xs
        pp_exp f
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
    | CSeqExp (f1, f2) ->
        fprintf ppf "%a;;%a"
          pp_exp f1
          pp_exp f2
    | CastExp (f1, u1, u2, _) as f ->
      begin match f1 with
      | CastExp (_, _, u1', _) when u1 = u1' ->
        fprintf ppf "%a => %a"
          (with_paren (gt_exp f f1) pp_exp) f1
          pp_ty u2
      | CastExp _ ->
        raise Syntax_error
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
    | DerefExp f' as f ->
      fprintf ppf "!%a"
        (with_paren (gte_exp f f') pp_exp) f'
    | DerefAnotExp (f', u) as f ->
      fprintf ppf "!%a@%a"
        (with_paren (gt_exp f f') pp_exp) f'
        pp_ty u
    | SubstExp (f1, f2) as f ->
      fprintf ppf "%a := %a"
        (with_paren (gte_exp f f1) pp_exp) f1
        (with_paren (gte_exp f f2) pp_exp) f2
    | SubstAnotExp (f1, f2, u) as f ->
      fprintf ppf "%a := %a@%a"
        (with_paren (gte_exp f f1) pp_exp) f1
        (with_paren (gte_exp f f2) pp_exp) f2
        pp_ty u
    (* | _ -> raise @@ Failure "yet" *)
  and pp_match ppf = function
    | ((mf, e1) :: m, e) -> 
      fprintf ppf " | %a -> %a%a"
        pp_matchform mf
        (with_paren (gte_exp e e1) pp_exp) e1
        pp_match (m, e)
    | ([], _) -> fprintf ppf ""

  let pp_program ppf = function
    | Exp e -> pp_exp ppf e
    | LetDecl (x, f) ->
      fprintf ppf "let %s = %a"
        x
        pp_exp f

  (*let pp_tag ppf t = pp_ty ppf @@ tag_to_ty t*)

  let gt_value v1 v2 = match v1, v2 with
    | (BoolV _ | IntV _ | UnitV | FunBV _ | FunSV _ | FunDualV _ | FunTyV _ | NilV | TupleV _ | CoercionV _ | Tagged _ | CoerceV _), ConsV _ -> true
    | (BoolV _ | IntV _ | UnitV | FunBV _ | FunSV _ | FunDualV _ | FunTyV _ | NilV | TupleV _ | CoercionV _), (Tagged _ | CoerceV _) -> true
    | _ -> false

  let gte_value v1 v2 = match v1, v2 with
    | (FunBV _ | FunSV _ | FunDualV _ | FunTyV _ ), (FunBV _ | FunSV _ | FunDualV _ | FunTyV _) -> true
    | Tagged _, Tagged _ -> true
    | CoerceV _, CoerceV _ -> true
    | ConsV _, ConsV _ -> true
    | TupleV _, TupleV _ -> true
    | _ -> gt_value v1 v2

  let rec pp_value ppf = function
    | BoolV b -> pp_print_bool ppf b
    | IntV i -> pp_print_int ppf i
    | UnitV -> pp_print_string ppf "()"
    | FunBV _ | FunSV _ | FunDualV _ | FunTyV _ -> pp_print_string ppf "<fun>"
    | CoerceV (v1, c) as v ->
      fprintf ppf "%a<<%a>>"
        (with_paren (gt_value v v1) pp_value) v1
        pp_coercion c
    | CoercionV c -> 
      fprintf ppf "%a"
        pp_coercion c
    | NilV -> pp_print_string ppf "[]"
    | ConsV (v1, v2) as v ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_value v v1) pp_value) v1
        (with_paren (gt_value v v2) pp_value) v2
    | TupleV vs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vals = pp_print_list pp_value ppf vals ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list vs
    | Tagged (t, v) ->
      fprintf ppf "%a: %a => ?"
        pp_value v
        pp_tag t

  let rec pp_value2 ppf = function
    | BoolV b -> pp_print_bool ppf b
    | IntV i -> pp_print_int ppf i
    | UnitV -> pp_print_string ppf "()"
    | FunBV _ | FunSV _ | FunDualV _ | FunTyV _ -> pp_print_string ppf "<fun>"
    | CoerceV (v1, c) as v ->
      fprintf ppf "%a<<%a>>"
        (with_paren (gt_value v v1) pp_value2) v1
        pp_coercion2 c
    | CoercionV c -> 
      fprintf ppf "%a"
        pp_coercion2 c
    | NilV -> pp_print_string ppf "[]"
    | ConsV (v1, v2) as v ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_value v v1) pp_value2) v1
        (with_paren (gt_value v v2) pp_value2) v2
    | TupleV vs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vals = pp_print_list pp_value2 ppf vals ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list vs
    | Tagged (t, v) ->
      fprintf ppf "%a: %a => ?"
        pp_value2 v
        pp_tag t
end

module KNorm = struct 
  open Syntax.KNorm

  let gt_exp e e1 = match e, e1 with
    | (Var _ | IConst _ | Nil), _ -> raise @@ Syntax_error(* "gt_exp: value-exp was given as e"*)
    | (Add _ | Sub _ | Mul _ | Div _ | Mod _ | Cons _ | Tuple _ | AppDExp _ | AppTy _ | AppMExp _ | Hd _ | Tl _ | Tget _), _ -> raise @@ Syntax_error(* "gt_exp : expression not contain exp was given as e"*)
    | (IfEqExp _ | IfLteExp _ | MatchExp _), (LetExp _ | LetFunExp _) -> true
    | _ -> false
  
  let gte_exp e e1 = match e, e1 with
    (* | Add _, Add _ | Sub _, Sub _ | Mul _, Mul _ | Div _, Div _ | Mod _, Mod _ | Cons _, Cons _ | Tuple _, Tuple _ -> true *)
    (* | AppTy _, AppTy _ | AppDExp _, AppDExp _ | AppMExp _, AppMExp _ -> true *)
    (* | Hd _, Hd _ | Tl _, Tl _ | Tget _, Tget _ -> true *)
    | (LetExp _ | LetFunExp _) , (LetExp _ | LetFunExp _) -> true
    | (IfEqExp _ | IfLteExp _), (IfEqExp _ | IfLteExp _) -> true
    | MatchExp _, MatchExp _ -> true
    | _ -> gt_exp e e1

  let rec pp_exp ppf = function
    | Var x -> pp_print_string ppf x
    | IConst i -> pp_print_int ppf i
    | Nil -> pp_print_string ppf "[]"
    | Add (x, y) -> fprintf ppf "%s + %s" x y
    | Sub (x, y) -> fprintf ppf "%s - %s" x y
    | Mul (x, y) -> fprintf ppf "%s * %s" x y
    | Div (x, y) -> fprintf ppf "%s / %s" x y
    | Mod (x, y) -> fprintf ppf "%s mod %s" x y
    | Cons (x, y) -> fprintf ppf "%s :: %s" x y
    | Tuple xs -> 
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf exps = pp_print_list pp_print_string ppf exps ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list xs
    | Tget (x, i) -> fprintf ppf "tget(%s, %d)" x i
    | Hd x -> fprintf ppf "hd(%s)" x
    | Tl x -> fprintf ppf "tl(%s)" x
    | IfEqExp (x, y, e1, e2) ->
      fprintf ppf "if %s=%s then %a else %a"
        x
        y
        pp_exp e1
        pp_exp e2
    | IfLteExp (x, y, e1, e2) ->
      fprintf ppf "if %s<=%s then %a else %a"
        x
        y
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
    | CSeqExp (x, y) -> 
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

  let gt_value v1 v2 = match v1, v2 with
    | (IntV _ | FunSV _ | FunDualV _ | FunBV _ | NilV | TupleV _ | CoercionV _ | CoerceV _), ConsV _ -> true
    | (IntV _ | FunSV _ | FunDualV _ | FunBV _ | NilV | TupleV _ | CoercionV _), CoerceV _ -> true
    | _ -> false

  let gte_value v1 v2 = match v1, v2 with
    | (FunSV _ | FunDualV _ | FunBV _ | FunTyV _), (FunSV _ | FunDualV _ | FunBV _ | FunTyV _) -> true
    | CoerceV _, CoerceV _ -> true
    | ConsV _, ConsV _ -> true
    | TupleV _, TupleV _ -> true
    | _ -> gt_value v1 v2

  let rec pp_value ppf = function
    | IntV i -> pp_print_int ppf i
    | NilV -> pp_print_string ppf "[]"
    | ConsV (v1, v2) as v ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_value v v1) pp_value) v1
        (with_paren (gt_value v v2) pp_value) v2
    | TupleV vs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vals = pp_print_list pp_value ppf vals ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list vs
    | FunSV _ | FunDualV _ | FunBV _ | FunTyV _ -> pp_print_string ppf "<fun>"
    | CoerceV (v1, c) as v -> 
      fprintf ppf "%a<<%a>>"
        (with_paren (gt_value v v1) pp_value) v1
        pp_coercion c
    | Tagged (t, v) ->
      fprintf ppf "%a: %a => ?"
        pp_value v
        pp_tag t
    | CoercionV c -> pp_coercion ppf c

  let rec pp_value2 ppf = function
    | IntV i -> pp_print_int ppf i
    | NilV -> pp_print_string ppf "[]"
    | ConsV (v1, v2) as v ->
      fprintf ppf "%a :: %a"
        (with_paren (gte_value v v1) pp_value2) v1
        (with_paren (gt_value v v2) pp_value2) v2
    | TupleV vs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vals = pp_print_list pp_value2 ppf vals ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list vs
    | FunSV _ | FunDualV _ | FunBV _ | FunTyV _ -> pp_print_string ppf "<fun>"
    | CoerceV (v1, c) as v -> 
      fprintf ppf "%a<<%a>>"
        (with_paren (gt_value v v1) pp_value2) v1
        pp_coercion2 c
    | Tagged (t, v) ->
      fprintf ppf "%a: %a => ?"
        pp_value2 v
        pp_tag t
    | CoercionV c -> pp_coercion2 ppf c
end

module Cls = struct
  open Syntax.Cls

  let gt_coercion c1 c2 = match c1, c2 with
    | (CTvInj _ | CTvProj _ | CId | CFun _ | CList _ | CTuple _), (CSeqInj _ | CSeqProj _) -> true
    | _ -> false

  let gte_coercion c1 c2 = match c1, c2 with
    | CFun _, CFun _ -> true
    | CTuple _, CTuple _ -> true
    (* | CList _, CList _ is intentionally ommited *)
    | _ -> gt_coercion c1 c2

  let rec pp_coercion ppf = function
    | CId -> fprintf ppf "id"
    (* | Fail _ -> fprintf ppf "⊥" *)
    | CSeqInj (c, t) -> fprintf ppf "%a;%a!" pp_coercion c pp_tag t
    | CSeqProj (t, _, c) -> fprintf ppf "%a?p;%a" pp_tag t pp_coercion c
    (* | SeqProjInj (t1, _, c, t2) -> fprintf ppf "%a?p;%a;%a!" pp_tag t1 pp_coercion c pp_tag t2 *)
    | CTvInj (tv, _) -> fprintf ppf "%a!" pp_ty (TyVar tv)
    | CTvProj (tv, _) -> fprintf ppf "%a?p" pp_ty (TyVar tv)
    (* | TvProjInj (tv, _) -> fprintf ppf "?p%a!" pp_ty (TyVar tv) *)
    | CFun (c1, c2) -> fprintf ppf "%a->%a" pp_coercion c1 pp_coercion c2
    | CList c -> fprintf ppf "[%a]" pp_coercion c
    | CTuple cs as c ->
      let pp_sep ppf () = fprintf ppf "*" in
      let pp_list ppf crcs = pp_print_list (fun ppf c' -> (with_paren (gte_coercion c c') pp_coercion) ppf c') ppf crcs ~pp_sep:pp_sep in
      fprintf ppf "%a"
        pp_list cs

  let pp_tyabses ppf tyvars =
    if List.length tyvars = 0 then
      fprintf ppf ""
    else
      let pp_sep ppf () = fprintf ppf "," in
      let pp_list ppf types = pp_print_list pp_ty ppf types ~pp_sep:pp_sep in
      fprintf ppf "[%a] " pp_list @@ List.map (fun x -> TyVar x) tyvars
  
  let pp_print_cls ppf { entry = x; actual_fv = ids } =
    if List.length ids = 0 then 
      fprintf ppf "%s" x
    else let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf xs = pp_print_list pp_print_string ppf xs ~pp_sep:pp_sep in
    fprintf ppf "%s[%a]"
      x
      pp_list ids

  let rec pp_exp ppf = function
    | Var x -> pp_print_string ppf x
    | Int i -> pp_print_int ppf i
    | Nil -> pp_print_string ppf "[]"
    | Add (x, y) -> fprintf ppf "%s + %s" x y
    | Sub (x, y) -> fprintf ppf "%s - %s" x y
    | Mul (x, y) -> fprintf ppf "%s * %s" x y
    | Div (x, y) -> fprintf ppf "%s / %s" x y
    | Mod (x, y) -> fprintf ppf "%s mod %s" x y
    | Cons (x, y) -> fprintf ppf "%s :: %s" x y
    | Tuple xs ->
      let pp_sep ppf () = fprintf ppf ", " in
      let pp_list ppf vars = pp_print_list pp_print_string ppf vars ~pp_sep:pp_sep in
      fprintf ppf "(%a)"
        pp_list xs
    | Hd x -> fprintf ppf "hd(%s)" x
    | Tl x -> fprintf ppf "tl(%s)" x
    | Tget (x, i) -> fprintf ppf "tget(%s, %i)" x i
    | IfEq (x, y, e1, e2) ->
      fprintf ppf "if %s=%s then %a else %a"
        x
        y
        pp_exp e1
        pp_exp e2
    | IfLte (x, y, e1, e2) ->
      fprintf ppf "if %s<=%s then %a else %a"
        x
        y
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
    | AppTy (x, _, _, tas) | AppTyFun (x, _, _, tas) ->
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
    | CSeq (x, y) ->
      fprintf ppf "%s;;%s" x y
    | Coercion c ->
      fprintf ppf "%a"
        pp_coercion c
    | MakeCls (x, cls, _, f) ->
      fprintf ppf "cls %s = %a in %a"
        x
        pp_print_cls cls
        pp_exp f
    | MakeTyCls (x, cls, _, f) ->
      fprintf ppf "tcls %s = %a in %a"
        x
        pp_print_cls cls
        pp_exp f
    | Let (x, f1, f2) ->
        fprintf ppf "let %s = %a in %a"
          x
          pp_exp f1
          pp_exp f2
    | Insert _ -> raise @@ Syntax_error (*"insert or setty was applied to Cls.pp_exp"*)
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
  | FundefD { name = l; tvs = (tvs, _); arg = (y, z); formal_fv = fvl; body = f} ->
    if List.length fvl = 0 then
      fprintf ppf "let rec %s %a(%s, %s) = %a"
        l
        pp_tyabses tvs
        y
        z
        pp_exp f
    else
      fprintf ppf "let rec %s %a(%s, %s) = %a (fv:%a)"
        l
        pp_tyabses tvs
        y
        z
        pp_exp f
        pp_print_fv fvl
  | FundefM { name = l; tvs = (tvs, _); arg = y; formal_fv = fvl; body = f} -> 
    if List.length fvl = 0 then
      fprintf ppf "let rec %s %a%s = %a"
        l
        pp_tyabses tvs
        y
        pp_exp f
    else
      fprintf ppf "let rec %s %a%s = %a (fv:%a)"
        l
        pp_tyabses tvs
        y
        pp_exp f
        pp_print_fv fvl
  | FundefTy { name = l; tvs = (tvs, _); formal_fv = fvl; body = f} ->
    if List.length fvl = 0 then
      fprintf ppf "let %s %a= %a"
        l
        pp_tyabses tvs
        pp_exp f
    else
      fprintf ppf "let %s %a= %a (fv:%a)"
        l
        pp_tyabses tvs
        pp_exp f
        pp_print_fv fvl
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
