open Syntax

(* Substitutions for type variables *)

type substitution = tyvar * ty
type substitutions = substitution list

(* S(t) *)
let subst_type (s : substitutions) (u : ty) =
  (* {X':->U'}(U) *)
  let rec subst u ((a', _), u' as s0) = match u with
    | TyFun (u1, u2) -> TyFun (subst u1 s0, subst u2 s0)
    | TyList u -> TyList (subst u s0)
    | TyTuple us -> TyTuple (List.map (fun u -> subst u s0) us)
    | TyRef u -> TyRef (subst u s0)
    | TyVar (a, { contents = None }) when a = a' -> u'
    | TyVar (_, { contents = Some u }) -> subst u s0
    | _ as u -> u
  in
  List.fold_left subst u s

let subst_tyarg s = function
  | Ty u -> Ty (subst_type s u)
  | TyNu -> TyNu

let rec subst_coercion ~monotonic s = function
  | CInj _ | CProj _ as c -> c
  | CTvInj ((a, _ as tv), p) ->
    CTvInj ((a, { contents = Some (subst_type s (TyVar tv)) }), p)
  | CTvProj ((a, _ as tv), p) ->
    (CTvProj ((a, { contents = Some (subst_type s (TyVar tv)) }), p))
  | CTvProjInj ((a, _ as tv), p, q) ->
    CTvProjInj ((a, { contents = Some (subst_type s (TyVar tv)) }), p, q)
  | CFun (c1, c2) -> CFun (subst_coercion ~monotonic s c1, subst_coercion ~monotonic s c2)
  | CList c -> CList (subst_coercion ~monotonic s c)
  | CTuple cs -> CTuple (List.map (fun c -> subst_coercion ~monotonic s c) cs)
  | CId u -> CId (subst_type s u)
  | CSeq (c1, c2) -> CSeq (subst_coercion ~monotonic s c1, subst_coercion ~monotonic s c2)
  | CFail _ as c -> c
  | CRef (c1, c2) -> CRef (subst_coercion ~monotonic s c1, subst_coercion ~monotonic s c2)
  | CMRef (u1, u2) -> CMRef (subst_type s u1, subst_type s u2)

let rec subst_mf s = function
  | MatchILit _ | MatchBLit _ | MatchULit as mf -> mf
  | MatchWild u -> MatchWild (subst_type s u)
  | MatchVar (x, u) -> MatchVar (x, subst_type s u)
  | MatchNil u -> MatchNil (subst_type s u)
  | MatchCons (mf1, mf2) -> MatchCons (subst_mf s mf1, subst_mf s mf2)
  | MatchTuple mfs -> MatchTuple (List.map (fun mf -> subst_mf s mf) mfs)

module CC = struct
  open Syntax.CC

  let rec subst_exp ~monotonic s = function
    | Var (x, ys) -> Var (x, List.map (subst_tyarg s) ys)
    | IConst _
    | BConst _
    | UConst as f -> f
    | BinOp (op, f1, f2) -> BinOp (op, subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | IfExp (f1, f2, f3) -> IfExp (subst_exp ~monotonic s f1, subst_exp ~monotonic s f2, subst_exp ~monotonic s f3)
    | FunExp (tvs, fd) ->
      (* Remove substitutions captured by tvs *)
      let s = List.filter (fun (x, _) -> not @@ List.memq x tvs) s in
      FunExp (tvs, subst_fund ~monotonic s fd)
    | FixExp (tvs, fixd) ->
      let s = List.filter (fun (x, _) -> not @@ List.memq x tvs) s in
      FixExp (tvs, subst_fixd ~monotonic s fixd)
    | NilExp u -> NilExp (subst_type s u)
    | ConsExp (f1, f2) -> ConsExp (subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | TupleExp fs -> TupleExp (List.map (fun f -> subst_exp ~monotonic s f) fs)
    | AppMExp (f1, f2) -> AppMExp (subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | AppDExp (f1, (f2, f3)) -> AppDExp (subst_exp ~monotonic s f1, (subst_exp ~monotonic s f2, subst_exp ~monotonic s f3))
    | CastExp (f, u1, u2, r_p) -> CastExp (subst_exp ~monotonic s f, subst_type s u1, subst_type s u2, r_p)
    | CoercionExp c -> CoercionExp (subst_coercion ~monotonic s c)
    | CAppExp (f1, f2) -> CAppExp (subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | CSeqExp (f1, f2) -> CSeqExp (subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | MatchExp (f, ms) ->
      MatchExp (subst_exp ~monotonic s f, List.map (fun (mf, f) -> subst_mf s mf, subst_exp ~monotonic s f) ms)
    | LetExp (y, f1, f2) ->
      LetExp (y, subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | RefExp (f, u) -> RefExp (subst_exp ~monotonic s f, subst_type s u)
    | DerefExp (f, uo) -> DerefExp (subst_exp ~monotonic s f, Option.map (subst_type s) uo)
    | SubstExp (f1, f2, uo) -> SubstExp (subst_exp ~monotonic s f1, subst_exp ~monotonic s f2, Option.map (subst_type s) uo)
  and subst_fund ~monotonic s = function
    | FunB ((x, u), f) -> FunB ((x, subst_type s u), subst_exp ~monotonic s f)
    | FunS ((x, u1), (k, uk), f) ->
      FunS ((x, subst_type s u1), (k, subst_type s uk), subst_exp ~monotonic s f)
    | FunDual ((x, u1), (k, uk), (f1, f2)) ->
      FunDual ((x, subst_type s u1), (k, subst_type s uk), (subst_exp ~monotonic s f1, subst_exp ~monotonic s f2))
    | FunTy f -> FunTy (subst_exp ~monotonic s f)
  and subst_fixd ~monotonic s = function
    | FixB (x, (y, u1), u2, f) -> FixB (x, (y, subst_type s u1), subst_type s u2, subst_exp ~monotonic s f)
    | FixS (x, (y, u1), u2, (k, uk), f) ->
      FixS (x, (y, subst_type s u1), subst_type s u2, (k, subst_type s uk), subst_exp ~monotonic s f)
    | FixDual (x, (y, u1), u2, (k, uk), (f1, f2)) ->
      FixDual (x, (y, subst_type s u1), subst_type s u2, (k, subst_type s uk), (subst_exp ~monotonic s f1, subst_exp ~monotonic s f2))
end

module KNorm = struct
  open Syntax.KNorm

  let rec subst_exp ~monotonic s = function
    | Var _ | IConst _ | Nil as f -> f
    | Add _ | Sub _ | Mul _ | Div _ | Mod _ | Cons _ | Tuple _ | Hd _ | Tl _ | Tget _ as f -> f
    | IfEqExp (x, y, f1, f2) -> IfEqExp (x, y, subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | IfLteExp (x, y, f1, f2) -> IfLteExp (x, y, subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | MatchExp (x, ms) -> MatchExp (x, List.map (fun (mf, f) -> subst_mf s mf, subst_exp ~monotonic s f) ms)
    | AppDExp _ | AppMExp _ | CAppExp _ | CSeqExp _ as f -> f
    | AppTy (x, tvs, tas) -> AppTy (x, tvs, List.map (subst_tyarg s) tas)
    | CastExp (x, u1, u2, r_p) -> CastExp (x, subst_type s u1, subst_type s u2, r_p)
    | CoercionExp c -> CoercionExp (subst_coercion ~monotonic s c)
    | LetExp (x, f1, f2) ->
      LetExp (x, subst_exp ~monotonic s f1, subst_exp ~monotonic s f2)
    | LetFunExp (x, tvs, fd, f) ->
      LetFunExp (x, tvs, subst_fd ~monotonic s fd, subst_exp ~monotonic s f)
  and subst_fd ~monotonic s = function
    | FunB (arg, f) -> FunB (arg, subst_exp ~monotonic s f)
    | FunS (arg, f) -> FunS (arg, subst_exp ~monotonic s f)
    | FunDual (arg, (f, f')) -> FunDual (arg, (subst_exp ~monotonic s f, subst_exp ~monotonic s f'))
    | FunTy f -> FunTy (subst_exp ~monotonic s f)
end