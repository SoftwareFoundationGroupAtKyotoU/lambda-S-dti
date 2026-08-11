open Syntax

(** Returns a set of free type variables in a given type. *)
let rec ftv_ty: ty -> TV.t = function
  | TyVar (_, { contents = None } as tv) -> TV.singleton tv
  | TyVar (_, { contents = Some u }) -> ftv_ty u
  | TyFun (u1, u2) -> TV.union (ftv_ty u1) (ftv_ty u2)
  | TyList u -> ftv_ty u
  | TyTuple us -> TV.big_union (List.map ftv_ty us)
  | TyRef u -> ftv_ty u
  | TyArray u -> ftv_ty u
  | _ -> TV.empty

let ftv_tysc: tysc -> TV.t = function
  | TyScheme (xs, u) -> TV.diff (ftv_ty u) (TV.of_list xs)
  
let ftv_tyarg = function
  | Ty ty -> ftv_ty ty
  | TyNu -> TV.empty

let ftv_tyenv (env: tysc Environment.t): TV.t =
  Environment.fold (fun _ us vars -> TV.union vars (ftv_tysc us)) env TV.empty

let rec ftv_matchform : matchform -> TV.t = function
  | MatchVar _ | MatchILit _ | MatchBLit _ | MatchULit | MatchWild -> TV.empty
  | MatchNil -> TV.empty
  (* | MatchAsc (mf, u) -> TV.union (ftv_matchform mf) (ftv_ty u) *)
  | MatchCons (mf1, mf2) -> TV.union (ftv_matchform mf1) (ftv_matchform mf2)
  | MatchTuple mfs -> TV.big_union (List.map ftv_matchform mfs)

let rec ftv_coercion = function
  | CInj _ | CProj _ -> TV.empty
  | CTvInj (tv, _) | CTvProj (tv, _) | CTvProjInj (tv, _, _) -> TV.singleton tv
  | CFun (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CList c -> ftv_coercion c
  | CTuple cs -> TV.big_union (List.map ftv_coercion cs)
  | CRef (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CMRef (u1, u2) -> TV.union (ftv_ty u1) (ftv_ty u2)
  | CArray (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CMArray (u1, u2) -> TV.union (ftv_ty u1) (ftv_ty u2)
  | CId u -> ftv_ty u
  | CSeq (c1, c2) -> TV.union (ftv_coercion c1) (ftv_coercion c2)
  | CFail _ -> TV.empty

module ITGL = struct
  open Syntax.ITGL

  let rec ftv_exp: exp -> TV.t = function
    | Var _
    | IConst _
    | FConst _
    | BConst _
    | UConst _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | AscExp (_, e, u) -> TV.union (ftv_exp e) (ftv_ty u)
    | IfExp (_, e1, e2, e3) -> TV.big_union @@ List.map ftv_exp [e1; e2; e3]
    | FunExp (_, (_, Expl, u), e) -> TV.union (ftv_ty u) (ftv_exp e)
    | FunExp (_, (_, Impl, _), e) -> ftv_exp e
    | FixExp (_, _, (_, Expl, u1), _, e) -> TV.union (ftv_ty u1) (ftv_exp e)
    | FixExp (_, _, (_, Impl, _), _, e) -> ftv_exp e
    | AppExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | MatchExp (_, e, ms) -> TV.union (ftv_exp e) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (ftv_matchform mf) (ftv_exp e)) ms)
    | LetExp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | NilExp _ -> TV.empty
    | ConsExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | TupleExp (_, es) -> TV.big_union (List.map ftv_exp es)
    | RefExp (_, e) -> ftv_exp e
    | DerefExp (_, e) -> ftv_exp e
    | SubstExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | MakeArrayExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | GetExp (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | PutExp (_, e1, e2, e3) -> TV.big_union @@ List.map ftv_exp [e1; e2; e3]
    | LengthExp (_, e) -> ftv_exp e
end

module CC = struct
  open Syntax.CC

  let rec ftv_exp: exp -> TV.t = function
    | Var (_, us) -> List.fold_right TV.union (List.map ftv_tyarg us) TV.empty
    | IConst _
    | FConst _
    | BConst _
    | UConst -> TV.empty
    | FunExp (tvs, fund) -> TV.diff (ftv_fund fund) (TV.of_list tvs)
    | FixExp (tvs, fixd) -> TV.diff (ftv_fixd fixd) (TV.of_list tvs)
    | CoercionExp c -> ftv_coercion c
    | BinOp (_, f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | IfExp (f1, f2, f3) ->
      List.fold_right TV.union (List.map ftv_exp [f1; f2; f3]) TV.empty
    | AppMExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | AppDExp (f1, (f2, f3)) -> TV.union (ftv_exp f1) (TV.union (ftv_exp f2) (ftv_exp f3))
    | LetExp (_, f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | NilExp _ -> TV.empty
    | ConsExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | MatchExp (f, ms) ->
      TV.union (ftv_exp f) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (ftv_matchform mf) (ftv_exp e)) ms)
    | TupleExp es -> TV.big_union (List.map ftv_exp es)
    | RefExp (f, u) -> TV.union (ftv_exp f) (ftv_ty u)
    | DerefExp (f, None) -> ftv_exp f
    | DerefExp (f, Some u) -> TV.union (ftv_exp f) (ftv_ty u)
    | SubstExp (f1, f2, None) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | SubstExp (f1, f2, Some u) -> TV.union (ftv_exp f1) @@ TV.union (ftv_exp f2) (ftv_ty u)
    | MakeArrayExp (f1, f2, u) -> TV.union (ftv_exp f1) @@ TV.union (ftv_exp f2) (ftv_ty u)
    | GetExp (f1, f2, None) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | GetExp (f1, f2, Some u) -> TV.union (ftv_exp f1) @@ TV.union (ftv_exp f2) (ftv_ty u)
    | PutExp (f1, f2, f3, None) -> List.fold_right TV.union (List.map ftv_exp [f1; f2; f3]) TV.empty
    | PutExp (f1, f2, f3, Some u) -> List.fold_right TV.union (List.map ftv_exp [f1; f2; f3]) (ftv_ty u)
    | LengthExp f -> ftv_exp f
    | CastExp (f, u1, u2, _) -> TV.union (ftv_exp f) @@ TV.union (ftv_ty u1) (ftv_ty u2)
    | CAppExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
    | CCompExp (f1, f2) -> TV.union (ftv_exp f1) (ftv_exp f2)
  and ftv_fund = function
    | FunB ((_, u), f) -> TV.union (ftv_ty u) (ftv_exp f)
    | FunS ((_, u), _, f) -> TV.union (ftv_ty u) (ftv_exp f)
    | FunDual ((_, u), _, (f1, f2)) -> TV.union (ftv_ty u) @@ TV.union (ftv_exp f1) (ftv_exp f2)
    | FunTy f -> ftv_exp f
  and ftv_fixd = function
    | FixB (_, (_, u1), _, f) -> TV.union (ftv_ty u1) (ftv_exp f)
    | FixS (_, (_, u1), _, (_, uk), f) -> TV.union (ftv_ty u1) @@ TV.union (ftv_ty uk) (ftv_exp f)
    | FixDual (_, (_, u1), _, (_, uk), (f1, f2)) -> TV.union (ftv_ty u1) @@ TV.union (ftv_ty uk) @@ TV.union (ftv_exp f1) (ftv_exp f2)
end