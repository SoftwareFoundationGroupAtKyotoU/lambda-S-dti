open Syntax
open Ftv

let rec tv_matchform : matchform -> TV.t = function
  | MatchILit _ | MatchBLit _ | MatchULit | MatchWild | MatchNil | MatchVar _ -> TV.empty
  (* | MatchAsc (mf, u) -> TV.union (tv_matchform mf) (ftv_ty u) *)
  | MatchCons (mf1, mf2) -> TV.union (tv_matchform mf1) (tv_matchform mf2)
  | MatchTuple mfs -> TV.big_union (List.map tv_matchform mfs)

module ITGL = struct
  open Syntax.ITGL
  
  (* for polymorphic let declaration *)
  let rec tv_exp: exp -> TV.t = function
    | Var _
    | IConst _
    | BConst _
    | UConst _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | AscExp (_, e, u) -> TV.union (tv_exp e) (ftv_ty u)
    | IfExp (_, e1, e2, e3) -> TV.big_union @@ List.map tv_exp [e1; e2; e3]
    | FunExp (_, (_, _, u), e) -> TV.union (ftv_ty u) (tv_exp e)
    | FixExp (_, _, (_, _, u1), _, e) -> TV.union (ftv_ty u1) (tv_exp e)
    | AppExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | MatchExp (_, e, ms) -> TV.union (tv_exp e) (TV.big_union @@ List.map (fun (mf, e) -> TV.union (tv_matchform mf) (tv_exp e)) ms)
    | LetExp (_, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | NilExp (_, u) -> ftv_ty u
    | ConsExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | TupleExp (_, es) -> TV.big_union (List.map tv_exp es)
    | RefExp (_, e) -> tv_exp e
    | DerefExp (_, e) -> tv_exp e
    | SubstExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | MakeArrayExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | GetExp (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | PutExp (_, e1, e2, e3) -> TV.big_union @@ List.map tv_exp [e1; e2; e3]
    | LengthExp (_, e) -> tv_exp e
end