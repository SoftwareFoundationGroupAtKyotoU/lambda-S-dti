open Syntax
open Type_utils

exception Normalize_bug of string

(* Normalize type variables *)

let rec normalize_type = function
  | TyVar (_, { contents = Some u }) -> normalize_type u
  | TyFun (u1, u2) -> TyFun (normalize_type u1, normalize_type u2)
  | TyList u -> TyList (normalize_type u)
  | TyTuple us -> TyTuple (List.map (fun u -> normalize_type u) us)
  | TyRef u -> TyRef (normalize_type u)
  | _ as u -> u

let normalize_tyenv =
  Environment.map @@ fun (TyScheme (xs, u)) -> TyScheme (xs, normalize_type u)

let rec normalize_matchform = function
  | MatchILit _ | MatchBLit _ | MatchULit | MatchWild | MatchVar _ | MatchNil as mf -> mf
  | MatchCons (mf1, mf2) -> MatchCons (normalize_matchform mf1, normalize_matchform mf2)
  | MatchTuple mfs -> MatchTuple (List.map (fun mf -> normalize_matchform mf) mfs)
  (* | MatchAsc (mf, u) -> MatchAsc (normalize_matchform mf, normalize_type u) *)

module ITGL = struct
  open Syntax.ITGL

  let rec normalize_exp = function
    | Var (r, x, ys) -> Var (r, x, ref @@ List.map normalize_type !ys)
    | IConst _
    | BConst _
    | UConst _ as e -> e
    | BinOp (r, op, e1, e2) ->
      BinOp (r, op, normalize_exp e1, normalize_exp e2)
    | AscExp (r, e, u) ->
      AscExp (r, normalize_exp e, normalize_type u)
    | IfExp (r, e1, e2, e3) ->
      IfExp (r, normalize_exp e1, normalize_exp e2, normalize_exp e3)
    | FunExp (r, (x1, anot, u1), e) ->
      FunExp (r, (x1, anot, normalize_type u1), normalize_exp e)
    | FixExp (r, x, (y, anot, u1), u2, e) ->
      FixExp (r, x, (y, anot, normalize_type u1), normalize_type u2, normalize_exp e)
    | AppExp (r, e1, e2) ->
      AppExp (r, normalize_exp e1, normalize_exp e2)
    | MatchExp (r, e, ms) ->
      MatchExp (r, normalize_exp e, List.map (fun (mf, e) -> normalize_matchform mf, normalize_exp e) ms)
    | LetExp (r, y, e1, e2) ->
      LetExp (r, y, normalize_exp e1, normalize_exp e2)
    | NilExp (r, u) -> NilExp (r, normalize_type u)
    | ConsExp (r, e1, e2) -> ConsExp (r, normalize_exp e1, normalize_exp e2)
    | TupleExp (r, es) -> TupleExp (r, List.map (fun e -> normalize_exp e) es)
    | RefExp (r, e) -> RefExp (r, normalize_exp e)
    | DerefExp (r, e) -> DerefExp (r, normalize_exp e)
    | SubstExp (r, e1, e2) -> SubstExp (r, normalize_exp e1, normalize_exp e2)
    (* | _ -> raise @@ Type_bug "yet" *)

  let normalize_program = function
    | Exp e -> Exp (normalize_exp e)
    | LetDecl (x, e) -> LetDecl (x, normalize_exp e)

  let normalize env p u =
    normalize_tyenv env,
    normalize_program p,
    normalize_type u
end

(* in CC *)

let rec make_static_proj_coercion ~monotonic u (r, p) = match normalize_type u with
  | TyInt | TyBool | TyUnit as g -> CSeq (CProj (tag_of_ty g, (r, p)), CId g)
  | TyFun (u1, u2) -> CSeq (CProj (Fn, (r, p)), CFun (make_static_inj_coercion ~monotonic u1 (r, neg p), make_static_proj_coercion ~monotonic u2 (r, p)))
  | TyList u -> CSeq (CProj (Li, (r, p)), CList (make_static_proj_coercion ~monotonic u (r, p)))
  | TyTuple us ->
    let n = List.length us in
    CSeq (CProj (Tp n, (r, p)), CTuple (List.map (fun u -> make_static_proj_coercion ~monotonic u (r, p)) us))
  | TyRef u ->
    if monotonic then CSeq (CProj (Rf, (r, p)), CMRef (u, TyDyn))
    else CSeq (CProj (Rf, (r, p)), CRef (make_static_proj_coercion ~monotonic u (r, p), make_static_inj_coercion ~monotonic u (r, p)))
  | TyVar tv -> CTvProj (tv, (r, p))
  | TyCoercion _ -> raise @@ Normalize_bug "static_proj: TyCoercion is inserted"
  | TyDyn -> raise @@ Normalize_bug "static_proj: not static"
and make_static_inj_coercion ~monotonic u (r, p) = match normalize_type u with
  | TyInt | TyBool | TyUnit as g -> CSeq (CId g, CInj (tag_of_ty g))
  | TyFun (u1, u2) -> CSeq (CFun (make_static_proj_coercion ~monotonic u1 (r, neg p), make_static_inj_coercion ~monotonic u2 (r, p)), CInj Fn)
  | TyList u -> CSeq (CList (make_static_inj_coercion ~monotonic u (r, p)), CInj Li)
  | TyTuple us ->
    let n = List.length us in
    CSeq (CTuple (List.map (fun u -> make_static_inj_coercion ~monotonic u (r, p)) us), CInj (Tp n))
  | TyRef u ->
    if monotonic then CSeq (CMRef (u, TyDyn), CInj Rf)
    else CSeq (CRef (make_static_proj_coercion ~monotonic u (r, p), make_static_inj_coercion ~monotonic u (r, p)), CInj Rf)
  | TyVar tv -> CTvInj (tv, (r, p))
  | TyCoercion _ -> raise @@ Normalize_bug "static_inj: TyCoercion is inserted"
  | TyDyn -> raise @@ Normalize_bug "static_inj: not static"

let rec make_static_projinj_coercion ~monotonic (r1, p1) u (r2, p2) = match u with
  | TyInt | TyBool | TyUnit as g -> CSeq (CProj (tag_of_ty g, (r1, p1)), CSeq (CId g, CInj (tag_of_ty g)))
  | TyFun (u1, u2) ->
    let c1 = make_static_projinj_coercion ~monotonic (r2, neg p2) u1 (r1, neg p1) in
    let c2 = make_static_projinj_coercion ~monotonic (r1, p1) u2 (r2, p2) in
    CSeq (CProj (Fn, (r1, p1)), CSeq (CFun (c1, c2), CInj Fn))
  | TyList u ->
    let c = make_static_projinj_coercion ~monotonic (r1, p1) u (r2, p2) in
    CSeq (CProj (Li, (r1, p1)), CSeq (CList c, CInj Li))
  | TyTuple us ->
    let n = List.length us in
    let cs = List.map (fun u -> make_static_projinj_coercion ~monotonic (r1, p1) u (r2, p2)) us in
    CSeq (CProj (Tp n, (r1, p1)), CSeq (CTuple cs, CInj (Tp n)))
  | TyRef u ->
    let c = 
      if monotonic then CMRef (TyDyn, u)
      else
        let c1 = make_static_projinj_coercion ~monotonic (r1, p1) u (r2, p2) in
        let c2 = make_static_projinj_coercion ~monotonic (r2, neg p2) u (r1, neg p1) in
        CRef (c1, c2)
    in
      CSeq (CProj (Rf, (r1, p1)), CSeq (c, CInj Rf))
  | TyVar tv -> CTvProjInj (tv, (r1, p1), (r2, p2))
  | TyCoercion _ -> raise @@ Normalize_bug "static_projinj: TyCoercion is inserted"
  | TyDyn -> raise @@ Normalize_bug "static_projinj: not static"

let rec normalize_coercion ~monotonic c = match c with
  | CId TyDyn -> c
  | CSeq (CProj _ as c1, c2) -> CSeq (c1, normalize_coercion ~monotonic c2)
  | CTvProj ((_, { contents = Some u }), r_p) ->
    make_static_proj_coercion ~monotonic u r_p
  | CTvProj ((_, { contents = None }), _) -> c
  | CTvInj ((_, { contents = Some u }), r_p) ->
    make_static_inj_coercion ~monotonic u r_p
  | CTvInj ((_, { contents = None }), _) -> c
  | CTvProjInj ((_, { contents = Some u }), r_p1, r_p2) ->
    make_static_projinj_coercion ~monotonic r_p1 u r_p2
  | CTvProjInj ((_, { contents = None }), _, _) -> c
  | CSeq (c1, (CInj _ as c2)) -> CSeq (normalize_coercion ~monotonic c1, c2)
  | CFail _ as c -> c
  | CId u -> CId (normalize_type u)
  | CFun (s, t) ->
    let s' = normalize_coercion ~monotonic s in
    let t' = normalize_coercion ~monotonic t in
    begin match s', t' with
      | CId u1, CId u2 -> CId (TyFun (u1, u2))
      | _ -> CFun (s', t')
    end
  | CList s ->
    let s' = normalize_coercion ~monotonic s in
    begin match s' with
      | CId u -> CId (TyList u)
      | _ -> CList s'
    end
  | CTuple ss ->
    let rec check_id l r = match l with
    | CId u :: t -> check_id t (u :: r)
    | _ :: _ -> (false, r) (* r is dummy *)
    | [] -> (true, List.rev r)
    in
    let (is_id, id_u) = check_id ss [] in
    if is_id then CId (TyTuple id_u)
    else CTuple ss
  | CRef (c1, c2) ->
    let c1 = normalize_coercion ~monotonic c1 in
    let c2 = normalize_coercion ~monotonic c2 in
    begin match c1, c2 with
    | CId u, CId _ -> CId (TyRef u)
    | _ -> CRef (c1, c2)
    end
  | CMRef (u1, u2) -> CMRef (normalize_type u1, normalize_type u2)
  | c -> raise @@ Normalize_bug (Format.asprintf "cannot normalize coercion: %a" Pp.pp_coercion c)