open Syntax
open Format
open Normalize
open Type_utils

exception Coercion_bug of string

let is_d = function
  | CSeq (CId _, CInj _)
  | CSeq (CFun _, CInj _)
  | CSeq (CList _, CInj _)
  | CSeq (CTuple _, CInj _)
  | CSeq (CRef _, CInj _)
  | CSeq (CMRef _, CInj _)
  | CFun _
  | CList _
  | CTuple _
  | CRef _ -> true
  | _ -> false

(* Cast insertion translation *)
let rec make_s_coercion ~monotonic u1 (r, p) u2 = match u1, u2 with
  | i1, i2 when is_base_type i1 && is_base_type i2 && i1 = i2 -> CId i1
  | TyVar (i1, {contents = None}) as t, TyVar (i2, {contents = None}) when i1 = i2 -> CId t
  | TyFun (u11, u12), TyFun (u21, u22) ->
    let s1 = make_s_coercion ~monotonic u21 (r, neg p) u11 in
    let s2 = make_s_coercion ~monotonic u12 (r, p) u22 in
    begin match s1, s2 with
    | CId u1, CId u2 -> CId (TyFun (u1, u2))
    | _ -> CFun (s1, s2)
    end
  | TyList u1, TyList u2 ->
    let s = make_s_coercion ~monotonic u1 (r, p) u2 in
    begin match s with
    | CId u -> CId (TyList u)
    | _ -> CList s
    end
  | TyTuple us1, TyTuple us2 ->
    let ss = List.map2 (fun u1 u2 -> make_s_coercion ~monotonic u1 (r, p) u2) us1 us2 in
    let rec check_id l r = match l with
    | CId u :: t -> check_id t (u :: r)
    | _ :: _ -> (false, r) (* r is dummy *)
    | [] -> (true, List.rev r)
    in
    let (is_id, id_u) = check_id ss [] in
    if is_id then CId (TyTuple id_u)
    else CTuple ss
  | TyRef u1, TyRef u2 ->
    if monotonic then
      if u1 = u2 then CId (TyRef u1)
      else CMRef (u1, u2)
    else
      let c_r = make_s_coercion ~monotonic u1 (r, p) u2 in
      let c_w = make_s_coercion ~monotonic u2 (r, neg p) u1 in
      begin match c_r, c_w with
      | CId u, CId _ -> CId (TyRef u)
      | _ -> CRef (c_r, c_w)
      end
  | TyDyn, TyDyn -> CId TyDyn
  | g, TyDyn when is_ground g -> CSeq (CId g, CInj (tag_of_ty g))
  | TyFun _ as u, TyDyn -> CSeq (make_s_coercion ~monotonic u (r, p) (TyFun (TyDyn, TyDyn)), CInj Ar)
  | TyList _ as u, TyDyn -> CSeq (make_s_coercion ~monotonic u (r, p) (TyList TyDyn), CInj Li)
  | TyTuple us as u, TyDyn ->
    let n = List.length us in
    let dtuple = TyTuple (List.map (fun _ -> TyDyn) us) in
    CSeq (make_s_coercion ~monotonic u (r, p) dtuple, CInj (Tp n))
  | TyRef _ as u, TyDyn -> CSeq (make_s_coercion ~monotonic u (r, p) (TyRef TyDyn), CInj Rf)
  | TyVar tv, TyDyn -> CTvInj (tv, (r, p))
  | TyDyn, g when is_ground g -> CSeq (CProj (tag_of_ty g, (r, p)), CId g)
  | TyDyn, (TyFun _ as u) -> CSeq (CProj (Ar, (r, p)), make_s_coercion ~monotonic (TyFun (TyDyn, TyDyn)) (r, p) u)
  | TyDyn, (TyList _ as u) -> CSeq (CProj (Li, (r, p)), make_s_coercion ~monotonic (TyList TyDyn) (r, p) u)
  | TyDyn, (TyTuple us as u) ->
    let n = List.length us in
    let dtuple = TyTuple (List.map (fun _ -> TyDyn) us) in
    CSeq (CProj (Tp n, (r, p)), make_s_coercion ~monotonic dtuple (r, p) u)
  | TyDyn, (TyRef _ as u) -> CSeq (CProj (Rf, (r, p)), make_s_coercion ~monotonic (TyRef TyDyn) (r, p) u)
  | TyDyn, TyVar tv -> CTvProj (tv, (r, p))
  | _ -> raise @@ Coercion_bug (Format.asprintf "cannot exist such coercion: %a and %a in %a" Pp.pp_ty u1 Pp.pp_ty u2 Utils.Error.pp_range r)
  
let rec compose ~(config:Config.t) c1 c2 = (* TODO : blame *)
  let debug = config.debug in
  let monotonic = config.monotonic in
  let compose = compose ~config in
  if debug then fprintf err_formatter "comp <-- %a；%a@." Pp.pp_coercion c1 Pp.pp_coercion c2;
  match normalize_coercion ~monotonic c1, normalize_coercion ~monotonic c2 with
  (* id{star} ;;; t *)
  | CId TyDyn, c2 -> c2
  (* G?p;i ;;; t *)
  | CSeq (CProj (t, p), c1), c2 -> CSeq (CProj (t, p), compose c1 c2)
  (* X?p ;;; t *)
  | CTvProj ((a1, _ as tv), p), CId (TyVar (a2, _)) when a1 = a2 -> CTvProj (tv, p)
  | CTvProj ((a1, _ as tv), p), CTvInj ((a2, _), q) when a1 = a2 -> CTvProjInj (tv, p, q)
  (* X! ;;; t *)
  | CTvInj (tv, p), CId TyDyn -> CTvInj (tv, p)
  | CTvInj ((_, uref as tv), (r, p)), CSeq (CProj (Ar, _), c2) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyFun (x1, x2));
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose (CFun (CTvProj (tv1, (r, neg p)), (CTvInj (tv2, (r, p))))) c2
      | _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    end
  | CTvInj ((_, uref as tv), p), CSeq (CProj (Li, _), c2) ->
    let x1 = fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyList x1);
    uref := Some (TyList x1);
    begin match x1 with
      | TyVar tv1 ->
        compose (CList (CTvInj (tv1, p))) c2
      | _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    end
  | CTvInj ((_, uref as tv), p), CSeq (CProj ((Tp n), _), c2) ->
    let xs = List.init n (fun _ -> fresh_tyvar ()) in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyTuple xs);
    uref := Some (TyTuple xs);
    let rec make_c1 l r = match l with
    | TyVar tv :: t -> 
      make_c1 t (CTvInj (tv, p) :: r)
    | _ :: _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    | [] -> CTuple (List.rev r)
    in
    compose (make_c1 xs []) c2
  | CTvInj ((_, uref as tv), (r, p)), CSeq (CProj (Rf, _), c2) ->
    let x1 = fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyRef x1);
    uref := Some (TyRef x1);
    begin match x1 with
      | TyVar tv1 ->
        if config.monotonic then compose (CMRef (x1, TyDyn)) c2
        else compose (CRef (CTvInj (tv1, (r, p)), CTvProj (tv1, (r, neg p)))) c2
      | _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    end
  | CTvInj ((_, uref as tv), _), CSeq (CProj (t, _), c2) -> 
    let u = type_of_tag t in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty u;
    uref := Some u;
    compose (CId u) c2
  | CTvInj ((a1, uref as tv1), _), CTvProj ((a2, _ as tv2), _) -> 
    if a1 = a2 then CId (TyVar tv1)
    else begin 
      if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv1) Pp.pp_ty (TyVar tv2);
      uref := Some (TyVar tv2); 
      CId (TyVar tv2)
    end
  | CTvInj (tv1, p), CTvProjInj (tv2, q, r) ->
    compose (compose (CTvInj (tv1, p)) (CTvProj (tv2, q))) (CTvInj (tv2, r))
    (* if a1 = a2 then CTvInj tv1
    else (uref := Some (TyVar tv2); CTvInj tv2) *)
  (* ?pX! ;;; t *)
  | CTvProjInj (tv, p, q), c2 ->
    compose (CTvProj (tv, p)) (compose (CTvInj (tv, q)) c2)
  (* | CTvProjInj (tv, p), CId TyDyn -> CTvProjInj (tv, p)
  | CTvProjInj ((_, uref), p), CSeq (CProj (Ar, (r', q)), c2) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
    | TyVar tv1, TyVar tv2 ->
      compose (CSeq (CProj (Ar, p), CFun (CTvProjInj (tv1, (r', neg q)), CTvProjInj (tv2, p)))) c2
    | _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    end
  | CTvProjInj ((_, uref), p), CSeq (CProj (t, _), c2) -> 
    uref := Some (type_of_tag t);
    compose (CSeq (CProj (t, p), CId (type_of_tag t))) c2
  | CTvProjInj ((a1, uref as tv1), p), CTvProj ((a2, _ as tv2), _) -> 
    if a1 = a2 then CTvProj (tv1, p)
    else (uref := Some (TyVar tv2); CTvProj (tv2, p))
  | CTvProjInj ((a1, uref as tv1), p), CTvProjInj ((a2, _ as tv2), _) ->
    if a1 = a2 then CTvProjInj (tv1, p)
    else (uref := Some (TyVar tv2); CTvProjInj (tv2, p)) *)
  (* i ;;; t *)
  | CSeq (_, CInj _) as c1, CId TyDyn -> c1
  | CSeq (c1, CInj t), CSeq (CProj (t', p), c2) ->
    if t = t' then compose c1 c2 
    else CFail (t, p, t')
  | CSeq (c1, CInj Ar), CTvProj ((_, uref as tv), (r, p)) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyFun (x1, x2));
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose c1 (CFun (CTvInj (tv1, (r, neg p)), CTvProj (tv2, (r, p))))
      | _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj Li), CTvProj ((_, uref as tv), p) ->
    let x1 = fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyList x1);
    uref := Some (TyList x1);
    begin match x1 with
      | TyVar tv1 ->
        compose c1 (CList (CTvProj (tv1, p)))
      | _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj (Tp n)), CTvProj ((_, uref as tv), p) ->
    let xs = List.init n (fun _ -> fresh_tyvar ()) in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyTuple xs);
    uref := Some (TyTuple xs);
    let rec make_c2 l r = match l with
    | TyVar tv :: t -> 
      make_c2 t (CTvProj (tv, p) :: r)
    | _ :: _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    | [] -> CTuple (List.rev r)
    in
    compose c1 (make_c2 xs [])
  | CSeq (c1, CInj Rf), CTvProj ((_, uref as tv), (r, p)) ->
    let x1 = fresh_tyvar () in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty (TyRef x1);
    uref := Some (TyRef x1);
    begin match x1 with
      | TyVar tv1 ->
        if config.monotonic then compose c1 (CMRef (TyDyn, x1))
        else compose c1 (CRef (CTvProj (tv1, (r, p)), CTvInj (tv1, (r, neg p))))
      | _ -> raise @@ Coercion_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj t), CTvProj ((_, uref as tv), _) ->
    let u = type_of_tag t in
    if debug then fprintf err_formatter "DTI: %a is instantiated to %a@." Pp.pp_ty (TyVar tv) Pp.pp_ty u;
    uref := Some u;
    compose c1 (CId u)
  | CSeq (_, (CInj _)) as c1, CTvProjInj (tv, p, q) ->
    compose (compose c1 (CTvProj (tv, p))) (CTvInj (tv, q))
  (* | CSeq (c1, CInj Ar), CTvProjInj ((_, uref), (r, p)) ->
    let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    uref := Some (TyFun (x1, x2));
    begin match x1, x2 with
      | TyVar tv1, TyVar tv2 ->
        compose c1 (CSeq (CFun (CTvProjInj (tv1, (r, neg p)), CTvProjInj (tv2, (r, p))), CInj Ar))
      | _ -> raise @@ Eval_bug "compose: unexpected type of coercion"
    end
  | CSeq (c1, CInj t), CTvProjInj ((_, uref), _) ->
    uref := Some (type_of_tag t);
    compose c1 (CSeq (CId (type_of_tag t), CInj t)) *)
  | CFail _ as c1, _ -> c1
  (* g ;;; i *)
  | _, (CFail _ as c2) (*when is_g c1*) -> c2
  | c1, CSeq (c2, CInj t) (*when is_g c1*) -> CSeq (compose c1 c2, CInj t)
  (* g ;;; g *)
  | CId _, c2 -> c2
  | c1, CId _ -> c1
  | CFun (s, t), CFun (s', t') ->
    let c1 = compose s' s in
    let c2 = compose t t' in
    begin match c1, c2 with
      | CId u1, CId u2 -> CId (TyFun (u1, u2))
      | _ -> CFun (c1, c2) 
    end
  | CList s, CList s' ->
    let c = compose s s' in
    begin match c with
      | CId u -> CId (TyList u)
      | _ -> CList c
    end
  | CTuple ss1, CTuple ss2 ->
    let ss = List.map2 (fun s1 s2 -> compose s1 s2) ss1 ss2 in
    let rec check_id l r = match l with
    | CId u :: t -> check_id t (u :: r)
    | _ :: _ -> (false, r) (* r is dummy *)
    | [] -> (true, List.rev r)
    in
    let (is_id, id_u) = check_id ss [] in
    if is_id then CId (TyTuple id_u)
    else CTuple ss
  | CRef (c_r1, c_w1), CRef (c_r2, c_w2) ->
    let c_r = compose c_r1 c_r2 in
    let c_w = compose c_w2 c_w1 in
    begin match c_r, c_w with
    | CId u, CId _ -> CId (TyRef u)
    | _ -> CRef (c_r, c_w)
    end
  | CMRef (u11, u12), CMRef (u21, u22) ->
    begin try
      let u1 = Typing.ITGL.type_of_meet u11 u21 in
      let u2 = Typing.ITGL.type_of_meet u12 u22 in
      CMRef (u1, u2)
    with Typing.Type_error _ -> CFail (Rf, (Utils.Error.dummy_range, Pos), Rf) end (* TODO *)
  | _ -> raise @@ Coercion_bug "cannot compose coercions"