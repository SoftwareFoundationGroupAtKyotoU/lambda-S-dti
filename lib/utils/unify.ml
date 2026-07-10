open Syntax
open Type_utils
open Format
open Ftv
open Pp

exception Unify_error of string

let rec unify = function
  (* CConsistent (U, U) *)
  (* When tyvar is already instantiated *)
  | CConsistent (TyVar (_, { contents = Some u1 }), u2)
  | CConsistent (u1, TyVar (_, { contents = Some u2 })) ->
    unify @@ CConsistent (u1, u2)
  (* iota ~ iota *)
  | CConsistent (u1, u2) when u1 = u2 && is_base_type u1 -> ()
  (* X ~ X *)
  | CConsistent (TyVar (a1, {contents = None}), TyVar (a2, {contents = None})) when a1 = a2 -> ()
  (* ? ~ U or U ~ ? *)
  | CConsistent (TyDyn, _) | CConsistent (_, TyDyn) -> ()
  (* U11->U12 ~ U21->U22 *)
  | CConsistent (TyFun (u11, u12), TyFun (u21, u22)) ->
    unify @@ CConsistent (u11, u21);
    unify @@ CConsistent (u12, u22)
  (* U1->U2 ~ X or X ~ U1->U2 *)
  | CConsistent (TyFun (u1, u2), TyVar x) | CConsistent (TyVar x, TyFun (u1, u2)) as c ->
    if TV.mem x (ftv_ty (TyFun (u1, u2))) then raise @@ Unify_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
    else let x1, x2 = fresh_tyvar (), fresh_tyvar () in
    unify @@ CEqual (TyVar x, TyFun (x1, x2));
    unify @@ CConsistent (x1, u1);
    unify @@ CConsistent (x2, u2)
  (* U1 list ~ U2 list *)
  | CConsistent (TyList u1, TyList u2) -> 
    unify @@ CConsistent (u1, u2)
  (* U list ~ X or X ~ U list *)
  | CConsistent (TyList u, TyVar x) | CConsistent (TyVar x, TyList u) as c ->
    if TV.mem x (ftv_ty (TyList u)) then raise @@ Unify_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
    else let y = fresh_tyvar () in
    unify @@ CEqual (TyVar x, TyList y);
    unify @@ CConsistent (y, u)
  (* (U11,...,U1n) ~ (U21,...,U2m) *)
  | CConsistent (TyTuple us1, TyTuple us2) as c ->
    begin try 
      List.iter2 (fun u1 u2 -> unify @@ CConsistent (u1, u2)) us1 us2
    with
      Invalid_argument _ -> raise @@ Unify_error (asprintf "cannot solve a constraint because of the difference of the tuple length: %a" pp_constr c)
    end
  (* (U1,...,Un) ~ X or X ~ (U1,...,Un) *)
  | CConsistent (TyTuple us, TyVar x) | CConsistent (TyVar x, TyTuple us) as c ->
    if TV.mem x (ftv_ty (TyTuple us)) then raise @@ Unify_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
    else 
      let ys = List.map (fun _ -> fresh_tyvar ()) us in
      unify @@ CEqual (TyVar x, TyTuple ys);
      List.iter2 (fun y u -> unify @@ CConsistent (y, u)) ys us
  (* U1 ref ~ U2 ref *)
  | CConsistent (TyRef u1, TyRef u2) -> 
    unify @@ CConsistent (u1, u2)
  (* U ref ~ X or X ~ U ref *)
  | CConsistent (TyRef u, TyVar x) | CConsistent (TyVar x, TyRef u) as c ->
    if TV.mem x (ftv_ty (TyRef u)) then raise @@ Unify_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
    else let y = fresh_tyvar () in
    unify @@ CEqual (TyVar x, TyRef y);
    unify @@ CConsistent (y, u)
  (* U ~ X or X ~ U *)
  | CConsistent (u, TyVar x) | CConsistent (TyVar x, u) ->
    unify @@ CEqual (TyVar x, u)
  (* CEqual (T, T) *)
  (* When tyvar is already instantiated *)
  | CEqual (TyVar (_, { contents = Some u1 }), u2)
  | CEqual (u1, TyVar (_, { contents = Some u2 })) ->
    unify @@ CEqual (u1, u2)
  (* CEqual can be used only for static types *)
  | CEqual (u1, u2) as c when not (is_static_type u1 && is_static_type u2) ->
    raise @@ Unify_error (asprintf "invalid constraint: %a" pp_constr c)
  (* ioType_bugta = iota *)
  | CEqual (TyInt, TyInt) | CEqual (TyBool, TyBool) | CEqual (TyUnit, TyUnit) (*when t1 = t2 && is_base_type t1 *) -> ()
  (* X = X *)
  | CEqual (TyVar (a1, _), TyVar (a2, _)) when a1 = a2 -> ()
  (* T11->T12 = T21->T22 *)
  | CEqual (TyFun (t11, t12), TyFun (t21, t22)) ->
    unify @@ CEqual (t11, t21);
    unify @@ CEqual (t12, t22)
  (* [T1] = [T2] *)
  | CEqual (TyList t1, TyList t2) ->
    unify @@ CEqual (t1, t2)
  (* (U11,...,U1n) = (U21,...,U2n) *)
  | CEqual (TyTuple ts1, TyTuple ts2) as c ->
    begin try 
      List.iter2 (fun t1 t2 -> unify @@ CEqual (t1, t2)) ts1 ts2
    with
      Invalid_argument _ -> raise @@ Unify_error (asprintf "cannot solve a constraint because of the difference of the tuple length: %a" pp_constr c)
    end
  (* T = X or X = T *)
  | CEqual (t, TyVar (_, tref as tv)) (*when not (is_tyvar t)*) | CEqual (TyVar (_, tref as tv), t) as c ->
    if TV.mem tv (ftv_ty t) then raise @@ Unify_error (asprintf "cannot solve a constraint because of occurance: %a" pp_constr c)
    (* else if not @@ is_static_type t then raise @@ Unify_error "unify: constraint is ill-formed" *)
    else tref := Some t
  | _ as c ->
    raise @@ Unify_error (asprintf "cannot solve a constraint: %a" pp_constr c)

let rec unify_dom = function
  | TyVar (_, { contents = Some u }) -> unify_dom u
  | TyVar (_, ({ contents = None } as tv)) ->
    let u1, u2 = fresh_tyvar (), fresh_tyvar () in
    tv := Some (TyFun (u1, u2));
    u1
  | TyFun (u1, _) -> u1
  | TyDyn -> TyDyn
  | _ as u -> raise @@ Unify_error (asprintf "failed to match: dom(%a)" pp_ty u)

let rec unify_cod = function
  | TyVar (_, { contents = Some u }) -> unify_cod u
  | TyVar (_, ({ contents = None } as tv)) ->
    let u1, u2 = fresh_tyvar (), fresh_tyvar () in
    tv := Some (TyFun (u1, u2));
    u2
  | TyFun (_, u2) -> u2
  | TyDyn -> TyDyn
  | _ as u -> raise @@ Unify_error (asprintf "failed to match: cod(%a)" pp_ty u)

let rec unify_lelm = function
  | TyVar (_, { contents = Some u }) -> unify_lelm u
  | TyVar (_, ({ contents = None } as tv)) ->
    let u = fresh_tyvar () in
    tv := Some (TyList u);
    u
  | TyList u -> u
  | TyDyn -> TyDyn
  | _ as u -> raise @@ Unify_error (asprintf "failed to match: elm(%a)" pp_ty u)

let rec unify_telm n = function
  | TyVar (_, { contents = Some u }) -> unify_telm n u
  | TyVar (_, ({ contents = None } as tv)) ->
    let us = List.init n (fun _ -> fresh_tyvar ()) in
    tv := Some (TyTuple us);
    us
  | TyTuple us when List.length us = n -> us
  | TyDyn -> List.init n (fun _ -> TyDyn)
  | _ as u -> raise @@ Unify_error (asprintf "failed to match: elm(%a)" pp_ty u)

let rec unify_cont = function
  | TyVar (_, { contents = Some u }) -> unify_cont u
  | TyVar (_, ({ contents = None } as tv)) ->
    let u = fresh_tyvar () in
    tv := Some (TyRef u);
    u
  | TyRef u -> u
  | TyDyn -> TyDyn
  | _ as u -> raise @@ Unify_error (asprintf "failed to match: cont(%a)" pp_ty u)

let rec unify_meet u1 u2 = match u1, u2 with
  | TyVar (_, { contents = Some u1 }), u2
  | u1, TyVar (_, { contents = Some u2 }) ->
    unify_meet u1 u2
  | TyBool, TyBool -> TyBool
  | TyInt, TyInt -> TyInt
  | TyUnit, TyUnit -> TyUnit
  | TyDyn, u | u, TyDyn ->
    unify @@ CConsistent (u, TyDyn);
    u
  | TyVar tv, u | u, TyVar tv ->
    unify @@ CConsistent (u, TyVar tv);
    TyVar tv
  | TyFun (u11, u12), TyFun (u21, u22) ->
    let u1 = unify_meet u11 u21 in
    let u2 = unify_meet u12 u22 in
    TyFun (u1, u2)
  | TyList u1, TyList u2 ->
    TyList (unify_meet u1 u2)
  | TyTuple us1, TyTuple us2 ->
    TyTuple (List.map2 (fun u1 u2 -> unify_meet u1 u2) us1 us2)
  | TyRef u1, TyRef u2 -> TyRef (unify_meet u1 u2)
  | u1, u2 -> raise @@ Unify_error (asprintf "failed to generate constraints: meet(%a, %a)" pp_ty u1 pp_ty u2)