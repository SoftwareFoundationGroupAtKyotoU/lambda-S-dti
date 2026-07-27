open Syntax
open Syntax.Cls
open Utils.Error
open Ftv

exception Static_manage_bug of string

module type MANAGER_ARG = sig
  type t
  val compare : t -> t -> int
  val prefix : string
end

module Manager (K : MANAGER_ARG) = struct
  module Static = Map.Make (struct type t = K.t let compare = K.compare end)

  type state = {
    counter : int;
    cache : string Static.t;
  }

  let current_state = ref {
    counter = 0;
    cache = Static.empty;
  }

  let register a =
    if not (Static.mem a !current_state.cache) then
      let name = Printf.sprintf "%s%d" K.prefix !current_state.counter in
      let c = !current_state.counter + 1 in
      current_state := {
        counter = c;
        cache = Static.add a name !current_state.cache;
      }

  let find a = Static.find a !current_state.cache
  let mem a = Static.mem a !current_state.cache
  let get_definitions () = Static.bindings !current_state.cache
end

module TyManager = Manager (struct
  type t = ty
  let compare = compare
  let prefix = "ty"
end)

module RangeManager = Manager (struct
  type t = range
  let compare = compare
  let prefix = ""
end)

module CrcManager = Manager (struct
  type t = coercion
  let compare = compare
  let prefix = "crc"
end)

let rec exist_tv l1 l2 = match l2 with
  | h :: t -> if List.mem h l1 then true else exist_tv l1 t
  | [] -> false
  
let rec ty_tv tvs u = match u with
  | TyInt | TyBool | TyUnit | TyDyn | TyFun (TyDyn, TyDyn) | TyList TyDyn | TyRef TyDyn | TyArray TyDyn as u -> (u, fun x -> x)
  | TyTuple us when List.fold_left (fun b u -> b && if u = TyDyn then true else false) true us -> TyManager.register u; (u, fun x -> x)
  | TyVar tv -> if not (List.mem tv tvs) then (TyManager.register u; (u, fun x -> x)) else (u, fun x -> x)
  | TyFun (u1, u2) ->
    let u1, ufun1 = ty_tv tvs u1 in
    let u2, ufun2 = ty_tv tvs u2 in
    if not (exist_tv (TV.elements (ftv_ty u1)) tvs) && not (exist_tv (TV.elements (ftv_ty u2)) tvs) then begin
      TyManager.register u;
      (u, fun x -> x)
    end else 
      let newu = Type_utils.fresh_tyvar () in
      let newtv = match newu with
      | TyVar (i, u) -> u := Some (TyFun (u1, u2)); (i, u)
      | _ -> raise @@ Static_manage_bug "not tyvar was created"
      in
      (newu, fun x -> ufun1 (ufun2 (SetTy (newtv, x))))
  | TyList u' -> 
    let u', ufun' = ty_tv tvs u' in
    if not (exist_tv (TV.elements (ftv_ty u)) tvs) then begin
      TyManager.register u;
      (u, fun x -> x)
    end else
      let newu = Type_utils.fresh_tyvar () in
      let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyList u'); (i, u)
        | _ -> raise @@ Static_manage_bug "not tyvar was created"
      in
      (newu, fun x -> ufun' (SetTy (newtv, x)))
  | TyTuple us ->
    let us, ufuns = List.split @@ List.map (fun u -> ty_tv tvs u) us in
    if not @@ List.fold_left (fun b u -> b || exist_tv (TV.elements (ftv_ty u)) tvs) false us then begin
      TyManager.register u;
      (u, fun x -> x)
    end else
      let newu = Type_utils.fresh_tyvar () in
      let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyTuple us); (i, u)
        | _ -> raise @@ Static_manage_bug "not tyvar was created"
      in
      (newu, fun x -> List.fold_left (fun x ufun -> ufun x) (SetTy (newtv, x)) (List.rev ufuns))
  | TyRef u' ->
    let u', ufun' = ty_tv tvs u' in
    if not (exist_tv (TV.elements (ftv_ty u)) tvs) then begin
      TyManager.register u;
      (u, fun x -> x)
    end else
      let newu = Type_utils.fresh_tyvar () in
      let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyRef u'); (i, u)
        | _ -> raise @@ Static_manage_bug "not tyvar was created"
      in
      (newu, fun x -> ufun' (SetTy (newtv, x)))
  | TyArray u' ->
    let u', ufun' = ty_tv tvs u' in
    if not (exist_tv (TV.elements (ftv_ty u)) tvs) then begin
      TyManager.register u;
      (u, fun x -> x)
    end else
      let newu = Type_utils.fresh_tyvar () in
      let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyArray u'); (i, u)
        | _ -> raise @@ Static_manage_bug "not tyvar was created"
      in
      (newu, fun x -> ufun' (SetTy (newtv, x)))
  | TyCoercion _ -> raise @@ Static_manage_bug "yet"

let ta_tv tvs = function
  | Ty u -> let (u, f) = ty_tv tvs u in (Ty u, f)
  | TyNu -> (TyNu, fun x -> x)

let rec static_crc tvs c = 
  let is_defined c = 
    let cached = CrcManager.mem c in
    let constant = match c with
    | CId _
    | CSeq (CId _, CInj I) 
    | CSeq (CId _, CInj B) 
    | CSeq (CId _, CInj U) 
    | CSeq (CId _, CInj Fn) 
    | CSeq (CId _, CInj Li) -> true
    | CSeq (CId _, CInj (Tp _)) -> false
    | CSeq (CId _, CInj Rf)
    | CSeq (CMRef (_, TyDyn), CInj Rf)
    | CSeq (CId _, CInj Ar)
    | CSeq (CMArray (_, TyDyn), CInj Ar) -> true
    | _ -> false
    in
    cached || constant
  in
  match c with
  | CId _ -> c, fun x -> x
  | CSeq (CProj (g, (r, p)), c') ->
    RangeManager.register r;
    let c', f = static_crc tvs c' in
    let c = CSeq (CProj (g, (r, p)), c') in
    if is_defined c' then CrcManager.register c;
    c, f
  | CSeq (CId _, CInj (Tp _)) ->
    CrcManager.register c; c, fun x -> x
  | CSeq (CId _, CInj _ ) -> c, fun x -> x
  | CSeq (CMRef (_, TyDyn), CInj Rf) -> c, fun x -> x
  | CSeq (CMArray (_, TyDyn), CInj Ar) -> c, fun x -> x
  | CSeq (c', CInj g) ->
    let c', f = static_crc tvs c' in
    let c = CSeq (c', CInj g) in
    if is_defined c' then CrcManager.register c;
    c, f
  | CInj _ | CProj _ | CSeq _ -> raise @@ Static_manage_bug "bad coercion"
  | CTvInj (tv, (r, _)) ->
    RangeManager.register r;
    if not (List.mem tv tvs) then begin
      TyManager.register (TyVar tv);
      CrcManager.register c
    end;
    c, fun x -> x
  | CTvProj (tv, (r, _)) ->
    RangeManager.register r;
    if not (List.mem tv tvs) then begin
      TyManager.register (TyVar tv);
      CrcManager.register c
    end;
    c, fun x -> x
  | CTvProjInj (tv, (r1, _), (r2, _)) ->
    RangeManager.register r1;
    RangeManager.register r2;
    if not (List.mem tv tvs) then begin
      TyManager.register (TyVar tv);
      CrcManager.register c
    end;
    c, fun x -> x
  | CFun (c1, c2) ->
    let c1, f1 = static_crc tvs c1 in
    let c2, f2 = static_crc tvs c2 in
    let c = CFun (c1, c2) in
    if is_defined c1 && is_defined c2 then CrcManager.register c;
    c, fun x -> f1 (f2 x)
  | CList c' ->
    let c', f = static_crc tvs c' in
    let c = CList c' in
    if is_defined c' then CrcManager.register c;
    c, f
  | CTuple cs ->
    let cs, fs = List.split @@ List.map (fun c -> static_crc tvs c) cs in
    let c = CTuple cs in
    if List.for_all (fun c -> is_defined c) cs then CrcManager.register c;
    c, fun x -> List.fold_left (fun e f -> f e) x (List.rev fs)
  | CRef (c1, c2) ->
    let c1, f1 = static_crc tvs c1 in
    let c2, f2 = static_crc tvs c2 in
    let c = CRef (c1, c2) in
    if is_defined c1 && is_defined c2 then CrcManager.register c;
    c, fun x -> f1 (f2 x)
  | CMRef (u1, u2) ->
    let u1, f1 = ty_tv tvs u1 in
    let u2, f2 = ty_tv tvs u2 in
    let c = CMRef (u1, u2) in
    let is_defined_ty = function
      | TyInt | TyBool | TyUnit | TyDyn | TyFun (TyDyn, TyDyn) | TyList TyDyn | TyRef TyDyn | TyArray TyDyn -> true
      | u -> TyManager.mem u
    in
    if is_defined_ty u1 && is_defined_ty u2 then CrcManager.register c;
    c, fun x -> f1 (f2 x)
  | CArray (c1, c2) ->
    let c1, f1 = static_crc tvs c1 in
    let c2, f2 = static_crc tvs c2 in
    let c = CArray (c1, c2) in
    if is_defined c1 && is_defined c2 then CrcManager.register c;
    c, fun x -> f1 (f2 x)
  | CMArray (u1, u2) ->
    let u1, f1 = ty_tv tvs u1 in
    let u2, f2 = ty_tv tvs u2 in
    let c = CMArray (u1, u2) in
    let is_defined_ty = function
      | TyInt | TyBool | TyUnit | TyDyn | TyFun (TyDyn, TyDyn) | TyList TyDyn | TyRef TyDyn | TyArray TyDyn -> true
      | u -> TyManager.mem u
    in
    if is_defined_ty u1 && is_defined_ty u2 then CrcManager.register c;
    c, fun x -> f1 (f2 x)
  | CFail _ -> raise @@ Static_manage_bug "yet"

let rec static_exp tvs = function
  | Var _ | Int _ | Nil | Add _ | Sub _ | Mul _ | Div _ | Mod _
  | Cons _ | Tuple _ | Hd _ | Tl _ | Tget _ 
  | Deref (_, None) | Subst (_, _, None)
  | Get (_, _, None) | Put (_, _, _, None)
  | AppDCls _ | AppDDir _ | AppMCls _ | AppMDir _ 
  | CApp _ | CComp _ as f -> f
  | Ref (x, u) ->
    let u, udeclfun = ty_tv tvs u in
    udeclfun (Ref (x, u))
  | Deref (x, Some u) ->
    let u, udeclfun = ty_tv tvs u in
    udeclfun (Deref (x, Some u))
  | Subst (x, y, Some u) ->
    let u, udeclfun = ty_tv tvs u in
    udeclfun (Subst (x, y, Some u))
  | MakeArray (x, y, u) ->
    let u, udeclfun = ty_tv tvs u in
    udeclfun (MakeArray (x, y, u))
  | Get (x, y, Some u) ->
    let u, udeclfun = ty_tv tvs u in
    udeclfun (Get (x, y, Some u))
  | Put (x, y, z, Some u) ->
    let u, udeclfun = ty_tv tvs u in
    udeclfun (Put (x, y, z, Some u))
  | Coercion c ->
    let c, udeclfun = static_crc tvs c in
    udeclfun (Coercion c)
  | AppTy (x, i1, tas, i2) -> 
    let uandf = List.map (ta_tv tvs) tas in
    let rec destruct_uandf l ru rf = match l with
      | (u, f) :: t -> destruct_uandf t (u::ru) (fun x -> rf (f x))
      | [] -> ru, rf 
    in
    let us, f = destruct_uandf (List.rev uandf) [] (fun x -> x) in
    f (AppTy (x, i1, us, i2))
  | AppTyFun (x, i1, tas, i2) -> 
    let uandf = List.map (ta_tv tvs) tas in
    let rec destruct_uandf l ru rf = match l with
      | (u, f) :: t -> destruct_uandf t (u::ru) (fun x -> rf (f x))
      | [] -> ru, rf 
    in
    let us, f = destruct_uandf (List.rev uandf) [] (fun x -> x) in
    f (AppTyFun (x, i1, us, i2))
  | Cast (x, u1, u2, (r, p)) ->
    let u1, udeclfun1 = ty_tv tvs u1 in 
    let u2, udeclfun2 = ty_tv tvs u2 in
    RangeManager.register r;
    udeclfun1 (udeclfun2 (Cast (x, u1, u2, (r, p))))
  | Let (x, f1, f2) ->
    let f1 = static_exp tvs f1 in
    let f2 = static_exp tvs f2 in
    Let (x, f1, f2)
  | Match (x, ms) -> Match (x, List.map (fun (mf, f) -> mf, static_exp tvs f) ms)
  | IfEq (x, y, f1, f2) -> IfEq (x, y, static_exp tvs f1, static_exp tvs f2)
  | IfLte (x, y, f1, f2) -> IfLte (x, y, static_exp tvs f1, static_exp tvs f2)
  | MakeCls (x, cls, f) -> MakeCls (x, cls, static_exp tvs f)
  | MakeTyCls (x, cls, f) -> MakeTyCls (x, cls, static_exp tvs f)
  | SetTy _ -> raise @@ Static_manage_bug "setty appear in static_exp"

let static_fundef = function
  | FundefD  { name; tvs; arg; vs; body } ->
    let body = static_exp tvs body in
    FundefD  { name; tvs; arg; vs; body }
  | FundefM  { name; tvs; arg; vs; body } -> 
    let body = static_exp tvs body in
    FundefM  { name; tvs; arg; vs; body }
  | FundefTy { name; tvs;      vs; body } ->
    let body = static_exp tvs body in
    FundefTy  { name; tvs;     vs; body }

let static_program (Prog (toplevel, p)) =
  Prog (List.map (fun fundef -> static_fundef fundef) toplevel, static_exp [] p)