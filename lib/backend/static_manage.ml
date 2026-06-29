open Syntax
open Syntax.Cls
open Utils.Error

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

  let initial_state = { counter = 0; cache = Static.empty }

  let register u state =
    if not (Static.mem u state.cache) then
      { counter = state.counter + 1;
        cache = Static.add u (Printf.sprintf "%s%d" K.prefix (state.counter + 1)) state.cache }
    else state

  let find u state = Static.find u state.cache
  let get_definitions state = Static.bindings state.cache
end

module TyManager = Manager (struct
  type t = ty
  let compare = compare
  let prefix = "ty"
end)

type static_data = {
  ty_defs : TyManager.state;
  (* range_defs : (range * int) list;
  range_to_id : range -> int;
  crc_defs : (Cls.coercion * string) list;
  crc_cached : Cls.coercion -> bool;
  crc_name : Cls.coercion -> string;
  inj_aliases : tag StringMap.t;
  proj_aliases : (tag * int * polarity) StringMap.t; *)
}

let intern_ty tvs u sd = match u with
  | TyInt | TyBool | TyUnit | TyDyn | TyFun (TyDyn, TyDyn) | TyList TyDyn -> sd
  | TyTuple us when List.for_all ((=) TyDyn) us -> sd
  | TyVar tv -> if List.mem tv tvs then sd else { (*sd with*) ty_defs = TyManager.register u sd.ty_defs }
  | _ -> raise @@ Static_manage_bug "yet"
  (* | TyFun (u1, u2) ->
    let u1, ufun1 = ty_tv tvs u1 in
    let u2, ufun2 = ty_tv tvs u2 in
    if not (exist_tv (TV.elements (ftv_ty u1)) tvs) && not (exist_tv (TV.elements (ftv_ty u2)) tvs) then begin
      TyManager.register u;
      (u, fun x -> x)
    end else 
      let newu = Type_utils.fresh_tyvar () in
      let newtv = match newu with
      | TyVar (i, u) -> u := Some (TyFun (u1, u2)); (i, u)
      | _ -> raise @@ Closure_bug "not tyvar was created"
      in
      (newu, fun x -> ufun1 (ufun2 (Cls.SetTy (newtv, x))))
  | TyList u' -> 
    let u', ufun' = ty_tv tvs u' in
    if not (exist_tv (TV.elements (ftv_ty u)) tvs) then begin
      TyManager.register u;
      (u, fun x -> x)
    end else
      let newu = Type_utils.fresh_tyvar () in
      let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyList u'); (i, u)
        | _ -> raise @@ Closure_bug "not tyvar was created"
      in
      (newu, fun x -> ufun' (Cls.SetTy (newtv, x)))
  | TyTuple us ->
    let us, ufuns = List.split @@ List.map (fun u -> ty_tv tvs u) us in
    if not @@ List.fold_left (fun b u -> b || exist_tv (TV.elements (ftv_ty u)) tvs) false us then begin
      TyManager.register u;
      (u, fun x -> x)
    end else
      let newu = Type_utils.fresh_tyvar () in
      let newtv = match newu with
        | TyVar (i, u) -> u := Some (TyTuple us); (i, u)
        | _ -> raise @@ Closure_bug "not tyvar was created"
      in
      (newu, fun x -> List.fold_left (fun x ufun -> ufun x) (Cls.SetTy (newtv, x)) (List.rev ufuns))
  | TyRef _ -> raise @@ Closure_bug "yet"
  | TyCoercion _ -> raise @@ Closure_bug "yet" *)

let rec intern_exp tvs f sd = match f with
  | Var _ | Int _ | Nil | Add _ | Sub _ | Mul _ | Div _ | Mod _ | Cons _ | Tuple _ | Hd _ | Tl _ | Tget _
  | AppDCls _ | AppDDir _ | AppMCls _ | AppMDir _ | CApp _ | CSeq _ -> sd
  | Ref _ -> raise @@ Static_manage_bug "yet"
  | Deref _ | Subst _ -> raise @@ Static_manage_bug "yet"
  | Cast (_, u1, u2, _) ->
    sd
    |> intern_ty tvs u1
    |> intern_ty tvs u2
  | AppTy _ -> raise @@ Static_manage_bug "yet"
  | AppTyFun _ -> raise @@ Static_manage_bug "yet"
  | Coercion _ -> raise @@ Static_manage_bug "yet"
  | IfEq (_, _, f1, f2) | IfLte (_, _, f1, f2) | Let (_, f1, f2) ->
    sd
    |> intern_exp tvs f1
    |> intern_exp tvs f2
  | Match _ -> raise @@ Static_manage_bug "yet"
  | MakeCls _ | MakeTyCls _ -> raise @@ Static_manage_bug "yet"
  | SetTy _ -> raise @@ Static_manage_bug "SetTy need?"

let intern_fundef fd sd = match fd with
  | FundefD { tvs = (tvs, _); body; _ } | FundefM { tvs = (tvs, _); body; _ } | FundefTy { tvs = (tvs, _); body; _ } ->
    intern_exp tvs body sd

let intern (Prog (fds, main)) =
  { ty_defs = TyManager.initial_state }
  |> (fun sd -> List.fold_left (fun sd fd -> intern_fundef fd sd) sd fds)
  |> intern_exp [] main

module RangeManager = struct
  module Range = Map.Make (struct type t = range let compare = compare end)

  type state = {
    counter : int;
    cache : int Range.t;
  }

  let current_state = ref {
    counter = -1;
    cache = Range.empty;
  }

  let clear () = 
    current_state := { counter = -1; cache = Range.empty }

  let save () = !current_state

  let restore s = 
    current_state := s

  let range_id r = 
    try
      Range.find r !current_state.cache
    with Not_found ->
      let c = !current_state.counter + 1 in
      current_state := {
        counter = c;
        cache = Range.add r c !current_state.cache;
      };
      c

  let get_definitions () = Range.bindings !current_state.cache
end

module CrcManager = struct
  module StaticCrc = Map.Make (struct type t = Cls.coercion let compare = compare end)
  module AtomInjCrc = Map.Make (struct type t = string let compare = compare end)
  module AtomProjCrc = Map.Make (struct type t = string let compare = compare end)

  type state = {
    counter : int;
    cache : string StaticCrc.t;
  }

  let current_state = ref {
    counter = 0;
    cache = StaticCrc.empty;
  }

  let current_inj = ref AtomInjCrc.empty
  let current_proj = ref AtomProjCrc.empty

  let clear () = 
    current_state := { counter = 0; cache = StaticCrc.empty };
    current_inj := AtomInjCrc.empty;
    current_proj := AtomProjCrc.empty

  let save () = !current_state, !current_inj, !current_proj

  let restore (cs, ci, cp) = 
    current_state := cs;
    current_inj := ci;
    current_proj := cp

  let register s =
    if not (StaticCrc.mem s !current_state.cache) then
      let c = !current_state.counter + 1 in
      let name = Printf.sprintf "crc%d" c in
      current_state := {
        counter = c;
        cache = StaticCrc.add s name !current_state.cache;
      }
  
  let mem s = StaticCrc.mem s !current_state.cache

  let find s = StaticCrc.find s !current_state.cache

  let get_definitions () = StaticCrc.bindings !current_state.cache

  let register_inj (str: string) (tag: tag) =
    if not (AtomInjCrc.mem str !current_inj) then
      current_inj := AtomInjCrc.add str tag !current_inj
  
  let mem_inj str = AtomInjCrc.mem str !current_inj

  let find_inj str = AtomInjCrc.find str !current_inj

  let register_proj (str: string) ((tag, rid, p): tag * int * polarity) =
    if not (AtomProjCrc.mem str !current_proj) then
      current_proj := AtomProjCrc.add str (tag, rid, p) !current_proj
  
  let mem_proj str = AtomProjCrc.mem str !current_proj

  let find_proj str = AtomProjCrc.find str !current_proj
end

let static_clear () = 
  RangeManager.clear ();
  CrcManager.clear ()

let static_save () =
  RangeManager.save (), CrcManager.save ()

let static_restore (s1, s2) =
  RangeManager.restore s1;
  CrcManager.restore s2
