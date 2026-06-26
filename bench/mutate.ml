(*
  Mutate.ml — 型注釈を TyDyn に置き換えるユーティリティ
    - Phase 1 (analyze): 1 回の走査でメタ情報を収集
        * Fun の総数 (後行順, body -> self)
        * Fix の総数 (出現順, left-to-right, pre-order)
        * Fix.ty2 と直下の Fun 鎖の同期リンク:
            fix_idx -> [(pos, lam_idx)] （pos は外→内 1-based）
    - Phase 2 (apply): 1 回の走査で適用
        * Fun の仮引数注釈を選択に応じて TyDyn 化
        * 上記に対応して Fix.ty2 の該当ドメインを TyDyn 化
        * Fix.ty1 を Fix 出現順選択に応じて TyDyn 化
    - インデックス空間:
        1..N_fun                    : Fun 仮引数（後行順）
        N_fun+1..N_fun+N_fix        : Fix.ty1（Fix 出現順）
        N_fun+N_fix+1..N_fun+2N_fix :  Fix.ty2 の返り値（Fix 出現順）
        N_fun+2*N_fix+1 .. N_fun+2*N_fix+N_tapp: TAppExp の型引数 ty（後行順= e の中を先に番号付け → 自分）
*)

(* open Format *)
open Lambda_S_dti
open Utils.Error
open Syntax
open Syntax.ITGL


module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

(* ---------- ユーティリティ ---------- *)
let rec drop n xs =
  if n <= 0 then xs
  else match xs with [] -> [] | _ ::tl -> drop (n - 1) tl

(* ty = a1 -> a2 -> ... -> an -> r を (doms, ret) に分解 *)
let split_arrows (t : ty) : ty list * ty =
  let rec loop acc = function
    | TyFun (a, b) -> loop (a :: acc) b
    | r          -> (List.rev acc, r)
  in
  loop [] t

(* ドメイン列と戻り型から関数型を再構成 *)
let build_arrows (doms : ty list) (ret : ty) : ty =
  List.fold_right (fun a acc -> TyFun (a, acc)) doms ret

(* Fix 本体の先頭に連なる Fun 鎖（外→内）と残りの式を返す。アノテーションを保持 *)
let collect_head_funs (e : exp) : (range * id * anotated * ty) list * exp =
  let rec go acc = function
    | FunExp (r, (x, annot, t), body) ->
      go ((r, x, annot, t) :: acc) body
    | other -> (List.rev acc, other)
  in
  go [] e

(* Fun（後行順）・Fix（出現順）の個数カウント *)
let rec count_fun_params (t : exp) : int = match t with
  | FunExp (_, _, e) -> 1 + count_fun_params e
  | Var _ | IConst _ | BConst _ | UConst _ | NilExp _ -> 0
  | FixExp (_, _, _, _, e) | AscExp (_, e, _) | RefExp (_, e) | DerefExp (_, e) -> count_fun_params e
  | BinOp (_, _, e1 , e2) | AppExp (_, e1, e2) | ConsExp (_, e1, e2) | LetExp (_, _, e1, e2) | SubstExp (_, e1, e2) -> count_fun_params e1 + count_fun_params e2
  | IfExp (_, e1, e2, e3) -> count_fun_params e1 + count_fun_params e2 + count_fun_params e3
  | MatchExp (_, e, ms) -> count_fun_params e + List.fold_left (fun n (_, e) -> n + count_fun_params e) 0 ms
  | TupleExp (_, es) -> List.fold_left (fun n e -> n + count_fun_params e) 0 es

let rec count_fix_nodes (t : exp) : int = match t with
  | FixExp (_, _, _, _, e) -> 1 + count_fix_nodes e
  | Var _ | IConst _ | BConst _ | UConst _ | NilExp _ -> 0
  | FunExp (_, _, e) | AscExp (_, e, _) | RefExp (_, e) | DerefExp (_, e) -> count_fix_nodes e
  | BinOp (_, _, e1, e2) | AppExp (_, e1, e2) | ConsExp (_, e1, e2) | LetExp (_, _, e1, e2) | SubstExp (_, e1, e2) -> count_fix_nodes e1 + count_fix_nodes e2
  | IfExp (_, e1, e2, e3) -> count_fix_nodes e1 + count_fix_nodes e2 + count_fix_nodes e3
  | MatchExp (_, e, ms) -> count_fix_nodes e + List.fold_left (fun n (_, e) -> n + count_fix_nodes e) 0 ms
  | TupleExp (_, es) -> List.fold_left (fun n e -> n + count_fix_nodes e) 0 es

let (*rec*) count_tapp_nodes ((*t*)_ : exp) : int = 0
  (*match t with
  | Var _ | IConst _ | BConst _ | NilExp _ -> 0
  | TAppExp (_, e0, _) -> 1 + count_tapp_nodes e0
  | FunExp (_,_,_,e0)
  | FixExp (_,_,_,_,_,e0)
  | TFunExp(_,_,e0)
  | AscExp (_,e0,_)
  | CAppExp(_,_,e0) -> count_tapp_nodes e0
  | BinOp  (_,_,e1,e2)
  | AppExp (_,  e1,e2)
  | ConsExp(_,  e1,e2)
  | LetExp (_,_,e1,e2) -> count_tapp_nodes e1 + count_tapp_nodes e2
  | IfExp   (_,e1,e2,e3)
  | MatchExp(_,e1,e2,_,_,e3) ->
      count_tapp_nodes e1 + count_tapp_nodes e2 + count_tapp_nodes e3 *)


(* ---------- Phase 1: メタ解析（リンク収集 + 個数） ---------- *)

(* リンク: Fix 出現順 fix_idx に対し、(pos, lam_idx) のリスト
   pos: Fix 直下の Fun 鎖の外→内 1-based
   lam_idx: その Fun の「後行順」番号 *)
type link = { fix_idx : int; pos : int; lam_idx : int }

type analysis = {
  n_fun  : int;               (* Fun 総数（後行順） *)
  n_fix  : int;               (* Fix 総数（出現順） *)
  n_tapp : int;               (* TApp 総数 *)
  links  : (int * (int * int) list) list;  (* fix_idx -> [(pos, lam_idx)]  *)
}

(* collect_links c fixc t = (c', fixc', links) *)
let rec collect_links (c:int) (fixc:int) (t:exp) : int * int * link list = match t with
  | Var _ | IConst _ | BConst _ | UConst _ | NilExp _ -> (c, fixc, [])
  | FunExp (_, _, e) ->
    let c1, fixc1, ls1 = collect_links c fixc e in
    let idx_here = c1 + 1 in
    (idx_here, fixc1, ls1)
  | FixExp (_, _, _, _, e) ->
    let my_fix_idx = fixc + 1 in
    let heads, base = collect_head_funs e in
    let k = List.length heads in
    let l_base = count_fun_params base in
    (* 後行順: base の中身にある Fun が先に付番され、そのあと head の内側→外側 *)
    let my_links =
      let rec build pos acc =
        if pos > k then List.rev acc
        else
          let lam_idx = c + l_base + (k - pos + 1) in
          build (pos + 1) ({ fix_idx = my_fix_idx; pos; lam_idx } :: acc)
      in
      build 1 []
    in
    let c1, fixc1, ls_body = collect_links c my_fix_idx e in
    (c1, fixc1, my_links @ ls_body)
  | AscExp (_, e, _) | RefExp (_, e) | DerefExp (_, e) ->
    collect_links c fixc e
  | BinOp (_, _, e1, e2) | AppExp (_, e1, e2) | ConsExp (_, e1, e2) | LetExp (_, _, e1, e2) | SubstExp (_, e1, e2) ->
    let c1, f1, l1 = collect_links c fixc e1 in
    let c2, f2, l2 = collect_links c1 f1 e2 in
    (c2, f2, l1 @ l2)
  | IfExp (_, e1, e2, e3) ->
    let c1, f1, l1 = collect_links c fixc e1 in
    let c2, f2, l2 = collect_links c1 f1 e2 in
    let c3, f3, l3 = collect_links c2 f2 e3 in
    (c3, f3, l1 @ l2 @ l3)
  | MatchExp (_, e, ms) ->
    let c1, f1, l1 = collect_links c fixc e in
    List.fold_left
      (fun (c, f, l) (_, e) ->
        let c', f', l' = collect_links c f e in c', f', l @ l')
      (c1, f1, l1) ms
  | TupleExp (_, es) ->
    List.fold_left
      (fun (c, f, l) e ->
        let c', f', l' = collect_links c f e in c', f', l @ l')
      (c, fixc, []) es

let build_link_map (ls:link list) : (int * (int * int) list) list =
  let tbl : (int, (int * int) list) Hashtbl.t = Hashtbl.create 17 in
  List.iter (fun {fix_idx; pos; lam_idx} ->
    let prev = match Hashtbl.find_opt tbl fix_idx with None -> [] | Some xs -> xs in
    Hashtbl.replace tbl fix_idx ((pos, lam_idx) :: prev)
  ) ls;
  let acc = ref [] in
  Hashtbl.iter (fun k xs -> acc := (k, xs) :: !acc) tbl;
  List.sort (fun (a,_) (b,_) -> compare a b) !acc

let analyze (t:exp) : analysis =
  let n_fun = count_fun_params t in
  let n_fix = count_fix_nodes t in
  let n_tapp = count_tapp_nodes t in
  let (_c_end, _f_end, links) = collect_links 0 0 t in
  { n_fun; n_fix; n_tapp; links = build_link_map links }

(* ---------- Phase 2: 適用（Fun 変異 + Fix.ty2 同期 + Fix.ty1 変異） ---------- *)
type selection = {
  sel_fun      : IntSet.t;   (* 1..n_fun *)
  sel_fix      : IntSet.t;   (* Fix.ty1 *)
  sel_fix_ret  : IntSet.t;   (* Fix.ty2 return *)
  sel_tapp     : IntSet.t;   (* TApp ty *)
}

let selection_of_global_indices (a:analysis) (idxs:int list) : selection =
  let sel_fun =
    List.fold_left
      (fun s i -> if i >= 1 && i <= a.n_fun then IntSet.add i s else s)
      IntSet.empty idxs
  in
  let sel_fix =
    List.fold_left
      (fun s i ->
         if i > a.n_fun && i <= a.n_fun + a.n_fix
         then IntSet.add (i - a.n_fun) s else s)
      IntSet.empty idxs
  in
  let sel_fix_ret =
    List.fold_left
      (fun s i ->
         if i > a.n_fun + a.n_fix && i <= a.n_fun + 2 * a.n_fix
         then IntSet.add (i - (a.n_fun + a.n_fix)) s else s)
      IntSet.empty idxs
  in
  let base = a.n_fun + 2 * a.n_fix in
  let sel_tapp =
    List.fold_left
      (fun s i ->
         if i > base && i <= base + a.n_tapp
         then IntSet.add (i - base) s else s)
      IntSet.empty idxs
  in
  { sel_fun; sel_fix; sel_fix_ret; sel_tapp }

(* 適用本体。lamc/fixc は現在までに消費した Fun/Fix のカウンタ（後行順/出現順）。 *)
let rec apply (a:analysis) (sel:selection) (lamc:int) (fixc:int) (tappc:int) (t:exp) : int * int * int * exp = match t with
  | Var _ | IConst _ | BConst _ | UConst _ | NilExp _ -> (lamc, fixc, tappc, t)
  | FunExp (r, (x, annot, u), e) ->
    let lamc1, fixc1, tappc1, e' = apply a sel lamc fixc tappc e in
    let idx_here = lamc1 + 1 in
    let u' = if IntSet.mem idx_here sel.sel_fun then TyDyn else u in
    (idx_here, fixc1, tappc1, FunExp (r, (x, annot, u'), e'))
  | FixExp (r, x, (y, annot, u1), u2, e) ->
    let my_fix_idx = fixc + 1 in
    let u1' = if IntSet.mem my_fix_idx sel.sel_fix then TyDyn else u1 in
    let doms, ret = split_arrows u2 in
    let max_pos = List.length doms in
    let doms' =
      let arr = Array.of_list doms in
      begin match List.assoc_opt my_fix_idx a.links with
      | None -> ()
      | Some pairs ->
          List.iter (fun (pos, lam_idx) ->
            if pos >= 1 && pos <= max_pos && IntSet.mem lam_idx sel.sel_fun
            then arr.(pos - 1) <- TyDyn) pairs
      end;
      Array.to_list arr
    in
    let ret_selected = IntSet.mem my_fix_idx sel.sel_fix_ret in
    let ret' = if ret_selected then TyDyn else ret in
    let u2' = build_arrows doms' ret' in

    (* 先に内部へ適用してから AscExp との返り型同期 *)
    let lamc1, fixc1, tappc1, e_applied = apply a sel lamc my_fix_idx tappc e in
    let e_synced =
      let heads, base = collect_head_funs e_applied in
      match base with
      | AscExp (rA, eInner, uA) ->
          let uA' = if ret_selected then TyDyn else uA in
          let base' = AscExp (rA, eInner, uA') in
          List.fold_right
            (fun (rf, xf, annotf, uf) acc -> FunExp (rf, (xf, annotf, uf), acc))
            heads base'
      | _ -> e_applied
    in
    (lamc1, fixc1, tappc1, FixExp (r, x, (y, annot, u1'), u2', e_synced))
  | BinOp (r, op, e1, e2) ->
    let lamc1, fixc1, tappc1, e1' = apply a sel lamc fixc tappc e1 in
    let lamc2, fixc2, tappc2, e2' = apply a sel lamc1 fixc1 tappc1 e2 in
    (lamc2, fixc2, tappc2, BinOp (r, op, e1', e2'))
  | AppExp (r, e1, e2) ->
    let lamc1, fixc1, tappc1, e1' = apply a sel lamc fixc tappc e1 in
    let lamc2, fixc2, tappc2, e2' = apply a sel lamc1 fixc1 tappc1 e2 in
    (lamc2, fixc2, tappc2, AppExp (r, e1', e2'))
  | ConsExp (r, e1, e2) ->
    let lamc1, fixc1, tappc1, e1' = apply a sel lamc fixc tappc e1 in
    let lamc2, fixc2, tappc2, e2' = apply a sel lamc1 fixc1 tappc1 e2 in
    (lamc2, fixc2, tappc2, ConsExp (r, e1', e2'))
  | LetExp (r, id, e1, e2) ->
    let lamc1, fixc1, tappc1, e1' = apply a sel lamc fixc tappc e1 in
    let lamc2, fixc2, tappc2, e2' = apply a sel lamc1 fixc1 tappc1 e2 in
    (lamc2, fixc2, tappc2, LetExp (r, id, e1', e2'))
  | IfExp (r, e1, e2, e3) ->
    let lamc1, fixc1, tappc1, e1' = apply a sel lamc fixc tappc e1 in
    let lamc2, fixc2, tappc2, e2' = apply a sel lamc1 fixc1 tappc1 e2 in
    let lamc3, fixc3, tappc3, e3' = apply a sel lamc2 fixc2 tappc2 e3 in
    (lamc3, fixc3, tappc3, IfExp (r, e1', e2', e3'))
  | MatchExp (r, e, ms) ->
    let lamc1, fixc1, tappc1, e' = apply a sel lamc fixc tappc e in
    let rec apply_ms lamc fixc tappc ms res = match ms with
      | (mf, e) :: ms ->
        let lamc, fixc, tappc, e = apply a sel lamc fixc tappc e in
        apply_ms lamc fixc tappc ms ((mf, e) :: res)
      | [] -> (lamc, fixc, tappc, MatchExp (r, e', List.rev res))
    in
    apply_ms lamc1 fixc1 tappc1 ms []
  | AscExp (r, e1, ty) ->
    let lamc1, fixc1, tappc1, e1' = apply a sel lamc fixc tappc e1 in
    (lamc1, fixc1, tappc1, AscExp (r, e1', ty))
  | TupleExp (r, es) ->
    let rec apply_es lamc fixc tappc es res = match es with
      | e :: es ->
        let lamc, fixc, tappc, e = apply a sel lamc fixc tappc e in
        apply_es lamc fixc tappc es (e :: res)
      | [] -> (lamc, fixc, tappc, TupleExp (r, List.rev res))
    in
    apply_es lamc fixc tappc es []
  | RefExp (r, e) ->
    let lamc1, fixc1, tappc1, e' = apply a sel lamc fixc tappc e in
    (lamc1, fixc1, tappc1, RefExp (r, e'))
  | DerefExp (r, e) ->
    let lamc1, fixc1, tappc1, e' = apply a sel lamc fixc tappc e in
    (lamc1, fixc1, tappc1, DerefExp (r, e'))
  | SubstExp (r, e1, e2) ->
    let lamc1, fixc1, tappc1, e1' = apply a sel lamc fixc tappc e1 in
    let lamc2, fixc2, tappc2, e2' = apply a sel lamc1 fixc1 tappc1 e2 in
    (lamc2, fixc2, tappc2, SubstExp (r, e1', e2'))


(* ---------- 公開 API ---------- *)

let mutate_term_with_indices (idxs:int list) (t:exp) : exp =
  let a   = analyze t in
  let sel = selection_of_global_indices a idxs in
  let (_lam_end, _fix_end, _tapp_end, t') = apply a sel 0 0 0 t in
  t'

let mutate_prog_with_indices (idxs:int list) (p : program) : program =
  let mutated = match p with
    | Exp t     -> Exp (mutate_term_with_indices idxs t)
    | LetDecl (x,t) -> LetDecl (x, mutate_term_with_indices idxs t)
  in
  let _, tyenv, _ = Stdlib.pervasives ~config:(Config.create ~compile:true ()) in
  let p, u = Typing.ITGL.type_of_program tyenv mutated in
  let _, p, _ = Normalize.ITGL.normalize tyenv p u in
  p

(* 0..n を長さ順に全列挙（昇順） *)
let all_subsets_by_length (n:int) : int list list =
  let rec range a b = if a > b then [] else a :: range (a+1) b in
  let xs = range 1 n in
  let rec choose k = function
    | _ when k = 0 -> [ [] ]
    | [] -> []
    | y :: ys ->
        let with_y    = List.map (fun t -> y :: t) (choose (k-1) ys) in
        let without_y = choose k ys in
        with_y @ without_y
  in
  let rec loop k acc =
    if k > n then List.rev acc
    else loop (k+1) (choose k xs :: acc)
  in
  loop 0 [] |> List.concat

let mutate_all (p:program) : program list =
  let t =
    match p with Exp t | LetDecl (_, t) -> t
  in
  let _, tyenv, _ = Stdlib.pervasives ~config:(Config.create ~compile:true ()) in
  let p, u = Typing.ITGL.type_of_program tyenv p in
  let _, p, _ = Normalize.ITGL.normalize tyenv p u in
  Format.fprintf Format.std_formatter "program's type is %a\n" Pp.pp_ty u;
  let a = analyze t in
  let n_total = a.n_fun + 2 * a.n_fix + a.n_tapp in
  let subsets = all_subsets_by_length n_total in
  List.map (fun idxs -> mutate_prog_with_indices idxs p) subsets
