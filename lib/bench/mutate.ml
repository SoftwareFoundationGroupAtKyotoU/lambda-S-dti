(*
  Mutate.ml — 型注釈を TyDyn に置き換えるユーティリティ

  スロット（= Dyn 化しうるユーザー型注釈）を **ソース出現順（pre-order DFS,
  left-to-right）で 1..N に番号付け**し、選択された番号の注釈を `?` (TyDyn) に置換する。

  1 スロットの内訳:
    - 非合成 FunExp の仮引数注釈                     … 1 スロット
    - 非合成 FixExp（`fix f (y:u1) h1 h2 … : R = body`）
        * param スロット群: y ＋ head Fun 鎖 h1..hk を外→内で (1+k) 個
          （y ↔ u1、hi ↔ u2 の第 i ドメイン ＝ FunExp 注釈、を同期して Dyn 化）
        * return スロット: R（u2 の末尾。body 適用後の先頭が AscExp なら注釈も同期）
        以上 (1+k)+1 スロットを param → return の順で消費し、その後 body(head 鎖を除く)へ再帰
    - 合成名（`_for_loop` 等）の Fun/Fix はスロットを消費しない

  1 回の pre-order 走査 `walk` が「数える(analyze)」と「適用(mutate)」の両方を担う。
*)

open Utils.Error
open Syntax
open Syntax.ITGL

module IntSet = Set.Make (Int)

(* ---------- ユーティリティ ---------- *)

(* "_" で始まる id はパーサが糖衣構文展開時に合成した名前（_match_arg, _for_loop,
 * _while_loop 等）。レキサの ID 規則は小文字始まりのみを許すため、ユーザーが
 * 書いたコードにはこの形の名前は絶対に現れない。これらは変異の対象から除外する。 *)
let is_synthetic (x : id) : bool =
  String.length x > 0 && x.[0] = '_'

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
    | FunExp (r, (x, annot, t), body) -> go ((r, x, annot, t) :: acc) body
    | other -> (List.rev acc, other)
  in
  go [] e

(* ---------- 出現順の 1 パス走査 ---------- *)

(* sel = None      : スロットを数えるだけ（変換しない）
   sel = Some s    : s に含まれるスロット番号の注釈を TyDyn 化
   戻り値 = (消費したスロット数, 変換後の式) *)
let rec walk (sel : IntSet.t option) (k : int) (t : exp) : int * exp =
  let recur k e = walk sel k e in
  let dyn_if slot u = match sel with
    | Some s when IntSet.mem slot s -> TyDyn
    | _ -> u
  in
  let selected slot = match sel with Some s -> IntSet.mem slot s | None -> false in
  match t with
  | Var _ | IConst _ | BConst _ | UConst _ | FConst _ | NilExp _ -> (k, t)

  | FunExp (r, (x, annot, u), e) when is_synthetic x ->
    let k1, e' = recur k e in
    (k1, FunExp (r, (x, annot, u), e'))
  | FunExp (r, (x, annot, u), e) ->
    let slot = k + 1 in
    let u' = dyn_if slot u in
    let k1, e' = recur slot e in
    (k1, FunExp (r, (x, annot, u'), e'))

  | FixExp (r, x, (y, annot, u1), u2, e) when is_synthetic x ->
    let k1, e' = recur k e in
    (k1, FixExp (r, x, (y, annot, u1), u2, e'))
  | FixExp (r, x, (y, annot, u1), u2, e) ->
    let heads, rest = collect_head_funs e in
    let doms, ret = split_arrows u2 in
    let n_heads = List.length heads in
    (* param スロット: k+1 = y/u1, k+1+i = heads[i-1]/doms[i-1] (i=1..n_heads)
       return スロット: k+1+n_heads+1 *)
    let ret_slot = k + n_heads + 2 in
    let u1' = dyn_if (k + 1) u1 in
    let doms' = List.mapi (fun j d -> dyn_if (k + 2 + j) d) doms in
    let heads' =
      List.mapi (fun j (rf, xf, af, uf) -> (rf, xf, af, dyn_if (k + 2 + j) uf)) heads
    in
    let ret_selected = selected ret_slot in
    let ret' = if ret_selected then TyDyn else ret in
    let u2' = build_arrows doms' ret' in
    let k1, rest' = recur ret_slot rest in
    let rest'' = match rest' with
      | AscExp (rA, eInner, uA) ->
        AscExp (rA, eInner, (if ret_selected then TyDyn else uA))
      | other -> other
    in
    let e' =
      List.fold_right
        (fun (rf, xf, af, uf) acc -> FunExp (rf, (xf, af, uf), acc)) heads' rest''
    in
    (k1, FixExp (r, x, (y, annot, u1'), u2', e'))

  | AscExp (r, e, ty)   -> let k1, e' = recur k e in (k1, AscExp (r, e', ty))
  | RefExp (r, e)       -> let k1, e' = recur k e in (k1, RefExp (r, e'))
  | DerefExp (r, e)     -> let k1, e' = recur k e in (k1, DerefExp (r, e'))
  | LengthExp (r, e)    -> let k1, e' = recur k e in (k1, LengthExp (r, e'))

  | BinOp (r, op, e1, e2) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in (k2, BinOp (r, op, e1', e2'))
  | AppExp (r, e1, e2) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in (k2, AppExp (r, e1', e2'))
  | ConsExp (r, e1, e2) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in (k2, ConsExp (r, e1', e2'))
  | LetExp (r, id, e1, e2) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in (k2, LetExp (r, id, e1', e2'))
  | SubstExp (r, e1, e2) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in (k2, SubstExp (r, e1', e2'))
  | MakeArrayExp (r, e1, e2) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in (k2, MakeArrayExp (r, e1', e2'))
  | GetExp (r, e1, e2) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in (k2, GetExp (r, e1', e2'))

  | IfExp (r, e1, e2, e3) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in let k3, e3' = recur k2 e3 in
    (k3, IfExp (r, e1', e2', e3'))
  | PutExp (r, e1, e2, e3) ->
    let k1, e1' = recur k e1 in let k2, e2' = recur k1 e2 in let k3, e3' = recur k2 e3 in
    (k3, PutExp (r, e1', e2', e3'))

  | MatchExp (r, e, ms) ->
    let k1, e' = recur k e in
    let k2, ms_rev =
      List.fold_left
        (fun (kk, acc) (mf, me) -> let kk', me' = recur kk me in (kk', (mf, me') :: acc))
        (k1, []) ms
    in
    (k2, MatchExp (r, e', List.rev ms_rev))
  | TupleExp (r, es) ->
    let k1, es_rev =
      List.fold_left
        (fun (kk, acc) e -> let kk', e' = recur kk e in (kk', e' :: acc)) (k, []) es
    in
    (k1, TupleExp (r, List.rev es_rev))

(* スロット総数 *)
let analyze (t : exp) : int = fst (walk None 0 t)

(* ---------- 公開 API ---------- *)

let mutate_term_with_indices (idxs : int list) (t : exp) : exp =
  let sel = List.fold_left (fun s i -> IntSet.add i s) IntSet.empty idxs in
  snd (walk (Some sel) 0 t)

(* 0..n のすべての部分集合を要素数順に全列挙（昇順）。ML 側と grift 側で共有する列挙順。 *)
let all_subsets_by_length (n : int) : int list list =
  let rec range a b = if a > b then [] else a :: range (a + 1) b in
  let xs = range 1 n in (* [1; 2; ...; n] *)
  let rec choose k = function
    | _ when k = 0 -> [ [] ]
    | [] -> []
    | y :: ys ->
      let with_y    = List.map (fun t -> y :: t) (choose (k - 1) ys) in
      let without_y = choose k ys in
      with_y @ without_y
  in
  let rec loop k acc =
    if k > n then List.rev acc
    else loop (k + 1) (choose k xs :: acc)
  in
  loop 0 [] |> List.concat