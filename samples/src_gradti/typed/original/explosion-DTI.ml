let rec mk_chain n x : ? =
  if n = 0 then x
  else
    (let next y : ? = 
      mk_chain (n - 1) (y : ?)
    in let dyn_next = (next : ? -> ?) in
    dyn_next x)
in
mk_chain 10000 (42 : ?);;



let rec pingpong n (f: ?) : ? =
  if n = 0 then f
  else
    (* ? から int->int へキャストし、即座に ? へ戻す（無意味な往復） *)
    (let f_typed = (f : int -> int) in
    let f_dyn = (f_typed : ?) in
    pingpong (n - 1) f_dyn)
in

let init x = x + 1 in
(* 10万回キャストの往復をさせる *)
let giant_func_dyn = pingpong 10 (init : ?) in

(* 最後に適用する *)
let typed_func = (giant_func_dyn : int -> int) in
typed_func 41



(* リストの多相関数。これで 'a list -> 'a list と推論させる *)
let id_list x =
  match x with
  | [] -> []
  | h :: t -> h :: t
in

let rec build_chain n (lst: ?) : ? =
  if n = 0 then lst
  else
    (* id_list を ?->? にキャストすると List(Y)? -> List(Y)! が生成される *)
    (let dyn_id = (id_list : ? -> ?) in
    (* lst (List(X)!) を渡すと List(X)! ;; List(Y)? が起き、内部で X! ;; Y? が発火して X->Y がリンクする！ *)
    build_chain (n - 1) (dyn_id lst))
in

let rec query m (lst: ?) =
  if m = 0 then 0
  else
    (* lst を int list にキャストすると、内部の X! ;; int? が発火し、ty_find(X) が呼ばれる！ *)
    (let check = (lst : [int]) in
    query (m - 1) lst)
in

(* 1. 起点となる空リスト（中身は X_0 list）を ? に隠蔽 *)
let orig = ([] : ?) in

(* 2. 1万回キャストを繰り返し、X_0 -> X_1 -> ... -> X_10000 の連鎖を作る *)
let res_dyn = build_chain 10000 orig in

(* 3. 【発火】一番新しい終端を int list に解決する（X_10000 -> int） *)
let x = (res_dyn : [int]) in

(* 4. 【計測】一番古い X_0 を持っている orig を 200 回 int list にキャストする！ *)
query 200 orig





(* 多相関数を受け取って、?に隠して返すプロキシ関数。
   これが呼ばれるたびに、引数 g に対して新しい型変数 X_n が生成される *)
let proxy g = (g : ?) in

let rec build_chain n (f: ?) : ? =
  if n = 0 then f
  else
    (* f (中身は X_{n-1} -> X_{n-1}) を proxy に渡す。
       ここで f は 'a -> 'a にキャストされるため、内部で
       dti(X_{n-1}->X_{n-1}, X_n->X_n) が発火し、X_{n-1} := X_n がリンクされる！ *)
    build_chain (n - 1) (proxy f)
in

let rec query m (f: ?) =
  if m = 0 then 0
  else
    (* 起点 f を int->int に解決する。
       ここで ty_find が 1万個のチェーンを辿る！ *)
    (let test = (f : int -> int) in
    query (m - 1) f)
in

(* 1. 起点となる型変数 X_0 を用意 *)
let id x = x in
let orig = (id : ?) in

(* 2. dti 関数を 10,000回 発生させ、X_0 -> X_1 -> ... -> X_10000 の連鎖を作る *)
let res_dyn = build_chain 1 orig in

(* 3. 連鎖の終端 X_10000 を int->int に単一化する *)
let x = (res_dyn : int -> int) in

(* 4. 起点 X_0 を 200 回解決させる *)
query 200 orig;;

(* let proxy = fun 'x14 -> fun (g: 'x14) -> 
  g<'x14!p> 
in
let build_chain = fun 'x15 -> fix build_chain (n: int): ? -> ? = fun (f: ?) -> 
  if n = 0 then f 
  else build_chain (n - 1) (proxy['x15] (f<'x15?p>))
in
let query = fix query (m: int): ? -> int = fun (f: ?) -> 
  if m = 0 then 0 
  else (let test = f<(? -> ?)?p;(id{int};int!)->(int?p;id{int})> in query (m - 1) f) 
in
let id = fun 'x10 -> fun (x: 'x10) -> x in
let orig = fun 'x16 -> id['x16]<'x16?p->'x16!p;(? -> ?)!> in
let res_dyn = build_chain[ν] 1 orig[ν] in
let x = res_dyn<(? -> ?)?p;(id{int};int!)->(int?p;id{int})> in
query 200 orig[ν] *)
