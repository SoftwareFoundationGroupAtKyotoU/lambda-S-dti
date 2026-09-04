(* Bench_grift — grift(.grift) 側の lattice ベンチマーク実行。
   旧 benchC/run_grift.py の OCaml 移植。

   - grift ソースを S 式として読み、Dyn 化しうる型注釈スロットを
     Mutate（ML 側）と同じ「出現順」で列挙する。
   - Mutate.all_subsets_by_length で ML 側と同一順の variant を作り、
     各 variant を grift でコンパイル（perf / cast-profiler / C バックエンド）して実行し、
     logs/<ts>/GRIFT_<name>.jsonl / GRIFTC_<name>.jsonl に書き出す。

   grift 実行環境（racket + LLVM 対応の grift）が必要。壊れている / 無い場合は
   各 variant で "[grift compile failed]" を出して継続する。 *)

module IntSet = Set.Make (Int)

(* ===================== S 式 ===================== *)

type sx = { id : int; k : node }
and node = Atom of string | Lst of sx list

let fresh =
  let c = ref 0 in
  fun k -> incr c; { id = !c; k }

(* `;` 以降を行末まで除去し、() [] を空白で区切ってトークン化。
   [ ] は ( ) と等価に扱う（grift のリーダ準拠）。 *)
let tokenize (src : string) : string list =
  let no_comments =
    String.split_on_char '\n' src
    |> List.map (fun line ->
        match String.index_opt line ';' with
        | Some i -> String.sub line 0 i
        | None -> line)
    |> String.concat " "
  in
  let b = Buffer.create (String.length no_comments) in
  String.iter
    (fun ch -> match ch with
       | '(' | '[' -> Buffer.add_string b " ( "
       | ')' | ']' -> Buffer.add_string b " ) "
       | c -> Buffer.add_char b c)
    no_comments;
  Buffer.contents b
  |> String.split_on_char ' '
  |> List.filter (fun t -> t <> "")

let parse_forms (tokens : string list) : sx list =
  let toks = ref tokens in
  let peek () = match !toks with [] -> None | t :: _ -> Some t in
  let next () =
    match !toks with [] -> failwith "grift sexp: unexpected EOF" | t :: r -> toks := r; t
  in
  let rec one () : sx =
    match next () with
    | "(" ->
      let rec loop acc =
        match peek () with
        | None -> failwith "grift sexp: unclosed ("
        | Some ")" -> ignore (next ()); fresh (Lst (List.rev acc))
        | Some _ -> loop (one () :: acc)
      in
      loop []
    | ")" -> failwith "grift sexp: unexpected )"
    | atom -> fresh (Atom atom)
  in
  let rec all acc = match peek () with None -> List.rev acc | Some _ -> all (one () :: acc) in
  all []

(* dyn に含まれる id のノードは "Dyn" に。list は 2 番目の子が `:` なら [..] 記法。 *)
let rec serialize (dyn : IntSet.t) (s : sx) : string =
  if IntSet.mem s.id dyn then "Dyn"
  else
    match s.k with
    | Atom a -> a
    | Lst xs ->
      let inner = String.concat " " (List.map (serialize dyn) xs) in
      (match xs with
       | _ :: { k = Atom ":"; _ } :: _ -> "[" ^ inner ^ "]"
       | _ -> "(" ^ inner ^ ")")

(* ===================== analyze（出現順スロット列挙） ===================== *)

(* mutation 対象外の define 名（grift サンプルのリスト表現ヘルパと entry point） *)
let fixed_names = [ "benchmark"; "empty-list"; "cons"; "is-empty"; "head"; "tail" ]

let atom_is s = function { k = Atom a; _ } -> a = s | _ -> false

(* (A -> B) を [A] ++ slots(B) に分解。それ以外は [自身]。 *)
let rec nested_type_slots (s : sx) : sx list =
  match s.k with
  | Lst (a :: op :: b :: _) when atom_is "->" op -> a :: nested_type_slots b
  | _ -> [ s ]

let rec is_referenced (name : string) (s : sx) : bool =
  match s.k with
  | Atom a -> a = name
  | Lst xs -> List.exists (is_referenced name) xs

(* [arg : T] 形から T を取り出す *)
let typed_binding_ty (s : sx) : sx option =
  match s.k with
  | Lst (_ :: colon :: ty :: _) when atom_is ":" colon -> Some ty
  | _ -> None

(* body 内の lambda を pre-order で辿り、各 lambda の第1引数の型注釈を集める *)
let rec collect_lambda_arg_tys (acc : sx list) (s : sx) : sx list =
  let acc =
    match s.k with
    | Lst (hd :: arglist :: _) when atom_is "lambda" hd ->
      (match arglist.k with
       | Lst (arg0 :: _) -> (match typed_binding_ty arg0 with Some ty -> ty :: acc | None -> acc)
       | _ -> acc)
    | _ -> acc
  in
  match s.k with Lst xs -> List.fold_left collect_lambda_arg_tys acc xs | Atom _ -> acc

(* 1 つの define から、出現順のスロット群（各群 = 一緒に Dyn 化する sx ノード）を返す。 *)
let slots_of_define (d : sx) : sx list list =
  match d.k with
  | Lst (hd :: header :: _rest) when atom_is "define" hd ->
    let name = match header.k with Lst ({ k = Atom n; _ } :: _) -> n | _ -> "" in
    if List.mem name fixed_names then []
    else begin
      (* define 引数の型注釈（順番どおり） *)
      let arg_tys =
        match header.k with
        | Lst (_ :: args) -> List.filter_map typed_binding_ty args
        | _ -> []
      in
      let dchildren = match d.k with Lst xs -> xs | _ -> [] in
      (* 先頭の裸の `:` の次を返り型、その先を body とみなす *)
      let ret_node, body_nodes =
        let rec find = function
          | colon :: rt :: after when atom_is ":" colon -> Some (rt, after)
          | _ :: tl -> find tl
          | [] -> None
        in
        match find dchildren with Some (rt, after) -> (Some rt, after) | None -> (None, [])
      in
      let ret_slots = match ret_node with Some rt -> nested_type_slots rt | None -> [] in
      let lam_tys = List.rev (List.fold_left collect_lambda_arg_tys [] body_nodes) in
      let n_ret = List.length ret_slots in
      let lam_groups =
        List.mapi
          (fun i lt -> if i < n_ret - 1 then [ lt; List.nth ret_slots i ] else [ lt ])
          lam_tys
      in
      let is_rec = List.exists (is_referenced name) body_nodes in
      let arg_groups = List.map (fun t -> [ t ]) arg_tys in
      let ret_group =
        if is_rec && n_ret > 0 then [ [ List.nth ret_slots (n_ret - 1) ] ] else []
      in
      arg_groups @ lam_groups @ ret_group
    end
  | _ -> []

let top_defines (forms : sx list) : sx list =
  List.filter
    (fun f -> match f.k with
       | Lst (hd :: _) ->
         (match hd.k with Atom ("define" | "module" | "imports") -> true | _ -> false)
       | _ -> false)
    forms

(* 公開: grift ソース文字列 → (top-level define 群, 出現順スロット群) *)
let analyze_src (src : string) : sx list * sx list list =
  let forms = parse_forms (tokenize src) in
  let defs = top_defines forms in
  (defs, List.concat_map slots_of_define defs)

let n_slots (src : string) : int = List.length (snd (analyze_src src))

(* subset = 1-based のスロット群インデックス列。該当群のノードを Dyn 化して module 文字列に。
   parse は 1 回だけ行い、グルーピングと serialize で同じノード（同じ id）を使う。 *)
let serialize_variant (defs : sx list) (groups : sx list list) (subset : int list) : string =
  let dyn =
    List.fold_left
      (fun acc gi ->
        List.fold_left
          (fun acc (n : sx) -> IntSet.add n.id acc)
          acc (List.nth groups (gi - 1)))
      IntSet.empty subset
  in
  String.concat "\n" (List.map (serialize dyn) defs)

(* テスト・デバッグ用: src を parse し subset を Dyn 化した module 文字列を返す *)
let render_variant (src : string) (subset : int list) : string =
  let defs, groups = analyze_src src in
  serialize_variant defs groups subset

(* ===================== grift 実行 ===================== *)

let read_file p =
  let ic = open_in_bin p in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

let write_file p s =
  let oc = open_out p in output_string oc s; close_out oc

let driver_code (loop_count : int) : string =
  Printf.sprintf
    "\n;; --- Auto-generated Loop Driver ---\n\
     (define (run-benchmark-loop [k : Int]) : Unit\n\
    \  (if (<= k 0)\n\
    \      ()\n\
    \      (begin\n\
    \        (time (benchmark))\n\
    \        (run-benchmark-loop (- k 1)))))\n\
     (run-benchmark-loop %d)\n"
    loop_count

(* "marker" の直後に現れる数値トークンを全部拾う *)
let numbers_after (marker : string) (s : string) : string list =
  let m = String.length marker and n = String.length s in
  let is_num c =
    (c >= '0' && c <= '9') || c = '.' || c = '-' || c = '+' || c = 'e' || c = 'E'
  in
  let rec go i acc =
    if i + m > n then List.rev acc
    else if String.sub s i m = marker then begin
      let j = ref (i + m) in
      while !j < n && (s.[!j] = ' ' || s.[!j] = '\t') do incr j done;
      let k = ref !j in
      while !k < n && is_num s.[!k] do incr k done;
      let tok = String.sub s !j (!k - !j) in
      go !k (tok :: acc)
    end
    else go (i + 1) acc
  in
  go 0 []

let parse_times (out : string) : float list =
  numbers_after "time (sec):" out |> List.filter_map float_of_string_opt

let substr_after (sub : string) (line : string) : string option =
  let m = String.length sub and n = String.length line in
  let rec find i =
    if i + m > n then None
    else if String.sub line i m = sub then Some (String.sub line (i + m) (n - i - m))
    else find (i + 1)
  in
  find 0

let ints_of (s : string) : int list =
  s
  |> String.split_on_char ' '
  |> List.concat_map (String.split_on_char '\t')
  |> List.filter_map int_of_string_opt

let parse_prof (out : string) : int option * int option =
  List.fold_left
    (fun (cast, longest) line ->
       match substr_after "total casts:" line with
       | Some rest -> (Some (List.fold_left ( + ) 0 (ints_of rest)), longest)
       | None ->
         (match substr_after "longest proxy chain:" line with
          | Some rest ->
            (cast, (match ints_of rest with x :: _ -> Some x | [] -> longest))
          | None -> (cast, longest)))
    (None, None)
    (String.split_on_char '\n' out)

let run_bin (bin : string) (stdin_data : string) : string option =
  if not (Sys.file_exists bin) then None
  else begin
    let out, inp, err = Unix.open_process_full bin (Unix.environment ()) in
    output_string inp stdin_data;
    close_out inp;
    let so = In_channel.input_all out in
    let _se = In_channel.input_all err in
    ignore (Unix.close_process_full (out, inp, err));
    Some so
  end

let jrow ~mode ~idx ~after_mutate ~times ~cast ~longest : Yojson.Safe.t =
  Bench_json.obj
    [ ("mode", Bench_json.str mode);
      ("mutant_index", Bench_json.int idx);
      ("after_mutate", Bench_json.str after_mutate);
      ("times_sec", Bench_json.list (List.map Bench_json.float times));
      ("mem", `Null);
      ("cast", (match cast with Some c -> Bench_json.int c | None -> `Null));
      ("inference", `Null);
      ("longest", (match longest with Some l -> Bench_json.int l | None -> `Null)) ]

let run ~log_dir ~grift_src ~itr ~static ~file =
  let input_path = Bench_config.input_path ~static file in
  let src = read_file grift_src in
  let defs, groups = analyze_src src in
  let n = List.length groups in
  let subsets = if static then [ [] ] else Mutate.all_subsets_by_length n in
  let base_input = String.trim (read_file input_path) in
  let repeat k = String.concat "" (List.init k (fun _ -> base_input ^ "\n")) in
  let input_perf = repeat (itr + 10) in
  let input_prof = repeat (1 + 10) in
  let suffix = if static then "_fs" else "" in
  let g = Bench_config.grift_cmd in
  let grift_dir = Filename.concat log_dir "GRIFT" in
  if not (Sys.file_exists grift_dir) then Sys.mkdir grift_dir 0o755;
  let work = Filename.concat log_dir (Printf.sprintf "grift_work_%s%s" file suffix) in
  if not (Sys.file_exists work) then Sys.mkdir work 0o755;
  let oc_g = open_out (Printf.sprintf "%s/GRIFT_%s%s.jsonl" log_dir file suffix) in
  let oc_gc = open_out (Printf.sprintf "%s/GRIFTC_%s%s.jsonl" log_dir file suffix) in
  Printf.printf "\n==> GRIFT %s%s (%d variants)\n%!" file suffix (List.length subsets);
  List.iteri
    (fun si subset ->
      let idx = si + 1 in
      let base_code = serialize_variant defs groups subset in
      let cdir = Printf.sprintf "%s/config_%d" work idx in
      if not (Sys.file_exists cdir) then Sys.mkdir cdir 0o755;
      let perf_f = Filename.concat cdir "perf.grift" in
      let prof_f = Filename.concat cdir "prof.grift" in
      write_file perf_f (base_code ^ driver_code itr);
      write_file prof_f (base_code ^ driver_code 1);
      let compile label extra src out =
        let cmd =
          Printf.sprintf "%s -O 3 %s -o %s %s > /dev/null 2>&1" g extra
            (Filename.quote out) (Filename.quote src)
        in
        if Sys.command cmd <> 0 then
          Format.eprintf "[grift compile failed] %s#%d %s@." file idx label
      in
      compile "perf" "" perf_f (Filename.concat cdir "bench_perf");
      compile "prof" "--cast-profiler" prof_f (Filename.concat cdir "bench_prof");
      compile "c" "--backend C" perf_f (Filename.concat cdir "bench_c_perf");
      (* ログ用に .c を1つ取り出す *)
      let dest_c = Printf.sprintf "%s%d.c" file idx in
      ignore
        (Sys.command
           (Printf.sprintf "cd %s && %s --backend C --keep-ir %s perf.grift > /dev/null 2>&1"
              (Filename.quote cdir) g (Filename.quote dest_c)));
      (try Sys.rename (Filename.concat cdir dest_c) (Filename.concat grift_dir dest_c)
       with _ -> ());
      (* 実行・計測 *)
      let times =
        match run_bin (Filename.concat cdir "bench_perf") input_perf with
        | Some o -> parse_times o
        | None -> []
      in
      let cast, longest =
        match run_bin (Filename.concat cdir "bench_prof") input_prof with
        | Some o -> parse_prof o
        | None -> (None, None)
      in
      let times_c =
        match run_bin (Filename.concat cdir "bench_c_perf") input_perf with
        | Some o -> parse_times o
        | None -> []
      in
      Bench_json.to_channel_ln oc_g
        (jrow ~mode:"GRIFT" ~idx ~after_mutate:base_code ~times ~cast ~longest);
      Bench_json.to_channel_ln oc_gc
        (jrow ~mode:"GRIFTC" ~idx ~after_mutate:base_code ~times:times_c ~cast:None
           ~longest:None))
    subsets;
  close_out oc_g;
  close_out oc_gc;
  ignore (Sys.command (Printf.sprintf "rm -rf %s" (Filename.quote work)))
