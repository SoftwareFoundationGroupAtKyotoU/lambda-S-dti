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
       | '\r' | '\t' -> Buffer.add_char b ' '
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
    let tmp = Filename.temp_file "grift_in_" ".txt" in
    Fun.protect
      ~finally:(fun () -> try Sys.remove tmp with _ -> ())
      (fun () ->
        let oc = open_out_bin tmp in
        output_string oc stdin_data;
        close_out oc;
        let cmd =
          Printf.sprintf "%s < %s 2>/dev/null"
            (Filename.quote bin) (Filename.quote tmp)
        in
        let ic = Unix.open_process_in cmd in
        let so = In_channel.input_all ic in
        ignore (Unix.close_process_in ic);
        Some so)
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

(* ===================== 並列コンパイル =====================

   grift/Racket コンパイラの起動コストを mutant 数 × 3 (perf / cast-profiler /
   Cバックエンド) 回払っているのが最大のボトルネック。Bench_builder はもともと
   clang専用ではなく「コマンド文字列のリストを1回の make -j で並列実行し、
   out_path の存在で成否判定する」完全に汎用な機構なので、ここでも
   そのまま再利用する。実行(計測)フェーズは今までどおり mutant ごとに
   独立したプロセスで直列に行う — 識別子リネームや複数mutantの同一プロセス
   同居は一切行わないため、GCやタイミング計測の共有状態汚染、障害分離の
   後退、--cast-profiler の累積といったリスクは発生しない。 *)

type grift_job_kind = Perf | Prof | Cbackend | CbackendStatic

type grift_prepared_mutant = {
  idx : int;
  base_code : string;         (* jsonl の after_mutate に使う *)
  cdir : string;
  jobs : (grift_job_kind * Bench_builder.job) list;  (* このmutantの3(or 4)ジョブ *)
}

(* Phase 1 の1 mutant分: perf.grift / prof.grift を書き出し、コンパイル
   ジョブを組み立てるだけ。Sys.command は一切呼ばない。~static:true のときは
   grift 自身のネイティブ --static (cast-representation=Static) を追加した
   Cバックエンドのジョブも作り、通常の(coercionベースの) Cバックエンドと
   両方計測できるようにする。 *)
let prepare_mutant ~work ~g ~monotonic_flag ~itr ~static defs groups si subset : grift_prepared_mutant =
  let idx = si + 1 in
  let base_code = serialize_variant defs groups subset in
  let cdir = Printf.sprintf "%s/config_%d" work idx in
  if not (Sys.file_exists cdir) then Sys.mkdir cdir 0o755;
  let perf_f = Filename.concat cdir "perf.grift" in
  let prof_f = Filename.concat cdir "prof.grift" in
  write_file perf_f (base_code ^ driver_code itr);
  write_file prof_f (base_code ^ driver_code 1);
  let job extra src out =
    (* grift --backend C は中間 .c ファイルを Racket の make-temporary-file で
       TMPDIR (既定 /var/tmp) 直下に作る。このリポジトリが対象とする Racket 7.2 の
       make-temporary-file は (current-seconds)+(current-inexact-milliseconds) から
       ファイル名を作るだけで衝突時のリトライを持たないため、make -j で大量の
       grift プロセスを同時起動すると同一ミリ秒に同名を生成して
       "with-output-to-file: file exists" で失敗することがある(mutant 数の多い
       ターゲットほど発生しやすい)。TMPDIR をこの mutant 専用の cdir に向けて
       プロセス間で温度ディレクトリを共有させないことで衝突自体を無くす。 *)
    let cmd =
      Printf.sprintf "TMPDIR=%s %s -O 3 %s %s -o %s %s > /dev/null 2>&1"
        (Filename.quote cdir) g monotonic_flag extra
        (Filename.quote out) (Filename.quote src)
    in
    { Bench_builder.out_path = out; cmd }
  in
  let bench_perf = Filename.concat cdir "bench_perf" in
  let bench_prof = Filename.concat cdir "bench_prof" in
  let bench_c_perf = Filename.concat cdir "bench_c_perf" in
  let base_jobs = [
    Perf,     job ""                 perf_f bench_perf;
    Prof,     job "--cast-profiler"  prof_f bench_prof;
    Cbackend, job "--backend C"      perf_f bench_c_perf;
  ] in
  let jobs =
    if static then
      let bench_c_perf_static = Filename.concat cdir "bench_c_perf_static" in
      base_jobs @ [ CbackendStatic, job "--backend C --static" perf_f bench_c_perf_static ]
    else base_jobs
  in
  { idx; base_code; cdir; jobs }

(* Phase 1 の結果。まだコンパイルしていない。呼び出し側(Bench_compiler)が
   複数 target 分の prepare をまとめてから、全target分のジョブを1回の
   Bench_builder.compile_all で並列コンパイルする(ML/C側の
   try_prepare_target/compile_targets と同じ「まず全部準備 → まとめて
   1回だけ並列コンパイル」パターンを、target を跨ぐレベルで適用する)。 *)
type grift_prepared = {
  file : string;
  mode_g : string;
  mode_gc : string;
  mode_gcs : string option;      (* grift ネイティブ --static 付きの C backend (static=true のときのみ) *)
  grift_dir : string;
  work : string;
  g : string;
  monotonic_flag : string;
  jsonl_g_path : string;
  jsonl_gc_path : string;
  jsonl_gcs_path : string option;
  prog : Bench_progress.t;
  prepared : grift_prepared_mutant list;
  input_perf : string;
  input_prof : string;
}

(* Phase 1(直列, 準備)のみ行う。grift ソース生成・コンパイルジョブの組み立て・
   jsonl のプレースホルダー行書き込みまでで、Bench_builder.compile_all は
   呼ばない(呼び出し側が複数 target 分をまとめてから1回だけ呼ぶ)。 *)
let prepare ~log_dir ~grift_src ~itr ~static ~file ~ordinal ~total_targets ~monotonic : grift_prepared =
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
  let monotonic_flag = if monotonic then "--monotonic-references" else "" in
  let monotonic_tag = if monotonic then "M" else "G" in
  let mode_g = "GRIFT" ^ monotonic_tag in
  let mode_gc = "GRIFTC" ^ monotonic_tag in
  let grift_dir = Filename.concat log_dir mode_g in
  if not (Sys.file_exists grift_dir) then Sys.mkdir grift_dir 0o755;
  (* Bench_builder.compile_all は <log_dir>/bench/ 配下に Makefile を書く。
     ML/C側(compile_mutants)がこのディレクトリを作っていない場合
     (例: --grift のみ指定して --dynamize/--static を指定しない場合)に
     備えて、ここでも作っておく。 *)
  let bench_dir = Filename.concat log_dir "bench" in
  if not (Sys.file_exists bench_dir) then Sys.mkdir bench_dir 0o755;
  let work = Filename.concat log_dir (Printf.sprintf "grift_work_%s%s%s" file suffix monotonic_tag) in
  if not (Sys.file_exists work) then Sys.mkdir work 0o755;
  let prog =
    Bench_progress.create
      ~label:(Printf.sprintf "%s_%s%s" mode_g file suffix)
      ~total:(List.length subsets) ~ordinal ~total_targets
  in
  (* 全mutant分の grift ソース生成 + コンパイルジョブ組み立て。 *)
  let prepared =
    List.mapi (fun si subset -> prepare_mutant ~work ~g ~monotonic_flag ~itr ~static defs groups si subset) subsets
  in
  let mode_gcs = if static then Some (mode_gc ^ "S") else None in
  (* コンパイル前に、after_mutate 入りのプレースホルダー行(times_sec は空)を
     書いてすぐ閉じておく。ML/C側の compile_mutants (Bench_output 経由) と
     同じパターン — こうしておくと、この後の並列コンパイルや実行(Phase 3)が
     一度も走らない場合(他 target の失敗による [Abort] 等)でも、jsonl が
     0行のまま残ることが無い。Phase 3 が実際に走れば、run_compiled が
     open_out (常に新規truncate) で上書きする。 *)
  List.iter (fun mode_str ->
    let w = Bench_output.open_writer ~log_dir ~mode_str ~file:(file ^ suffix) in
    List.iter (fun p ->
      Bench_output.write_mutant w
        (Bench_output.mutant_json ~mode_str ~idx:p.idx ~after_mutate:p.base_code ~times_sec:[])
    ) prepared;
    Bench_output.close_writer w
  ) ([ mode_g; mode_gc ] @ (match mode_gcs with Some m -> [m] | None -> []));
  (* 実行結果を書く先のパスだけ覚えておく。実際に開く(常に新規truncateする
     open_out で、上のプレースホルダーを上書きする)のは run_compiled の
     冒頭 — Phase 3 が実際に走る場合にのみ、ここで初めて発生する。 *)
  let jsonl_g_path = Printf.sprintf "%s/%s_%s%s.jsonl" log_dir mode_g file suffix in
  let jsonl_gc_path = Printf.sprintf "%s/%s_%s%s.jsonl" log_dir mode_gc file suffix in
  let jsonl_gcs_path = Option.map (fun m -> Printf.sprintf "%s/%s_%s%s.jsonl" log_dir m file suffix) mode_gcs in
  { file; mode_g; mode_gc; mode_gcs; grift_dir; work; g; monotonic_flag;
    jsonl_g_path; jsonl_gc_path; jsonl_gcs_path; prog; prepared; input_perf; input_prof }

let jobs_of_prepared (p : grift_prepared) : Bench_builder.job list =
  List.concat_map (fun m -> List.map snd m.jobs) p.prepared

(* Phase 1 + Phase 2 の結果。まだ実行(計測)はしていない — 呼び出し側
   (Bench_runner)が dynamize/static/grift 全ての compile 結果を見て、
   全て成功している場合にのみ run_compiled を呼ぶことで、grift 側の
   コンパイル失敗が dynamize/static の実行を(逆方向も)妨げるようにする。 *)
type grift_compiled = {
  file : string;
  mode_g : string;
  mode_gc : string;
  mode_gcs : string option;
  grift_dir : string;
  work : string;
  g : string;
  monotonic_flag : string;
  jsonl_g_path : string;
  jsonl_gc_path : string;
  jsonl_gcs_path : string option;
  prog : Bench_progress.t;
  prepared : grift_prepared_mutant list;
  input_perf : string;
  input_prof : string;
  failed : bool;  (* いずれかの mutant のいずれかのジョブが失敗していれば true *)
}

(* Phase 2(全target・全mutant一括, 並列コンパイル)が完了した後に、
   1 target分の成否を判定する。呼び出し側(Bench_compiler.compile_grift)が
   全target分の prepare を集め、jobs_of_prepared で集めたジョブをまとめて
   1回だけ Bench_builder.compile_all した直後に、target ごとにこれを呼ぶ。 *)
let finalize (p : grift_prepared) : grift_compiled =
  let failed =
    List.exists
      (fun m -> List.exists (fun (_, j) -> not (Sys.file_exists j.Bench_builder.out_path)) m.jobs)
      p.prepared
  in
  { file = p.file; mode_g = p.mode_g; mode_gc = p.mode_gc; mode_gcs = p.mode_gcs;
    grift_dir = p.grift_dir; work = p.work;
    g = p.g; monotonic_flag = p.monotonic_flag;
    jsonl_g_path = p.jsonl_g_path; jsonl_gc_path = p.jsonl_gc_path; jsonl_gcs_path = p.jsonl_gcs_path;
    prog = p.prog; prepared = p.prepared; input_perf = p.input_perf; input_prof = p.input_prof; failed }

(* Phase 3 (直列): mutant ごとに実行・計測する。
   compile が完全に終わった後(呼び出し側が dynamize/static/grift 全ての
   コンパイル結果を確認した後)にのみ呼び出すこと。 *)
let run_compiled (c : grift_compiled) : unit =
  (* open_out は常に新規truncateするので、prepare が書いたプレースホルダー
     行はここで上書きされる。 *)
  let oc_g = open_out c.jsonl_g_path in
  let oc_gc = open_out c.jsonl_gc_path in
  let oc_gcs = Option.map open_out c.jsonl_gcs_path in
  List.iter
    (fun p ->
      let find kind = List.assoc kind p.jobs in
      let ok kind = Sys.file_exists (find kind).Bench_builder.out_path in
      if not (ok Perf) then Format.eprintf "[grift compile failed] %s#%d perf@." c.file p.idx;
      if not (ok Prof) then Format.eprintf "[grift compile failed] %s#%d prof@." c.file p.idx;
      if not (ok Cbackend) then Format.eprintf "[grift compile failed] %s#%d c@." c.file p.idx;
      let times =
        if ok Perf then
          match run_bin (find Perf).Bench_builder.out_path c.input_perf with
          | Some o -> parse_times o
          | None -> []
        else []
      in
      let cast, longest =
        if ok Prof then
          match run_bin (find Prof).Bench_builder.out_path c.input_prof with
          | Some o -> parse_prof o
          | None -> (None, None)
        else (None, None)
      in
      let times_c =
        if ok Cbackend then
          match run_bin (find Cbackend).Bench_builder.out_path c.input_perf with
          | Some o -> parse_times o
          | None -> []
        else []
      in
      (match c.mode_gcs, oc_gcs with
       | Some mode_gcs, Some oc_gcs ->
         if not (ok CbackendStatic) then
           Format.eprintf "[grift compile failed] %s#%d c-static@." c.file p.idx;
         let times_cs =
           if ok CbackendStatic then
             match run_bin (find CbackendStatic).Bench_builder.out_path c.input_perf with
             | Some o -> parse_times o
             | None -> []
           else []
         in
         Bench_json.to_channel_ln oc_gcs
           (jrow ~mode:mode_gcs ~idx:p.idx ~after_mutate:p.base_code ~times:times_cs ~cast:None
              ~longest:None)
       | _ -> ());
      (* ログ用に .c を1つ取り出す *)
      let dest_c = Printf.sprintf "%s%d.c" c.file p.idx in
      ignore
        (Sys.command
           (Printf.sprintf "cd %s && %s %s --backend C --keep-ir %s perf.grift > /dev/null 2>&1"
              (Filename.quote p.cdir) c.g c.monotonic_flag (Filename.quote dest_c)));
      (try Sys.rename (Filename.concat p.cdir dest_c) (Filename.concat c.grift_dir dest_c)
       with _ -> ());
      Bench_json.to_channel_ln oc_g
        (jrow ~mode:c.mode_g ~idx:p.idx ~after_mutate:p.base_code ~times ~cast ~longest);
      Bench_json.to_channel_ln oc_gc
        (jrow ~mode:c.mode_gc ~idx:p.idx ~after_mutate:p.base_code ~times:times_c ~cast:None
           ~longest:None);
      Bench_progress.tick c.prog)
    c.prepared;
  Bench_progress.print ~final:true c.prog;
  close_out oc_g;
  close_out oc_gc;
  Option.iter close_out oc_gcs;
  ignore (Sys.command (Printf.sprintf "rm -rf %s" (Filename.quote c.work)))
