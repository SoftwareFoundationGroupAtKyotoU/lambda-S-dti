(* grift side of the benchmark: parse .grift as S-expressions, number Dyn-able type
   annotations in the same order as Mutate, then write, compile, run and record each variant.
   Output: GRIFTLLVM<M|G>_<file>.jsonl, GRIFTC<M|G>_<file>.jsonl (+ GRIFTC<M|G>S_ for --static). *)

module IntSet = Set.Make (Int)

(* ===================== S 式 ===================== *)

(* S-expression node with a unique id, so specific nodes can be marked for Dyn replacement. *)
type sx = { id : int; k : node }
and node = Atom of string | Lst of sx list

(* Allocate a node with a fresh id. *)
let fresh =
  let c = ref 0 in
  fun k -> incr c; { id = !c; k }

(* Remove ;-comments and split into tokens ("(", ")" and atoms; [ ] are read as ( )). *)
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

(* Parse tokens into a list of top-level S-expressions. *)
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

(* Print back to grift source, writing "Dyn" for every node whose id is in dyn. *)
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

(* mutation 対象外の define 名（entry point） *)
let fixed_names = [ "benchmark" ]

(* Whether the node is the atom s. *)
let atom_is s = function { k = Atom a; _ } -> a = s | _ -> false

(* Split a curried arrow type into [dom1; dom2; ...; final result]. *)
let rec nested_type_slots (s : sx) : sx list =
  match s.k with
  | Lst (a :: op :: b :: _) when atom_is "->" op -> a :: nested_type_slots b
  | _ -> [ s ]

(* grift の define 名を ML 側の識別子に揃える（ハイフン区切り → アンダースコア区切り）。
   例: energy-loop-o ↔ energy_loop_o *)
let ml_name_of_grift (name : string) : string =
  String.map (fun c -> if c = '-' then '_' else c) name

(* [arg : T] 形から T を取り出す *)
let typed_binding_ty (s : sx) : sx option =
  match s.k with
  | Lst (_ :: colon :: ty :: _) when atom_is ":" colon -> Some ty
  | _ -> None

(* First-argument type of every lambda in the body, collected in pre-order (reversed; the caller re-reverses). *)
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

(* Slot groups of one define, in order: argument types, body-lambda arguments,
   then the return type (only when the ML side defines this name with let rec). *)
let slots_of_define ~(fix_names : string list) (d : sx) : sx list list =
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
      (* The i-th body lambda's argument is grouped with the i-th domain of the curried return type. *)
      let lam_groups =
        List.mapi
          (fun i lt -> if i < n_ret - 1 then [ lt; List.nth ret_slots i ] else [ lt ])
          lam_tys
      in
      let is_rec = List.mem (ml_name_of_grift name) fix_names in
      let arg_groups = List.map (fun t -> [ t ]) arg_tys in
      let ret_group =
        if is_rec && n_ret > 0 then [ [ List.nth ret_slots (n_ret - 1) ] ] else []
      in
      arg_groups @ lam_groups @ ret_group
    end
  | _ -> []

(* Keep the top-level define/module/imports forms (these make up the emitted program). *)
let top_defines (forms : sx list) : sx list =
  List.filter
    (fun f -> match f.k with
       | Lst (hd :: _) ->
         (match hd.k with Atom ("define" | "module" | "imports") -> true | _ -> false)
       | _ -> false)
    forms

(* Name of a function define `(define (name args...) ...)`. *)
let define_name (d : sx) : string option =
  match d.k with
  | Lst (hd :: { k = Lst ({ k = Atom n; _ } :: _); _ } :: _) when atom_is "define" hd -> Some n
  | _ -> None

(* Parse a grift source into (top-level forms, slot groups); fails if an ML let rec has no grift define. *)
let analyze_src ~(fix_names : string list) (src : string) : sx list * sx list list =
  let forms = parse_forms (tokenize src) in
  let defs = top_defines forms in
  let grift_funs = List.filter_map (fun d -> Option.map ml_name_of_grift (define_name d)) defs in
  (match List.filter (fun x -> not (List.mem x grift_funs)) fix_names with
   | [] -> ()
   | missing ->
     failwith ("grift: no function define corresponding to ML let rec: "
               ^ String.concat ", " missing));
  (defs, List.concat_map (slots_of_define ~fix_names) defs)

(* ソース解析結果。parse は 1 回だけ行い、グルーピングと serialize で同じ
   ノード（同じ id）を使う。 *)
type analysis = { defs : sx list; groups : sx list list }

(* Parse and number the slots of a grift source (called once per file in the parse phase). *)
let analyze ~fix_names (src : string) : analysis =
  let defs, groups = analyze_src ~fix_names src in
  { defs; groups }

(* Number of slots; must equal the untyped ML slot count. *)
let n_slots (a : analysis) : int = List.length a.groups

(* grift source of one variant: the slot groups in subset (1-based) become Dyn. *)
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

(* Debug helper: parse src and render one variant (currently not called anywhere). *)
let render_variant ~fix_names (src : string) (subset : int list) : string =
  let defs, groups = analyze_src ~fix_names src in
  serialize_variant defs groups subset

(* ===================== grift 実行 ===================== *)

(* Whole-file read / write helpers. *)
let read_file p =
  let ic = open_in_bin p in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

let write_file p s =
  let oc = open_out p in output_string oc s; close_out oc

(* grift code appended to each variant: run (benchmark) warmup times untimed, then
   (time (benchmark)) loop_count times. Each run reads one copy of the input. *)
let driver_code ~(warmup : int) (loop_count : int) : string =
  Printf.sprintf
    "\n;; --- Auto-generated Loop Driver ---\n\
     (define (run-warmup-loop [k : Int]) : Unit\n\
    \  (if (<= k 0)\n\
    \      ()\n\
    \      (begin\n\
    \        (benchmark)\n\
    \        (run-warmup-loop (- k 1)))))\n\
     (define (run-benchmark-loop [k : Int]) : Unit\n\
    \  (if (<= k 0)\n\
    \      ()\n\
    \      (begin\n\
    \        (time (benchmark))\n\
    \        (run-benchmark-loop (- k 1)))))\n\
     (run-warmup-loop %d)\n\
     (run-benchmark-loop %d)\n"
    warmup loop_count

(* The numeric token after each occurrence of marker. *)
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

(* Per-iteration times printed by grift's `time` ("time (sec): ..."). *)
let parse_times (out : string) : float list =
  numbers_after "time (sec):" out |> List.filter_map float_of_string_opt

(* Rest of the line after the first occurrence of sub. *)
let substr_after (sub : string) (line : string) : string option =
  let m = String.length sub and n = String.length line in
  let rec find i =
    if i + m > n then None
    else if String.sub line i m = sub then Some (String.sub line (i + m) (n - i - m))
    else find (i + 1)
  in
  find 0

(* All integer tokens in s (space- or tab-separated). *)
let ints_of (s : string) : int list =
  s
  |> String.split_on_char ' '
  |> List.concat_map (String.split_on_char '\t')
  |> List.filter_map int_of_string_opt

(* (total casts, longest proxy chain) from --cast-profiler output. *)
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

(* Run a binary with stdin_data (via a temp file) and return its stdout; None if the binary is missing. *)
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

(* One JSONL record in the same schema as the ML side (Bench_output.mutant_json). *)
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

(* ---- Parallel compilation: every grift compile goes through Bench_builder's make -j;
   the binaries are then run one at a time. ---- *)
(* Binaries per variant: Perf = default (LLVM) backend timing, Prof = C backend + cast profiler,
   Cbackend = C backend timing, CbackendStatic = C backend with --static (only for --static). *)
type grift_job_kind = Perf | Prof | Cbackend | CbackendStatic

(* One variant: its source (for after_mutate), its work directory, and its compile jobs. *)
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
let prepare_mutant ~work ~g ~monotonic_flag ~heap_kb ~itr ~static defs groups si subset : grift_prepared_mutant =
  let idx = si + 1 in
  let base_code = serialize_variant defs groups subset in
  let cdir = Printf.sprintf "%s/config_%d" work idx in
  if not (Sys.file_exists cdir) then Sys.mkdir cdir 0o755;
  let perf_f = Filename.concat cdir "perf.grift" in
  let prof_f = Filename.concat cdir "prof.grift" in
  write_file perf_f (base_code ^ driver_code ~warmup:Bench_config.warmup itr);
  (* The cast profiler counts over the whole process, so prof runs the benchmark once. *)
  write_file prof_f (base_code ^ driver_code ~warmup:0 1);
  (* Compile job: grift -O 3 -m <heap KB> [monotonic] <extra flags> -o out src, with TMPDIR=cdir. *)
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
      Printf.sprintf "TMPDIR=%s %s -O 3 -m %d %s %s -o %s %s > /dev/null 2>&1"
        (Filename.quote cdir) g heap_kb monotonic_flag extra
        (Filename.quote out) (Filename.quote src)
    in
    { Bench_builder.out_path = out; cmd }
  in
  let bench_perf = Filename.concat cdir "bench_perf" in
  let bench_prof = Filename.concat cdir "bench_prof" in
  let bench_c_perf = Filename.concat cdir "bench_c_perf" in
  let base_jobs = [
    Perf,     job ""                 perf_f bench_perf;
    (* cast 数・longest proxy chain は比較の主対象である C バックエンドで計測する *)
    Prof,     job "--backend C --cast-profiler" prof_f bench_prof;
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
  mode_gl : string;
  mode_gc : string;
  mode_gcs : string option;      (* grift ネイティブ --static 付きの C backend (static=true のときのみ) *)
  grift_dir : string;
  work : string;
  g : string;
  monotonic_flag : string;
  heap_kb : int;
  jsonl_gl_path : string;
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
let prepare ~heap_size ~log_dir ~itr ~static ~file ~ordinal ~total_targets ~monotonic
    ~(analysis : analysis) ~(subsets : int list list) : grift_prepared =
  let input_path = Bench_config.input_path ~static file in
  let { defs; groups } = analysis in
  (* subsets は ML 側（untyped）と共有する部分集合列（Mutate.subsets_auto）。
     スロット数が ML 側と一致することはスロット対応検査フェーズで確認済みなので、
     同じ mutant_index が同じスロット選択を指す。 *)
  let subsets = if static then [ [] ] else subsets in
  (* grift binaries read input once per run (warm-up runs included), so repeat it (+10 spare copies). *)
  let base_input = String.trim (read_file input_path) in
  let repeat k = String.concat "" (List.init k (fun _ -> base_input ^ "\n")) in
  let input_perf = repeat (Bench_config.warmup + itr + 10) in
  let input_prof = repeat (1 + 10) in
  let suffix = if static then "_fs" else "" in
  let g = Bench_config.grift_cmd in
  let monotonic_flag = if monotonic then "--monotonic-references" else "" in
  (* grift の -m (--start-memory) は KB 単位で、生成 C の GC_INITIAL_HEAP_SIZE
     (LLVM バックエンドでは clang の -D) になる。ML 側 (Builder の
     -D GC_INITIAL_HEAP_SIZE) と同じ初期 heap にそろえる。1024 の倍数である
     ことは bin/bench.ml の --heap-size 解析で保証している。 *)
  let heap_kb = heap_size / 1024 in
  let monotonic_tag = if monotonic then "M" else "G" in
  let mode_gl = "GRIFTLLVM" ^ monotonic_tag in
  let mode_gc = "GRIFTC" ^ monotonic_tag in
  (* ログ用に取り出す .c は C バックエンドの出力なので GRIFTC<M|G>/ に置く *)
  let grift_dir = Filename.concat log_dir mode_gc in
  if not (Sys.file_exists grift_dir) then Sys.mkdir grift_dir 0o755;
  (* Bench_builder.compile_all は <log_dir>/bench/ 配下に Makefile を書く。
     ML/C側(compile_mutants)がこのディレクトリを作っていない場合
     (例: --grift のみ指定して --dynamize/--static を指定しない場合)に
     備えて、ここでも作っておく。 *)
  let bench_dir = Filename.concat log_dir "bench" in
  if not (Sys.file_exists bench_dir) then Sys.mkdir bench_dir 0o755;
  let work = Filename.concat log_dir (Printf.sprintf "grift_work_%s%s%s" file suffix monotonic_tag) in
  if not (Sys.file_exists work) then Sys.mkdir work 0o755;
  (* 1本の進捗バーで C / LLVM 両バックエンドの実行を数えるので両方の名前を出す *)
  let prog =
    Bench_progress.create
      ~label:(Printf.sprintf "%s+%s_%s%s" mode_gc mode_gl file suffix)
      ~total:(List.length subsets) ~ordinal ~total_targets
  in
  (* 全mutant分の grift ソース生成 + コンパイルジョブ組み立て。 *)
  let prepared =
    List.mapi (fun si subset -> prepare_mutant ~work ~g ~monotonic_flag ~heap_kb ~itr ~static defs groups si subset) subsets
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
  ) ([ mode_gl; mode_gc ] @ (match mode_gcs with Some m -> [m] | None -> []));
  (* 実行結果を書く先のパスだけ覚えておく。実際に開く(常に新規truncateする
     open_out で、上のプレースホルダーを上書きする)のは run_compiled の
     冒頭 — Phase 3 が実際に走る場合にのみ、ここで初めて発生する。 *)
  let jsonl_gl_path = Printf.sprintf "%s/%s_%s%s.jsonl" log_dir mode_gl file suffix in
  let jsonl_gc_path = Printf.sprintf "%s/%s_%s%s.jsonl" log_dir mode_gc file suffix in
  let jsonl_gcs_path = Option.map (fun m -> Printf.sprintf "%s/%s_%s%s.jsonl" log_dir m file suffix) mode_gcs in
  { file; mode_gl; mode_gc; mode_gcs; grift_dir; work; g; monotonic_flag; heap_kb;
    jsonl_gl_path; jsonl_gc_path; jsonl_gcs_path; prog; prepared; input_perf; input_prof }

(* Every compile job of every variant of a target. *)
let jobs_of_prepared (p : grift_prepared) : Bench_builder.job list =
  List.concat_map (fun m -> List.map snd m.jobs) p.prepared

(* Phase 1 + Phase 2 の結果。まだ実行(計測)はしていない — 呼び出し側
   (Bench_runner)が dynamize/static/grift 全ての compile 結果を見て、
   全て成功している場合にのみ run_compiled を呼ぶことで、grift 側の
   コンパイル失敗が dynamize/static の実行を(逆方向も)妨げるようにする。 *)
type grift_compiled = {
  file : string;
  mode_gl : string;
  mode_gc : string;
  mode_gcs : string option;
  grift_dir : string;
  work : string;
  g : string;
  monotonic_flag : string;
  heap_kb : int;
  jsonl_gl_path : string;
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
  { file = p.file; mode_gl = p.mode_gl; mode_gc = p.mode_gc; mode_gcs = p.mode_gcs;
    grift_dir = p.grift_dir; work = p.work;
    g = p.g; monotonic_flag = p.monotonic_flag; heap_kb = p.heap_kb;
    jsonl_gl_path = p.jsonl_gl_path; jsonl_gc_path = p.jsonl_gc_path; jsonl_gcs_path = p.jsonl_gcs_path;
    prog = p.prog; prepared = p.prepared; input_perf = p.input_perf; input_prof = p.input_prof; failed }

(* Phase 3 (直列): mutant ごとに実行・計測する。
   compile が完全に終わった後(呼び出し側が dynamize/static/grift 全ての
   コンパイル結果を確認した後)にのみ呼び出すこと。 *)
let run_compiled (c : grift_compiled) : unit =
  (* open_out は常に新規truncateするので、prepare が書いたプレースホルダー
     行はここで上書きされる。 *)
  let oc_gl = open_out c.jsonl_gl_path in
  let oc_gc = open_out c.jsonl_gc_path in
  let oc_gcs = Option.map open_out c.jsonl_gcs_path in
  List.iter
    (fun p ->
      (* Job of the given kind, and whether its binary was built. *)
      let find kind = List.assoc kind p.jobs in
      let ok kind = Sys.file_exists (find kind).Bench_builder.out_path in
      if not (ok Perf) then Format.eprintf "[grift compile failed] %s#%d llvm@." c.file p.idx;
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
      (* Recompile with --keep-ir to keep the generated .c, and move it to <log_dir>/GRIFTC<M|G>/. *)
      (* ログ用に .c を1つ取り出す *)
      let dest_c = Printf.sprintf "%s%d.c" c.file p.idx in
      ignore
        (Sys.command
           (Printf.sprintf "cd %s && %s -m %d %s --backend C --keep-ir %s perf.grift > /dev/null 2>&1"
              (Filename.quote p.cdir) c.g c.heap_kb c.monotonic_flag (Filename.quote dest_c)));
      (try Sys.rename (Filename.concat p.cdir dest_c) (Filename.concat c.grift_dir dest_c)
       with _ -> ());
      Bench_json.to_channel_ln oc_gl
        (jrow ~mode:c.mode_gl ~idx:p.idx ~after_mutate:p.base_code ~times ~cast:None ~longest:None);
      Bench_json.to_channel_ln oc_gc
        (jrow ~mode:c.mode_gc ~idx:p.idx ~after_mutate:p.base_code ~times:times_c ~cast ~longest);
      Bench_progress.tick c.prog)
    c.prepared;
  Bench_progress.print ~final:true c.prog;
  close_out oc_gl;
  close_out oc_gc;
  Option.iter close_out oc_gcs;
  ignore (Sys.command (Printf.sprintf "rm -rf %s" (Filename.quote c.work)))
