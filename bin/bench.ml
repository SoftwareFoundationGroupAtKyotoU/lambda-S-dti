open Lambda_S_dti

let () =
  (* benchmark settings *)
  let files, itr, jobs = ref [], ref 0, ref 0 in
  (* evaluation mode *)
  let eagernesses, hash_modes, monotonicities = ref [], ref [], ref [] in
  (* benchmark modes *)
  let static, dynamize, grift = ref false, ref false, ref false in
  let typed = ref false in
  let specs = [
    ("-i", Arg.Int (fun i -> itr := i), " Specify iteration count");
    ("--jobs", Arg.Int (fun n -> jobs := n),
     " Max parallel compile jobs for --dynamize/--static/--grift (default: nproc-1)");
    ("--eager", Arg.Unit (fun () -> eagernesses := true :: !eagernesses), " Run eager mode");
    ("--lazy", Arg.Unit (fun () -> eagernesses := false :: !eagernesses), " Run lazy mode");
    ("--hash", Arg.Unit (fun () -> hash_modes := true :: !hash_modes), " Run hash-consing mode");
    ("--no-hash", Arg.Unit (fun () -> hash_modes := false :: !hash_modes), " Run no-hash-consing mode");
    ("--guarded", Arg.Unit (fun () -> monotonicities := false :: !monotonicities), " Run guarded reference semantics");
    ("--monotonic", Arg.Unit (fun () -> monotonicities := true :: !monotonicities), " Run monotonic reference semantics");
    ("--typed", Arg.Unit (fun () -> typed := true), " Use samples/src_gradti/typed/ sources instead of untyped/");
    ("--static", Arg.Unit (fun () -> static := true), " Benchmarking fully-static programs");
    ("--dynamize", Arg.Unit (fun () -> dynamize := true), " Benchmarking mutated programs");
    ("--grift", Arg.Unit (fun () -> grift := true), " Benchmarking on grift");
    ("--all", Arg.Unit (fun () -> dynamize := true; static := true; grift := true), " Benchmarking all (--static --dynamize --grift)");
    ("--out", Arg.String (fun s -> Bench_output.out_mode := (match s with
        | "json" -> Bench_output.Json | "jsonl" -> Bench_output.JsonLines
        | _ -> failwith "unknown --out (expected json|jsonl)")), " Output format: json|jsonl (default jsonl)");
    ("--list", Arg.Unit (fun () -> List.iter print_endline Bench_config.all_targets; exit 0), " List benchmark targets and exit");
  ]
  in
  Arg.parse specs (fun f -> files := f :: !files) " Usage: ./bench [file...]";

  (* 指定がなければ全部、あればそれを対象にする *)
  let files = if !files = [] then Bench_config.all_targets else !files in
  let itr = if !itr = 0 then Bench_config.default_itr else !itr in
  let jobs = if !jobs > 0 then !jobs else Bench_builder.default_jobs () in
  let eagernesses = if !eagernesses = [] then [true; false] else !eagernesses in
  let hash_modes = if !hash_modes = [] then [true; false] else !hash_modes in
  let monotonicities = if !monotonicities = [] then [true; false] else !monotonicities in

  (* 1. 前処理: 全ファイルを parse→mutate。対象ソースが存在しない場合は
     （例: untyped/GTP_benchmark/ がまだ無い等）他の対象を巻き込んで
     落ちないよう、[Skip] 警告を出してそのターゲットだけ除外する。 *)
  let prepared : (string * Syntax.ITGL.program list) list =
    List.filter_map (fun file ->
      let path = Bench_config.sample_path ~lang:`Gradti ~typed:!typed file in
      if not (Sys.file_exists path) then begin
        Format.eprintf "[Skip] %s: sample not found (%s)@." file path;
        None
      end else
        Some (file, Bench_target.parse_and_mutate ~typed:!typed file)
    ) files
  in

  (* 2. モード展開してターゲット配列を作る *)
  let targets = Bench_target.expand_targets ~eagernesses ~hash_modes ~monotonicities prepared in

  (* 3. ログディレクトリ準備 *)
  let tm = Unix.localtime (Unix.time ()) in
  let timestamp =
    Printf.sprintf "%04d%02d%02d-%02d:%02d:%02d"
      (tm.Unix.tm_year + 1900) (tm.Unix.tm_mon + 1) tm.Unix.tm_mday
      tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec
  in
  let log_dir = Printf.sprintf "%s/%s" Bench_config.log_root timestamp in
  if not (Sys.file_exists Bench_config.log_root) then Core_unix.mkdir Bench_config.log_root;
  if not (Sys.file_exists log_dir) then Core_unix.mkdir log_dir;

  (* 4. コンパイル: dynamize/static/grift 全てを先に終わらせてから実行する。
     いずれか1つでもコンパイルに失敗したら、他が成功していても
     ベンチマーク実行(Pass 3)は一切行わない。 *)
  let ml_batches =
    (if !dynamize then [ Bench_compiler.compile_dynamize ~log_dir ~itr ~jobs targets ] else []) @
    (if !static then [ Bench_compiler.compile_static ~log_dir ~itr ~jobs targets ] else [])
  in
  let grift_batches =
    if !grift then
      Bench_compiler.compile_dynamize_grift ~log_dir ~itr ~jobs ~files ~monotonicities ::
      (if !static then [ Bench_compiler.compile_static_grift ~log_dir ~itr ~jobs ~files ~monotonicities ] else [])
    else []
  in
  let any_failed =
    List.exists (fun (b : Bench_compiler.compiled_batch) -> b.failed) ml_batches
    || List.exists (fun (b : Bench_compiler.grift_compiled_batch) -> b.failed) grift_batches
  in
  if any_failed then
    Format.eprintf
      "[Abort] compilation failed for one or more targets (dynamize/static/grift); skipping all benchmark execution@."
  else begin
    List.iter Bench_runner.run_batch ml_batches;
    List.iter Bench_runner.run_grift_batch grift_batches
  end;

  if not (!dynamize || !static || !grift) then
    prerr_endline "nothing to do: pass one of --dynamize / --static / --grift / --all";
  Printf.printf "done\n"