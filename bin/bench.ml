open Lambda_S_dti

let () =
  (* benchmark settings *)
  let files, itr, jobs = ref [], ref 0, ref 0 in
  (* 軸別アブレーションフラグ: 立てた軸だけ、fully-optimized 基準値(ALHMT)
     から1つ反転させた2点比較を行う。複数指定しても軸間の直積は取らない。 *)
  let axis_specs, requested_axes = Bench_target.axis_specs () in
  (* benchmark modes *)
  let static, dynamize, grift = ref false, ref false, ref false in
  let specs = [
    ("-i", Arg.Int (fun i -> itr := i), " Specify iteration count");
    ("--jobs", Arg.Int (fun n -> jobs := n),
     " Max parallel compile jobs for --dynamize/--static/--grift (default: nproc-1)");
  ] @ axis_specs @ [
    ("--static", Arg.Unit (fun () -> static := true), " Benchmarking fully-static programs");
    ("--dynamize", Arg.Unit (fun () -> dynamize := true), " Benchmarking mutated programs");
    ("--grift", Arg.Unit (fun () -> grift := true),
     " Benchmarking against GRIFT's C backend (GRIFTCM vs our own fully-optimized ALHMT config)");
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
  let axes = requested_axes () in

  (* 1. 前処理: 全ファイルを parse→mutate（Bench_target.prepare 参照） *)
  let prepared = Bench_target.prepare ~axes files in

  (* 2. ターゲット配列を作る。expand_ablation_targets は要求された axes を
     まとめて一度だけ受け取るので、複数の軸フラグを同時指定しても
     fully-optimized 基準点(ALHMT)はファイルごとに1つしか生成されない
     (=1回しかコンパイル・実行されない)。 *)
  let dynamize_targets = Bench_target.expand_ablation_targets ~axes prepared in
  (* --static 用: dynamize_targets に STATIC 基準をファイルごとに1つ足す
     （Bench_target.with_static_baselines 参照） *)
  let static_targets = Bench_target.with_static_baselines prepared dynamize_targets in

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
    (if !dynamize then [ Bench_compiler.compile_dynamize ~log_dir ~itr ~jobs dynamize_targets ] else []) @
    (if !static then [ Bench_compiler.compile_static ~log_dir ~itr ~jobs static_targets ] else [])
  in
  let grift_batches =
    if !grift then
      (* --grift は軸フラグの有無に関わらず、fully-optimized 基準値の
         monotonic=true(ALHMT の M)側のみで GRIFTCM と比較する独立した計測。 *)
      Bench_compiler.compile_dynamize_grift ~log_dir ~itr ~jobs ~files ~monotonicities:[true] ::
      (if !static then [ Bench_compiler.compile_static_grift ~log_dir ~itr ~jobs ~files ~monotonicities:[true] ] else [])
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
