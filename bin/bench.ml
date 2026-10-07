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
    ("--cpu", Arg.Int (fun n -> Bench_config.run_cpu := Some n),
     " Pin the measured runs (phase 9) to this CPU with taskset; compilation stays parallel");
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

  if not (!dynamize || !static || !grift) then begin
    prerr_endline "nothing to do: pass one of --dynamize / --static / --grift / --all";
    exit 2
  end;
  (* --cpu の CPU 番号が taskset で使えるか（taskset が有る・番号が範囲内・
     cpuset で許可されている）を、何時間もかかる前処理・コンパイルの前に確かめる *)
  (match !Bench_config.run_cpu with
   | Some n when Sys.command (Bench_config.run_prefix () ^ "true > /dev/null 2>&1") <> 0 ->
     Printf.eprintf "--cpu %d: cannot pin to this CPU with taskset\n" n;
     exit 2
   | _ -> ());

  (* Phase 1〜6: restriction 解決 → ソース存在 → input 存在 → parse →
     スロット対応 → mutate。各フェーズは全対象分のエラーを集め、1件でも
     あればそのフェーズで終了する（Bench_phases 参照）。 *)
  let prepared = Bench_phases.prepare_all ~axes ~dynamize:!dynamize ~static:!static ~grift:!grift files in
  let ml_prepared = Bench_phases.ml_prepared prepared in

  (* ターゲット配列を作る。基準点(ALHMT)はファイルごとに1つしか生成されない
     (=1回しかコンパイル・実行されない)。 *)
  let dynamize_targets = Bench_target.expand_ablation_targets ml_prepared in
  (* --static 用: dynamize_targets に STATIC 基準をファイルごとに1つ足す
     （Bench_target.with_static_baselines 参照） *)
  let static_targets = Bench_target.with_static_baselines ml_prepared dynamize_targets in
  let grift_targets =
    List.concat_map (fun (p : Bench_phases.prepared) ->
      match p.grift with
      | None -> []
      | Some analysis ->
        List.map (fun monotonic ->
          { Bench_compiler.file = p.plan.spec.name; monotonic; analysis; subsets = p.subsets })
          p.plan.grift_monos
    ) prepared
  in

  (* ログディレクトリ準備。ここまでのフェーズはファイルシステムに何も
     書かないので、前処理で落ちた場合に空のログディレクトリは残らない。 *)
  let tm = Unix.localtime (Unix.time ()) in
  let timestamp =
    Printf.sprintf "%04d%02d%02d-%02d:%02d:%02d"
      (tm.Unix.tm_year + 1900) (tm.Unix.tm_mon + 1) tm.Unix.tm_mday
      tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec
  in
  let log_dir = Printf.sprintf "%s/%s" Bench_config.log_root timestamp in
  if not (Sys.file_exists Bench_config.log_root) then Core_unix.mkdir Bench_config.log_root;
  if not (Sys.file_exists log_dir) then Core_unix.mkdir log_dir;

  (* Phase 7: C コード生成（ML 側）/ grift ソース生成。clang はまだ呼ばない。 *)
  let ml_batches, grift_batches =
    Bench_phases.run ~num:7 ~name:"code generation" (fun () ->
      (* OCaml は @ / :: の両辺を右から評価するので、let で順序を固定する *)
      let dyn =
        if !dynamize then
          [ Bench_compiler.prepare_batch ~log_dir ~itr ~label:"dynamize"
              (Bench_compiler.dynamize_targets dynamize_targets) ] else [] in
      let sta =
        if !static then
          [ Bench_compiler.prepare_batch ~log_dir ~itr ~label:"static"
              (Bench_compiler.static_targets static_targets) ] else [] in
      let gr_dyn =
        if !grift then
          [ Bench_compiler.prepare_grift_batch ~log_dir ~itr ~static:false ~label:"grift_dynamize" grift_targets ]
        else [] in
      let gr_sta =
        if !grift && !static then
          [ Bench_compiler.prepare_grift_batch ~log_dir ~itr ~static:true ~label:"grift_static" grift_targets ]
        else [] in
      let ml = dyn @ sta and gr = gr_dyn @ gr_sta in
      ((List.map fst ml, List.map fst gr), List.concat_map snd ml @ List.concat_map snd gr))
  in

  (* Phase 8: clang / grift の並列コンパイル。dynamize/static/grift 全てを
     先に終わらせ、1件でも失敗したらベンチマーク実行は一切行わない。 *)
  let grift_compiled =
    Bench_phases.run ~num:8 ~name:"compile (clang / grift)" (fun () ->
      let ml_errors = List.concat_map (Bench_compiler.compile_batch ~log_dir ~jobs) ml_batches in
      let gr = List.map (Bench_compiler.compile_grift_batch ~log_dir ~jobs) grift_batches in
      (* ↑ let の逐次評価なので ML → grift の順にコンパイルされる *)
      (List.map fst gr, ml_errors @ List.concat_map snd gr))
  in

  (* Phase 9: 計測（直列） *)
  Format.printf "@.=== [Phase 9] run ===@.";
  List.iter Bench_runner.run_batch ml_batches;
  List.iter Bench_runner.run_grift_batch grift_compiled;
  Printf.printf "done\n"
