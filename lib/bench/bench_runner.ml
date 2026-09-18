open Bench_target

let config_of_target ~file ~eager ~hash ~monotonic = function
  | S      -> Config.create ~eager ~hash ~monotonic ~file:(Some file) ~compile:true ()
  | A      -> Config.create ~eager ~hash ~monotonic ~file:(Some file) ~alt:true ~compile:true ()
  | B      -> Config.create ~eager ~hash ~file:(Some file) ~intoB:true ~compile:true ()
  | STATIC -> Config.create ~eager ~hash ~monotonic ~file:(Some file) ~static:true ~compile:true ()

(* -------- 1ファイル×1モード分の mutant を全て C にコンパイルし、
   log_dir/mode_str/ 以下に .c ファイルとして書き出す。ベンチ実行（run_target）と
   正当性チェック（test/check_mutants.ml）の両方から共有される前処理。
   ?record（デフォルト true）: mutant ごとの after_mutate 等を記録した .jsonl を
   書くかどうか。この記録はベンチ結果の一部であって、正当性チェックには不要な
   ので、test/check_mutants.ml からは false を渡して余分なファイル書き込みを
   避ける。 *)
let compile_mutants ?(record=true) ~log_dir ~mode_str ~config ~ordinal ~total_targets (t : target) : Bench_progress.t =
  let writer = if record then Some (Bench_output.open_writer ~log_dir ~mode_str ~file:t.file) else None in
  let ppf = Utils.Format.empty_formatter in
  let null_fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
  let label = Printf.sprintf "%s_%s" mode_str t.file in
  let prog = Bench_progress.create ~label ~total:(List.length t.mutants) ~ordinal ~total_targets in
  let c_dir = Printf.sprintf "%s/%s" log_dir mode_str in
  if not (Sys.file_exists c_dir) then Core_unix.mkdir c_dir;
  let bench_dir = Printf.sprintf "%s/bench" log_dir in
  if not (Sys.file_exists bench_dir) then Core_unix.mkdir bench_dir;
  List.iteri (fun i p ->
    try
      let idx = i + 1 in
      let after_mutate_str = Format.asprintf "%a" Pp.ITGL.pp_program p in
      let initial_state = Pipeline.init_state p ~config in
      (* --- Compilation --- *)
      let c_code =
        initial_state
        |> Pipeline.typing_ITGL ppf (* save ty in state *)
        |> Pipeline.translate_to_CC ppf ~config ~bench_ppf:null_fmt ~bench:idx |> fst
        |> Pipeline.kNorm_funs ppf ~config
        |> Pipeline.closure ppf ~config
        |> Pipeline.toC ppf ~config ~bench:idx
      in
      (* write c_code in c file *)
      let filename = Format.asprintf "%s/%s/%s_%d.c" log_dir mode_str t.file idx in
      let oc = open_out filename in
      Printf.fprintf oc "%s" c_code;
      close_out oc;
      (* write mutant information in json file (record=true のときのみ) *)
      (match writer with
       | Some w ->
         Bench_output.write_mutant w
           (Bench_output.mutant_json ~mode_str ~idx
              ~after_mutate:after_mutate_str ~times_sec:[])
       | None -> ());
      Bench_progress.tick prog (* ← 変異1件完了ごとに更新 *)
    with e ->
      Format.fprintf Format.std_formatter "\n[Error] %s some error raised in compilation: %s@." t.file (Printexc.to_string e);
      Format.fprintf Format.std_formatter "DEBUG mutant %d:\n%a@." i Pp.ITGL.pp_program p
  ) t.mutants;
  (match writer with Some w -> Bench_output.close_writer w | None -> ());
  prog

(* -------- 1ファイル × 1モード（ターゲット）を実行 ------------------ *)
let run_target ~log_dir ~itr ~ordinal ~total_targets (t : target) =
  let mode_str = full_mode_name t.mode t.eager t.hash t.monotonic in
  try
    let config = config_of_target ~file:t.file ~eager:t.eager ~hash:t.hash ~monotonic:t.monotonic t.mode in
    let prog = compile_mutants ~log_dir ~mode_str ~config ~ordinal ~total_targets t in
    Builder.build_run_bench ~log_dir ~file:t.file ~mode_str ~itr ~mutants_length:(List.length t.mutants) ~config;
    Bench_progress.print ~final:false prog
  with
  | e -> Format.eprintf "[Skip] %s: %s@." mode_str (Printexc.to_string e)

let run_dynamize ~log_dir ~itr targets =
  (* STATIC は dynamize では走らせない。分母にも含めない *)
  let targets = List.filter (fun t -> t.mode <> STATIC) targets in
  let total_targets = List.length targets in
  List.iteri (fun i t ->
    run_target ~log_dir ~itr ~ordinal:(i + 1) ~total_targets t
  ) targets

(* STATIC モードは config が eager=true / hash=false に固定されるため、
   eager×hash の 4 通りは同一の実行になる。ファイルごとに 1 つへ畳む。 *)
let dedup_static (targets : target list) : target list =
  let seen = Hashtbl.create 16 in
  List.filter (fun t ->
    match t.mode with
    | STATIC ->
      if Hashtbl.mem seen t.file then false
      else (Hashtbl.add seen t.file (); true)
    | _ -> true
  ) targets

let run_static ~log_dir ~itr targets =
  let targets =
    dedup_static targets
    |> List.map (fun t -> { t with file = t.file ^ "_fs"; mutants = [List.hd t.mutants] })
  in
  let total_targets = List.length targets in
  List.iteri (fun i t ->
    let t = if t.mode = STATIC then { t with eager = true; hash = false; monotonic = false } else t in
    run_target ~log_dir ~itr ~ordinal:(i+1) ~total_targets t
  ) targets

let run_grift ~log_dir ~itr ~static ~files ~monotonicities =
  let targets = Bench_target.restrict_grift_targets ~monotonicities files in
  let total_targets = List.length targets in
  List.iteri (fun i (file, monotonic) ->
    let grift_src = Bench_config.sample_path ~lang:`Grift file in
    if not (Sys.file_exists grift_src) then
      Format.eprintf "[Skip grift] %s: %s not found@." file grift_src
    else
      try
        Bench_grift.run ~log_dir ~grift_src ~itr ~static ~file ~monotonic
          ~ordinal:(i + 1) ~total_targets
      with e -> Format.eprintf "[Skip grift] %s: %s@." file (Printexc.to_string e)
  ) targets

let run_dynamize_grift ~log_dir ~itr ~files ~monotonicities =
  run_grift ~log_dir ~itr ~static:false ~files ~monotonicities

let run_static_grift ~log_dir ~itr ~files ~monotonicities =
  run_grift ~log_dir ~itr ~static:true ~files ~monotonicities