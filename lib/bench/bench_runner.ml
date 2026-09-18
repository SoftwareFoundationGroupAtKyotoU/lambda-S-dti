(* コンパイル済みの target を実行・計測するモジュール。コード生成・
   並列コンパイルは Bench_compiler の役目。 *)

(* Pass 3: コンパイルが成功した target のみ、1 つずつ直列に実行・計測する。
   Pass 2（並列コンパイル、Bench_compiler.compile_targets）が完全に終わった
   後にしか呼ばれないので、実行中に他 target のコンパイルが裏で走っている
   ことは無い。 *)
let run_bench_binaries (j : Bench_compiler.bench_job) =
  Format.fprintf Format.std_formatter "%s@." j.run_cmd;
  let i = Sys.command j.run_cmd in
  if i != 0 then raise @@ Runner.Build_bad ".out(for time) fail";
  Format.fprintf Format.std_formatter "%s@." j.profile_run_cmd;
  let i = Sys.command j.profile_run_cmd in
  if i != 0 then raise @@ Runner.Build_bad ".out(for profile) fail"

let run_measured (p : Bench_compiler.prepared_target) =
  try run_bench_binaries p.b
  with e -> Format.eprintf "[Skip] %s: %s@." p.mode_str (Printexc.to_string e)

let run_batch (b : Bench_compiler.compiled_batch) =
  List.iter run_measured b.succeeded

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
