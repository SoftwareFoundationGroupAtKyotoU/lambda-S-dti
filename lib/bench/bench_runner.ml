(* コンパイル済みの target を実行・計測するモジュール。コード生成・
   並列コンパイルは Bench_compiler の役目。 *)

(* Pass 3: コンパイルが成功した target のみ、1 つずつ直列に実行・計測する。
   コンパイルフェーズ（並列コンパイル、Bench_compiler.compile_batch）が完全に終わった
   後にしか呼ばれないので、実行中に他 target のコンパイルが裏で走っている
   ことは無い。 *)
let run_bench_binaries (j : Bench_compiler.bench_job) =
  let run_cmd = Bench_config.run_prefix () ^ j.run_cmd in
  let profile_run_cmd = Bench_config.run_prefix () ^ j.profile_run_cmd in
  Format.fprintf Format.std_formatter "%s@." run_cmd;
  let i = Sys.command run_cmd in
  if i != 0 then raise @@ Runner.Build_bad ".out(for time) fail";
  Format.fprintf Format.std_formatter "%s@." profile_run_cmd;
  let i = Sys.command profile_run_cmd in
  if i != 0 then raise @@ Runner.Build_bad ".out(for profile) fail"

let run_measured (p : Bench_compiler.prepared_target) =
  try run_bench_binaries p.b
  with e -> Format.eprintf "[Skip] %s: %s@." p.mode_str (Printexc.to_string e)

let run_batch (b : Bench_compiler.batch) =
  List.iter run_measured b.targets

(* GRIFT側: コンパイル済みの grift target を1つずつ直列に実行・計測する。
   コンパイル(Bench_compiler.compile_grift 等)は Bench_compiler の役目。 *)
let run_grift_batch (b : Bench_compiler.grift_compiled_batch) =
  List.iter Bench_grift.run_compiled b.compiled
