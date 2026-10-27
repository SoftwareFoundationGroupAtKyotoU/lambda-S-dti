(* コンパイル済みの target を実行・計測するモジュール。コード生成・
   並列コンパイルは Bench_compiler の役目。 *)

(* Run the timing binary, then the profiling binary, of one compiled target.
   Each binary updates its target's JSONL file itself. Raises on non-zero exit. *)
let run_bench_binaries (j : Bench_compiler.bench_job) =
  Format.fprintf Format.std_formatter "%s@." j.run_cmd;
  let i = Sys.command j.run_cmd in
  if i != 0 then raise @@ Runner.Build_bad ".out(for time) fail";
  Format.fprintf Format.std_formatter "%s@." j.profile_run_cmd;
  let i = Sys.command j.profile_run_cmd in
  if i != 0 then raise @@ Runner.Build_bad ".out(for profile) fail"

(* Measure one target; a runtime failure is reported as [Skip] and does not stop the others. *)
let run_measured (p : Bench_compiler.prepared_target) =
  try run_bench_binaries p.b
  with e -> Format.eprintf "[Skip] %s: %s@." p.mode_str (Printexc.to_string e)

(* Measure every target of an ML-side batch (dynamize or static), one after another. *)
let run_batch (b : Bench_compiler.batch) =
  List.iter run_measured b.targets

(* GRIFT側: コンパイル済みの grift target を1つずつ直列に実行・計測する。
   コンパイル(Bench_compiler.compile_grift 等)は Bench_compiler の役目。 *)
let run_grift_batch (b : Bench_compiler.grift_compiled_batch) =
  List.iter Bench_grift.run_compiled b.compiled
