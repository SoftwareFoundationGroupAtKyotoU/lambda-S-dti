open Lambda_S_dti
open Bench_target

let check_target ~log_dir ~expected ~ordinal ~total_targets (t : target) : bool =
  let mode_str = ablation_mode_str t in
  try
    let config = Bench_compiler.config_of_target ~file:t.file ~eager:t.eager ~hash:t.hash ~monotonic:t.monotonic ~tvs_opt:t.tvs_opt t.mode in
    let prog = Bench_compiler.compile_mutants ~record:false ~log_dir ~mode_str ~config ~ordinal ~total_targets t in
    let mutants_length = List.length t.mutants in
    let failing = Bench_compiler.build_run_bench_check ~log_dir ~file:t.file ~mode_str ~mutants_length ~config ~expected in
    List.iter (fun (idx, actual) ->
      Format.printf "[FAIL] %s_%s mutant%d: expected %S but got %S@." mode_str t.file idx expected actual)
      failing;
    Bench_progress.print ~final:false prog;
    failing = []
  with
  | e -> Format.eprintf "[Skip] %s: %s@." mode_str (Printexc.to_string e); false

let check_all ~log_dir ~expected targets =
  let total_targets = List.length targets in
  List.mapi (fun i t ->
    check_target ~log_dir ~expected ~ordinal:(i + 1) ~total_targets t
  ) targets
  |> List.for_all (fun ok -> ok)

let () =
  let files = ref [] in
  (* ベンチ(bin/bench.ml)と同じ軸フラグ。fully-optimized 基準値(ALHMT)と、
     立てた軸だけ1つ反転させたターゲットを検査する。1つも立てなければ全軸。 *)
  let axis_specs, requested_axes = Bench_target.axis_specs () in
  let static, dynamize = ref false, ref false in
  let expected = ref None in
  let specs = axis_specs @ [
    ("--static", Arg.Unit (fun () -> static := true), " Check fully-static compilation");
    ("--dynamize", Arg.Unit (fun () -> dynamize := true), " Check mutated (dynamized) programs");
    ("--expected", Arg.String (fun s -> expected := Some s),
     " Expected stdout: every mutant's stdout (per mode) must match this string exactly (required)");
  ]
  in
  Arg.parse specs (fun f -> files := f :: !files)
    " Usage: ./check_mutants.exe <file> --expected <output> [--dynamize] [--static] [--id_opt] [--eagerness] [--hash] [--monotonic] [--tvs_opt] [--typed]";

  let files = !files in
  (match files with
   | [_] -> ()
   | _ ->
     prerr_endline "check_mutants requires exactly one target file (one expected output per run)";
     exit 2);
  let expected = match !expected with
    | Some s -> s
    | None -> prerr_endline "missing --expected <output>"; exit 2
  in
  if not (!dynamize || !static) then begin
    prerr_endline "nothing to do: pass --dynamize and/or --static";
    exit 2
  end;
  let axes = match requested_axes () with [] -> Bench_target.all_axes | axes -> axes in

  let prepared = Bench_target.prepare ~axes files in
  let targets = Bench_target.expand_ablation_targets ~axes prepared in

  let check_tmp_root = ".check_tmp" in
  if not (Sys.file_exists check_tmp_root) then Core_unix.mkdir check_tmp_root;
  let log_dir = Filename.concat check_tmp_root (Printf.sprintf "check_mutants-%d" (Unix.getpid ())) in
  Core_unix.mkdir log_dir;
  at_exit (fun () -> ignore (Sys.command (Printf.sprintf "rm -rf %s" (Filename.quote log_dir))));

  let ok = ref true in
  if !dynamize then
    ok := check_all ~log_dir ~expected (Bench_compiler.dynamize_targets targets) && !ok;
  if !static then
    ok := check_all ~log_dir ~expected
            (Bench_compiler.static_targets (Bench_target.with_static_baselines prepared targets)) && !ok;
  Printf.printf "done\n";
  if not !ok then exit 1
