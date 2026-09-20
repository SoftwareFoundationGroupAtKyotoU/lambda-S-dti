open Lambda_S_dti
open Bench_target

let check_target ~log_dir ~expected ~ordinal ~total_targets (t : target) : bool =
  let mode_str = full_mode_name t.mode t.eager t.hash t.monotonic in
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

let run_dynamize ~log_dir ~expected targets =
  (* STATIC は dynamize では走らせない。分母にも含めない *)
  let targets = List.filter (fun t -> t.mode <> STATIC) targets in
  let total_targets = List.length targets in
  List.mapi (fun i t ->
    check_target ~log_dir ~expected ~ordinal:(i + 1) ~total_targets t
  ) targets
  |> List.for_all (fun ok -> ok)

let run_static ~log_dir ~expected targets =
  let targets =
    Bench_compiler.dedup_static targets
    |> List.map (fun t -> { t with file = t.file ^ "_fs"; mutants = [List.hd t.mutants] })
  in
  let total_targets = List.length targets in
  List.mapi (fun i t ->
    let t = if t.mode = STATIC then { t with eager = true; hash = false; monotonic = false } else t in
    check_target ~log_dir ~expected ~ordinal:(i + 1) ~total_targets t
  ) targets
  |> List.for_all (fun ok -> ok)

let () =
  let files = ref [] in
  let eagernesses, hash_modes, monotonicities = ref [], ref [], ref [] in
  let static, dynamize = ref false, ref false in
  let expected = ref None in
  let specs = [
    ("--eager", Arg.Unit (fun () -> eagernesses := true :: !eagernesses), " Check eager mode");
    ("--lazy", Arg.Unit (fun () -> eagernesses := false :: !eagernesses), " Check lazy mode");
    ("--hash", Arg.Unit (fun () -> hash_modes := true :: !hash_modes), " Check hash-consing mode");
    ("--no-hash", Arg.Unit (fun () -> hash_modes := false :: !hash_modes), " Check no-hash-consing mode");
    ("--guarded", Arg.Unit (fun () -> monotonicities := false :: !monotonicities), " Check guarded reference semantics");
    ("--monotonic", Arg.Unit (fun () -> monotonicities := true :: !monotonicities), " Check monotonic reference semantics");
    ("--static", Arg.Unit (fun () -> static := true), " Check fully-static compilation");
    ("--dynamize", Arg.Unit (fun () -> dynamize := true), " Check mutated (dynamized) programs");
    ("--expected", Arg.String (fun s -> expected := Some s),
     " Expected stdout: every mutant's stdout (per mode) must match this string exactly (required)");
  ]
  in
  Arg.parse specs (fun f -> files := f :: !files)
    " Usage: ./check_mutants.exe <file> --expected <output> [--dynamize] [--static] [--eager|--lazy] [--hash|--no-hash] [--guarded|--monotonic]";

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
  let eagernesses = if !eagernesses = [] then [true; false] else !eagernesses in
  let hash_modes = if !hash_modes = [] then [true; false] else !hash_modes in
  let monotonicities = if !monotonicities = [] then [true; false] else !monotonicities in

  let prepared : (string * Syntax.ITGL.program list) list =
    List.map (fun file -> (file, Bench_target.parse_and_mutate file)) files
  in
  let targets = Bench_target.expand_targets ~eagernesses ~hash_modes ~monotonicities prepared in

  let check_tmp_root = ".check_tmp" in
  if not (Sys.file_exists check_tmp_root) then Core_unix.mkdir check_tmp_root;
  let log_dir = Filename.concat check_tmp_root (Printf.sprintf "check_mutants-%d" (Unix.getpid ())) in
  Core_unix.mkdir log_dir;
  at_exit (fun () -> ignore (Sys.command (Printf.sprintf "rm -rf %s" (Filename.quote log_dir))));

  let ok = ref true in
  if !dynamize then ok := run_dynamize ~log_dir ~expected targets && !ok;
  if !static then ok := run_static ~log_dir ~expected targets && !ok;
  Printf.printf "done\n";
  if not !ok then exit 1
