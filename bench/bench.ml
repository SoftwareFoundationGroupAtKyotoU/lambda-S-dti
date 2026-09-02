open Unix
open Lambda_S_dti
open Bench_lib
open Bench_config
open Bench_target

let () =
  (* benchmark settings *)
  let files, itr = ref [], ref 0 in
  (* evaluation mode *)
  let eagernesses, hash_modes = ref [], ref [] in
  (* benchmark modes *)
  let static, dynamize, grift = ref false, ref false, ref false in
  let specs = [
    ("-i", Arg.Int (fun i -> itr := i), " Specify itration");
    ("--eager", Arg.Unit (fun () -> eagernesses := true :: !eagernesses), " Run eager mode");
    ("--lazy", Arg.Unit (fun () -> eagernesses := false :: !eagernesses), " Run lazy mode");
    ("--hash", Arg.Unit (fun () -> hash_modes := true :: !hash_modes), " Run hash-consing mode");
    ("--no-hash", Arg.Unit (fun () -> hash_modes := false :: !hash_modes), " Run no-hash-consing mode");
    ("--static", Arg.Unit (fun () -> static := true), " Benchmarking fully-static programs");
    ("--dynamize", Arg.Unit (fun () -> dynamize := true), " Benchmarking mutated programs");
    ("--grift", Arg.Unit (fun () -> grift := true), " Benchmarking on grift");
    ("--all", Arg.Unit (fun () -> dynamize := true; static := true; grift := true), " Benchmarking all (--static --dynamize --grift)");
    ("--out", Arg.String (fun s -> Bench_output.out_mode := (match s with
        | "json" -> Bench_output.Json | "jsonl" -> Bench_output.JsonLines
        | _ -> failwith "unknown --out (expected json|jsonl)")), " Output format: json|jsonl (default jsonl)");
    ("--list", Arg.Unit (fun () -> List.iter print_endline all_targets; exit 0), " List benchmark targets and exit");
  ]
  in
  Arg.parse specs (fun f -> files := f :: !files) " Usage: ./bench [file...]";

  (* 指定がなければ全部、あればそれを対象にする *)
  let files = if !files = [] then all_targets else !files in
  let itr = if !itr = 0 then default_itr else !itr in
  let eagernesses = if !eagernesses = [] then [true; false] else !eagernesses in
  let hash_modes = if !hash_modes = [] then [true; false] else !hash_modes in

  (* 1. 前処理: 全ファイルを parse→mutate *)
  Format.fprintf Format.std_formatter "debug: parse->mutate\n";
  let prepared : (string * Syntax.ITGL.program list) list =
    List.map (fun file -> (file, parse_and_mutate file)) files
  in
    Format.fprintf Format.std_formatter "debug: parse->mutate done\n";

  (* モード展開してターゲット配列を作る *)
  Format.fprintf Format.std_formatter "debug: making targets lists\n";
  let targets = Bench_target.expand_targets ~eagernesses ~hash_modes prepared in
  Format.fprintf Format.std_formatter "debug: making targets lists done\n";
  Format.fprintf Format.std_formatter "debug: targets lists number is %d\n" (List.length targets);
  let total_targets = List.length targets in

  (* 2. ログディレクトリ準備 *)
  let tm = localtime (time ()) in
  let timestamp =
    Printf.sprintf "%04d%02d%02d-%02d:%02d:%02d"
      (tm.tm_year + 1900) (tm.tm_mon + 1) tm.tm_mday (tm.tm_hour) (tm.tm_min) (tm.tm_sec)
  in
  let log_base_dir = Bench_config.log_root in
  let log_dir = Printf.sprintf "%s/%s" log_base_dir timestamp in

  if not (Sys.file_exists log_base_dir) then Core_unix.mkdir log_base_dir;
  if not (Sys.file_exists log_dir) then Core_unix.mkdir log_dir;

  (* 3. 実行: 各ターゲットを順番に *)
  Format.fprintf Format.std_formatter "debug: main iteration\n";

  if !dynamize then Bench_runner.run_dynamize ~log_dir ~itr ~total_targets targets;
  if !static then Bench_runner.run_static ~log_dir ~itr ~total_targets targets;
  if !grift then begin
    Format.fprintf Format.std_formatter "debug: grift\n";
    Bench_runner.run_dynamize_grift ~itr ~files;
    if !static then Bench_runner.run_static_grift ~itr ~files
  end;

  Printf.printf "\n";
  Printf.printf "debug: everything was done\n"