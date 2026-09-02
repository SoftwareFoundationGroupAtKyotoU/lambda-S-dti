open Lambda_S_dti
open Bench_target

let config_of_target ~file ~eager ~hash = function
  | S      -> Config.create ~eager ~hash ~file:(Some file) ~compile:true ()
  | A      -> Config.create ~eager ~hash ~file:(Some file) ~alt:true ~compile:true ()
  | B      -> Config.create ~eager ~hash ~file:(Some file) ~intoB:true ~compile:true ()
  | STATIC -> Config.create ~eager ~hash ~file:(Some file) ~static:true ~compile:true ()

(* -------- 1ファイル × 1モード（ターゲット）を実行 ------------------ *)
let run_target ~log_dir ~itr ~ordinal ~total_targets (t : target) =
  let mode_str = full_mode_name t.mode t.eager t.hash in
  try
    let config = config_of_target ~file:t.file ~eager:t.eager ~hash:t.hash t.mode in
    Format.fprintf Format.std_formatter "debug: bench_file_mode\n";
    let writer = Bench_output.open_writer ~log_dir ~mode_str ~file:t.file in
    let ppf = Utils.Format.empty_formatter in
    let null_fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
    (* ターゲット用 Progress を開始 *)
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
        let initial_state = { (Pipeline.init_state () ~config) with Pipeline.program = p } in
        (* --- Compilation --- *)
        let c_code = 
          initial_state
          |> Pipeline.typing_ITGL ppf
          |> Pipeline.translate_to_CC ppf ~config ~bench_ppf:null_fmt ~bench:idx
          |> Pipeline.kNorm_funs ppf ~config
          |> Pipeline.closure ppf ~config
          |> Pipeline.toC ppf ~config ~bench:idx
        in
        (* write c_code in c file *)
        let filename = Format.asprintf "%s/%s/%s_%d.c" log_dir mode_str t.file idx in
        let oc = open_out filename in
        Printf.fprintf oc "%s" c_code;
        close_out oc;
        (* write mutant information in json file *)
        Bench_output.write_mutant writer
          (Bench_output.mutant_json ~mode_str ~idx
             ~after_mutate:after_mutate_str ~times_sec:[]);
        Bench_progress.tick prog (* ← 変異1件完了ごとに更新 *)
      with e ->
        Format.fprintf Format.std_formatter "\n[Error] %s some error raised in compilation: %s@." t.file (Printexc.to_string e);
        Format.fprintf Format.std_formatter "DEBUG mutant %d:\n%a@." i Pp.ITGL.pp_program p
    ) t.mutants;
    Bench_output.close_writer writer;
    Builder.build_run_bench ~log_dir ~file:t.file ~mode_str ~itr ~mutants_length:(List.length t.mutants) ~config;
    Bench_progress.print ~final:false prog
  with Failure msg -> Format.eprintf "[Skip] %s@." msg

let run_dynamize ~log_dir ~itr ~total_targets targets =
  List.iteri (fun i t -> 
    if t.mode <> STATIC then run_target ~log_dir ~itr ~ordinal:(i + 1) ~total_targets t
  ) targets

let run_static ~log_dir ~itr ~total_targets targets =
  let targets = List.map (fun t -> { t with file = t.file ^ "_fs"; mutants = [List.hd t.mutants] }) targets in
  List.iteri (fun i t ->
    let t = if t.mode = STATIC then { t with eager = true; hash = false } else t in
    run_target ~log_dir ~itr ~ordinal:(i+1) ~total_targets t
  ) targets

let run_grift ~itr ~static ~files =
  let go ~fs file =
    let grift_path = Bench_config.sample_path ~lang:`Grift file in
    if not (Sys.file_exists grift_path) then
      Format.eprintf "[Skip grift] %s: %s not found@." file grift_path
    else
      let input_path = Bench_config.input_path ~fs file in
      let static_flag = if fs then " --static" else "" in
      let cmd = Format.asprintf "python3 benchC/run_grift.py %s %s%s -i %d" grift_path input_path static_flag itr in
      if Sys.command cmd <> 0 then failwith (Printf.sprintf "python grift%s" static_flag)
  in
  List.iter (go ~fs:static) files

let run_dynamize_grift ~itr ~files = run_grift ~itr ~static:false ~files

let run_static_grift ~itr ~files = run_grift ~itr ~static:true ~files