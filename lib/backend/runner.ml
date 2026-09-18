open Format
open Config

exception Build_bad of string

let build_run c_code ~config = match config.file with
  | Some filename ->
    (* ファイル入力モード *)
    let base = Builder.unique_base config filename in
    let out_path = Filename.concat (Resources.result_c_dir ()) (base ^ "_out.c") in
    let oc = open_out out_path in
    Printf.fprintf oc "%s" c_code;
    close_out oc;
    (* print_debug "Generated C file: %s (Execution delegated)@." out_path *)
    let cmd = Builder.build_clang_cmd ~config ~bench:false ~profile:false () in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad "clang fail";
    let cmd = Filename.concat (Resources.result_dir ()) (base ^ ".out") in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad ".out fail";
    ()
  | None ->
    (* 標準入力モード *)
    let out_path = Filename.concat (Resources.result_c_dir ()) "stdin.c" in
    let oc = open_out out_path in
    Printf.fprintf oc "%s" c_code;
    close_out oc;
    (* print_debug "%s" (Compiler.build_cmd_for_stdin ()); *)
    let cmd = Builder.build_clang_cmd ~config ~bench:false ~profile:false () in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad "clang fail";
    let cmd = Filename.concat (Resources.result_dir ()) "stdin.out" in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad ".out fail";
    ()
