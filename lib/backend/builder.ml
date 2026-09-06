open Format
open Config
open Syntax.C

exception Build_bad of string

let gc_ini_heap_var = "-D GC_INITIAL_HEAP_SIZE=1048576 "

let unique_base (config : Config.t) filename =
  let base = Filename.basename filename in
  let abs_filename =
    if Filename.is_relative filename then Filename.concat (Sys.getcwd ()) filename
    else filename
  in
  let mode_key = Printf.sprintf "%b_%b_%b_%b_%b_%b"
    config.intoB config.static config.eager config.alt config.monotonic config.hash
  in
  base ^ "_" ^ Digest.to_hex (Digest.string (abs_filename ^ mode_key))

let build_clang_cmd ?(log_dir="") ?(file="") ?(mode_str="") ?(src_files="")
  ~config ~bench ~profile () =
  let libc_dir = Resources.libc_dir () in
  let intoB = config.intoB in
  let static = config.static in
  let eager = config.eager in
  let alt = config.alt in
  let monotonic = config.monotonic in
  let hash = config.hash in
  let mode_var = (if intoB && not static then "-D CAST " else if alt && not static then "-D ALT " else "") in
  let eager_var = (if eager && not static then "-D EAGER " else "") in
  let monotonic_var = (if monotonic then "-D MONOTONIC " else "") in
  let hash_var = (if hash && not static then "-D HASH " else "") in
  let static_var = (if static then "-D STATIC " else "") in
  let profile_var = (if profile then "-D PROFILE " else "") in
  if bench then
    let bench_opt_level = "-O3" in
    asprintf "clang %s/bench/%s%s%s.c %s%s%s%s%s%s%slibC/*.c benchC/bench_json.c %s -o %s/bench/%s%s%s.out -lgc -lcjson %s" (* -flto *) (* -falign-functions=32 -falign-loops=32 -falign-jumps=32 *)
      log_dir
      file
      mode_str
      (if profile then "_profile" else "")
      gc_ini_heap_var
      mode_var
      eager_var
      monotonic_var
      hash_var
      static_var
      profile_var
      src_files
      log_dir
      file
      mode_str
      (if profile then "_profile" else "")
      bench_opt_level
  else
    let result_c_dir = Resources.result_c_dir () in
    let result_dir = Resources.result_dir () in
    let opt_level = config.opt_level in
    match config.file with
    | Some filename ->
      let base = unique_base config filename in
      asprintf "clang %s/%s_out.c %s%s%s%s%s%s%s/*.c -iquote %s -o %s/%s.out -lgc -g3 %s"
        result_c_dir
        base
        gc_ini_heap_var
        mode_var
        eager_var
        monotonic_var
        hash_var
        static_var
        libc_dir
        libc_dir
        result_dir
        base
        opt_level
    | None ->
      (* clang <result_c_dir>/stdin.c <libc_dir>/*.c -o <result_dir>/stdin.out -lgc -g3 -std=c2x -pg -O3 *)
      asprintf "clang %s/stdin.c %s%s%s%s%s%s%s/*.c -iquote %s -o %s/stdin.out -lgc -g3 -std=c2x -pg %s"
        result_c_dir
        gc_ini_heap_var
        mode_var
        eager_var
        monotonic_var
        hash_var
        static_var
        libc_dir
        libc_dir
        result_dir
        opt_level

let build_run c_code ~config = match config.file with
  | Some filename ->
    (* ファイル入力モード *)
    let base = unique_base config filename in
    let out_path = Filename.concat (Resources.result_c_dir ()) (base ^ "_out.c") in
    let oc = open_out out_path in
    Printf.fprintf oc "%s" c_code;
    close_out oc;
    (* print_debug "Generated C file: %s (Execution delegated)@." out_path *)
    let cmd = build_clang_cmd ~config ~bench:false ~profile:false () in
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
    let cmd = build_clang_cmd ~config ~bench:false ~profile:false () in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad "clang fail";
    let cmd = Filename.concat (Resources.result_dir ()) "stdin.out" in
    if config.debug then fprintf err_formatter "@.%s@." cmd;
    let i = Sys.command cmd in
    if i != 0 then raise @@ Build_bad ".out fail";
    ()

let build_run_bench ~log_dir ~file ~mode_str ~itr ~mutants_length ~config =
  let src_files = asprintf "%s/%s/%s*.c" log_dir mode_str file in
  let mutant_num_list = List.init mutants_length (fun i -> i + 1) in
  (* _mutants.h 生成 *)
  let mutants_h =
    List.concat_map (fun k ->
      [ FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "mutant%d" k;  params = [(VOID, "")] });
        FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "set_tys%d" k; params = [(VOID, "")] }) ]
    ) mutant_num_list
  in
  let oc = open_out (asprintf "%s/bench/%s%s_mutants.h" log_dir file mode_str) in
  output_string oc (Format.asprintf "%a" Pp.C.pp_program mutants_h);
  close_out oc;
  (* .c 生成 *)
  let includes = [
    Include "<stdio.h>"; Include "<gc.h>"; Include "<sys/time.h>";
    Include "\"../../../libC/types.h\""; Include "\"../../../benchC/bench_json.h\"";
    Include (Format.asprintf "\"%s%s_mutants.h\"" file mode_str);
  ] @
    if config.hash then [Include "\"../../../libC/crc.h\""] else []
  in
  let decls = 
    (if config.static then [] else [Decl (No, PTR RANGE, "range_list", None)]) @
    [Decl (Static, DOUBLE, Format.asprintf "times[%d][%d]" mutants_length itr, None); Decl (No, INT, "i", None); Decl (No, STRUCT "timeval", "start_tv", None); Decl (No, STRUCT "timeval", "end_tv", None)]
  in
  let main =
    let init = [SExp (App (Var "GC_INIT", []))] in
    let stms n = 
      let for_cont = 
        (if config.hash then [SExp (App (Var "clear_crc_caches", []))] else []) @
        [
          SExp (App (Var "gettimeofday", [Addr "start_tv"; Null]));
          SExp (App (Var ("mutant" ^ string_of_int n), []));
          SExp (App (Var "gettimeofday", [Addr "end_tv"; Null]));
          SAssign (Index (Index (Var "times", Int (n - 1)), Var "i"), BinOp (Cast (DOUBLE, BinOp (Dot (Var "end_tv", "tv_sec"), Minus, Dot (Var "start_tv", "tv_sec"))), Plus, BinOp (Cast (DOUBLE, BinOp (Dot (Var "end_tv", "tv_usec"), Minus, Dot (Var "start_tv", "tv_usec"))), Mult, Float 0.000001)));
          SExp (App (Var "rewind", [Var "stdin"]));
        ]
      in
      [
        SFor ((SAssign (Var "i", Int 0), BinOp (Var "i", Lt, Int itr), PostOp (Var "i", Incr)), for_cont);
        SExp (App (Var "fprintf", [Var "stderr"; Str (Format.asprintf "mutant%d done. " n)]));
        SExp (App (Var "fflush", [Var "stdout"]));
      ]
    in
    let ret = SReturn (App (Var "update_jsonl_file", [Str (Format.asprintf "%s/%s_%s.jsonl" log_dir mode_str file); PreOp (Deref, Var "times"); Int mutants_length; Int itr])) in
    FunDef (No, { ret_ty = INT; fname = "main"; params = [] }, init @ (List.concat_map (fun k -> stms k) mutant_num_list) @ [ret])
  in
  let oc = open_out (asprintf "%s/bench/%s%s.c" log_dir file mode_str) in
  output_string oc (Format.asprintf "%a" Pp.C.pp_program (includes @ decls @ [main]));
  close_out oc;
  (* _profile.c 生成 *)
  let includes = [
    Include "<stdio.h>"; Include "<gc.h>";
    Include "\"../../../libC/types.h\""; Include "\"../../../benchC/bench_json.h\"";
    Include (Format.asprintf "\"%s%s_mutants.h\"" file mode_str);
  ] @
    if config.hash then [Include "\"../../../libC/crc.h\""] else []
  in
  let decls = 
    (if config.static then [] else [Decl (No, PTR RANGE, "range_list", None)]) @
    [Decl (Static, INT, Format.asprintf "gc_counts[%d]" mutants_length, None); Decl (Static, INT, Format.asprintf "cast_counts[%d]" mutants_length, None); 
     Decl (Static, INT, Format.asprintf "inference_counts[%d]" mutants_length, None); Decl (Static, INT, Format.asprintf "longest[%d]" mutants_length, None); 
     Decl (No, INT, "i", None); Decl (No, INT, "gc_num", None); Decl (No, INT, "gc_tmp", None); Decl (No, INT, "current_inference", None);
     Decl (No, INT, "current_cast", None); Decl (No, INT, "current_longest", None); Decl (No, INT, "current_compose", None); Decl (No, INT, "compose_cached", None);
     Decl (No, INT, "current_alloc", None); Decl (No, INT, "new_crc_num", None); Decl (No, INT, "alloc_hash", None); Decl (No, INT, "find_ty_num", None);]
  in
  let main = 
    let init = [SExp (App (Var "GC_INIT", []))] in
    let stms n = 
      let cont = 
        (if config.hash then [SExp (App (Var "clear_crc_caches", []))] else []) @
        [
          SExp (App (Var ("mutant" ^ string_of_int n), []));
          SAssign (Var "gc_tmp", App (Var "GC_get_total_bytes", []));
          SAssign (Index (Var "gc_counts", Int (n - 1)), BinOp (Var "gc_tmp", Minus, Var "gc_num"));
          SAssign (Var "gc_num", Var "gc_tmp");
          SAssign (Index (Var "cast_counts", Int (n - 1)), Var "current_cast");
          SAssign (Index (Var "inference_counts", Int (n - 1)), Var "current_inference");
          SAssign (Index (Var "longest", Int (n - 1)), Var "current_longest");
          SAssign (Var "current_cast", Int 0);
          SAssign (Var "current_inference", Int 0);
          SAssign (Var "current_longest", Int 0);
          SExp (App (Var "rewind", [Var "stdin"]));
        ]
      in
      cont @
      [ 
        SExp (App (Var "fprintf", [Var "stderr"; Str (Format.asprintf "mutant%d done. " n)]));
        SExp (App (Var "fflush", [Var "stdout"]));
      ]
    in
    let ret = SReturn (App (Var "update_jsonl_file_profile", [Str (Format.asprintf "%s/%s_%s.jsonl" log_dir mode_str file); Var "gc_counts"; Var "cast_counts"; Var "inference_counts"; Var "longest"; Int mutants_length])) in
    FunDef (No, { ret_ty = INT; fname = "main"; params = [] }, init @ List.concat_map (fun k -> stms k) mutant_num_list @ [ret])
  in
  let oc = open_out (asprintf "%s/bench/%s%s_profile.c" log_dir file mode_str) in
  output_string oc (Format.asprintf "%a" Pp.C.pp_program (includes @ decls @ [main]));
  close_out oc;
  (* build *)
  let cmd = build_clang_cmd ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:false () in
  fprintf std_formatter "@.%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad "clang(for time) fail";
  let cmd = build_clang_cmd ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:true () in
  fprintf std_formatter "@.%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad "clang(for profile) fail";
  (* run *)
  let cmd = asprintf "%s/bench/%s%s.out < samples/input/%s.txt > /dev/null" log_dir file mode_str file in
  fprintf std_formatter "%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad ".out(for time) fail";
  let cmd = asprintf "%s/bench/%s%s_profile.out < samples/input/%s.txt > /dev/null" log_dir file mode_str file in
  fprintf std_formatter "%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad ".out(for profile) fail";
  ()