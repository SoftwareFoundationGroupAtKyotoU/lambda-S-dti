open Format
open Config
open Syntax.C

exception Build_bad of string

let gc_ini_heap_var = "-D GC_INITIAL_HEAP_SIZE=1048576 "

let warmup = 5

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
  ?(check=false) ~config ~bench ~profile () =
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
    let suffix = if profile then "_profile" else if check then "_check" else "" in
    asprintf "clang %s/bench/%s%s%s.c %s%s%s%s%s%s%slibC/*.c benchC/*.c %s -o %s/bench/%s%s%s.out -lgc -lcjson %s" (* -flto *) (* -falign-functions=32 -falign-loops=32 -falign-jumps=32 *)
      log_dir
      file
      mode_str
      suffix
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
      suffix
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

let crc_active (config : Config.t) = not config.intoB && not config.static

let build_run_bench ~log_dir ~file ~mode_str ~itr ~mutants_length ~config =
  let src_files = asprintf "%s/%s/%s*.c" log_dir mode_str file in
  let mutant_num_list = List.init mutants_length (fun i -> i + 1) in
  (* _mutants.h 生成 *)
  let mutants_h =
    List.concat_map (fun k ->
      [ FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "mutant%d" k; params = [(VOID, "")] }) ] @
      (if config.static then []
       else [ FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "set_tys%d" k; params = [(VOID, "")] }) ])
    ) mutant_num_list
  in
  let oc = open_out (asprintf "%s/bench/%s%s_mutants.h" log_dir file mode_str) in
  output_string oc (Format.asprintf "%a" Pp.C.pp_program mutants_h);
  close_out oc;
  let jsonl_path = Format.asprintf "%s/%s_%s.jsonl" log_dir mode_str file in
  let per_run_prelude n =
    (if config.static then [] else [SExp (App (Var (Printf.sprintf "set_tys%d" n), []))]) @
    (if config.hash then [SExp (App (Var "clear_crc_caches", []))] else [])
  in
  (* --- timing .c 生成 --- *)
  let includes = [
    Include "<stdio.h>"; Include "<gc.h>"; Include "<sys/time.h>";
    Include "\"../../../libC/types.h\""; Include "\"../../../benchC/bench_json.h\"";
    Include (Format.asprintf "\"%s%s_mutants.h\"" file mode_str);
  ] @
    if crc_active config then [Include "\"../../../libC/crc.h\""] else []
  in
  let decls =
    (if config.static then [] else [Decl (No, PTR RANGE, "range_list", None)]) @
    [ Decl (Static, DOUBLE, Format.asprintf "times[%d][%d]" mutants_length itr, None);
      Decl (No, INT, "i", None);
      Decl (No, STRUCT "timeval", "start_tv", None);
      Decl (No, STRUCT "timeval", "end_tv", None) ]
  in
  let per_iter n ~timed =
    per_run_prelude n @
    (if timed then [SExp (App (Var "gettimeofday", [Addr "start_tv"; Null]))] else []) @
    [ SExp (App (Var ("mutant" ^ string_of_int n), [])) ] @
    (if timed then
      [ SExp (App (Var "gettimeofday", [Addr "end_tv"; Null]));
        SAssign (Index (Index (Var "times", Int (n - 1)), Var "i"),
          BinOp (Cast (DOUBLE, BinOp (Dot (Var "end_tv", "tv_sec"), Minus, Dot (Var "start_tv", "tv_sec"))),
                 Plus,
                 BinOp (Cast (DOUBLE, BinOp (Dot (Var "end_tv", "tv_usec"), Minus, Dot (Var "start_tv", "tv_usec"))),
                        Mult, Float 0.000001))) ]
     else []) @
    [ SExp (App (Var "rewind", [Var "stdin"])) ]
  in
  let mutant_time_block n =
    [ SFor ((SDecl (INT, "w", Some (Int 0)), BinOp (Var "w", Lt, Int warmup), PostOp (Var "w", Incr)),
            per_iter n ~timed:false);
      SFor ((SAssign (Var "i", Int 0), BinOp (Var "i", Lt, Int itr), PostOp (Var "i", Incr)),
            per_iter n ~timed:true);
      SExp (App (Var "fprintf", [Var "stderr"; Str (Format.asprintf "mutant%d done. " n)]));
      SExp (App (Var "fflush", [Var "stdout"])) ]
  in
  let main =
    FunDef (No, { ret_ty = INT; fname = "main"; params = [] },
      [ SExp (App (Var "GC_INIT", [])) ] @
      List.concat_map mutant_time_block mutant_num_list @
      [ SReturn (App (Var "update_jsonl_file",
          [ Str jsonl_path; PreOp (Deref, Var "times"); Int mutants_length; Int itr ])) ])
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
    if crc_active config then [Include "\"../../../libC/crc.h\""] else []
  in
  (* --- メトリクス表 --- *)
  let coerce_kind_metrics : (string * [ `Mem | `Scalar of string | `Arr of string * string ]) list = [
    "coerce_id",         `Arr ("coerce_kind", "C_ID");
    "coerce_fun",        `Arr ("coerce_kind", "C_FUN");
    "coerce_list",       `Arr ("coerce_kind", "C_LIST");
    "coerce_tuple",      `Arr ("coerce_kind", "C_TUPLE");
    "coerce_ref",        `Arr ("coerce_kind", "C_REF");
    "coerce_array",      `Arr ("coerce_kind", "C_ARRAY");
    "coerce_tv",         `Arr ("coerce_kind", "C_TV");
    "coerce_bot",        `Arr ("coerce_kind", "C_BOT");
  ]
  in
  let dti_by_ground_metrics : (string * [ `Mem | `Scalar of string | `Arr of string * string ]) list = [
    "dti_fn",            `Arr ("dti_by_ground", "G_FN");
    "dti_li",            `Arr ("dti_by_ground", "G_LI");
    "dti_tp",            `Arr ("dti_by_ground", "G_TP");
    "dti_rf",            `Arr ("dti_by_ground", "G_RF");
    "dti_ar",            `Arr ("dti_by_ground", "G_AR");
    "dti_int",           `Arr ("dti_by_ground", "G_INT");
    "dti_bool",          `Arr ("dti_by_ground", "G_BOOL");
    "dti_float",         `Arr ("dti_by_ground", "G_FLOAT");
    "dti_unit",          `Arr ("dti_by_ground", "G_UNIT");
  ]
  in
  let profile_metrics : (string * [ `Mem | `Scalar of string | `Arr of string * string ]) list = [
    "mem",               `Mem;
    "cast",              `Scalar "current_cast";
    "inference",         `Scalar "current_inference";
    "longest",           `Scalar "current_longest";
    "compose",           `Scalar "current_compose";
    "compose_cached",    `Scalar "compose_cached";
    "alloc",             `Scalar "current_alloc";
    "new_crc",           `Scalar "new_crc_num";
    "alloc_hash",        `Scalar "alloc_hash";
    "find_ty",           `Scalar "find_ty_num";
    "ty_find_calls",     `Scalar "ty_find_calls";
    "ty_find_max_chain", `Scalar "ty_find_max_chain";
    "normalize_tv",      `Scalar "normalize_tv_num";
    "compose_max_depth", `Scalar "compose_max_depth";
    "blame_check",       `Scalar "blame_check_num";
    "blame_raised",      `Scalar "blame_raised_num";
  ] @
    (if crc_active config then coerce_kind_metrics else []) @
    (if not config.static then dti_by_ground_metrics else [])
  in
  let nm = List.length profile_metrics in
  (* profile .c 側で定義すべき大域カウンタ*)
  let counter_int  = ["current_inference"; "current_cast"; "current_longest"; "current_compose";
                      "compose_cached"; "current_alloc"; "new_crc_num"; "alloc_hash"; "find_ty_num";
                      "ty_find_calls"; "ty_find_max_chain"; "normalize_tv_num"; "compose_max_depth";
                      "blame_check_num"; "blame_raised_num"] in
  let counter_arr  =
    (if crc_active config then [("coerce_kind", "N_CRCKIND")] else []) @
    (if not config.static then [("dti_by_ground", "N_GROUND_TY")] else []) in
  let decls =
    (if config.static then [] else [Decl (No, PTR RANGE, "range_list", None)]) @
    [ Decl (Static, LLONG, Format.asprintf "metric_data[%d][%d]" mutants_length nm, None);
      Decl (No, PTR CHAR, "metric_names[]", Some (Array (List.map (fun (k, _) -> Str k) profile_metrics)));
      Decl (No, LLONG, "mem_before", None) ] @
    List.map (fun c -> Decl (No, INT, c, None)) counter_int @
    List.map (fun (c, size_const) -> Decl (No, INT, Format.asprintf "%s[%s]" c size_const, None)) counter_arr
  in
  let read_metric = function
    | `Mem -> BinOp (App (Var "GC_get_total_bytes", []), Minus, Var "mem_before")
    | `Scalar g -> Var g
    | `Arr (g, member) -> Index (Var g, Var member)
  in
  let reset_counters =
    List.map (fun c -> SAssign (Var c, Int 0)) counter_int @
    List.map (fun (c, size_const) ->
      SFor ((SDecl (INT, "_rk", Some (Int 0)), BinOp (Var "_rk", Lt, Var size_const), PostOp (Var "_rk", Incr)),
            [ SAssign (Index (Var c, Var "_rk"), Int 0) ])) counter_arr
  in
  let mutant_profile_block n =
    reset_counters @
    [ SAssign (Var "mem_before", App (Var "GC_get_total_bytes", [])) ] @
    per_run_prelude n @
    [ SExp (App (Var ("mutant" ^ string_of_int n), [])) ] @
    List.mapi (fun j (_, src) ->
      SAssign (Index (Index (Var "metric_data", Int (n - 1)), Int j), read_metric src)) profile_metrics @
    [ SExp (App (Var "rewind", [Var "stdin"]));
      SExp (App (Var "fprintf", [Var "stderr"; Str (Format.asprintf "mutant%d done. " n)]));
      SExp (App (Var "fflush", [Var "stdout"])) ]
  in
  let pmain =
    FunDef (No, { ret_ty = INT; fname = "main"; params = [] },
      [ SExp (App (Var "GC_INIT", [])) ] @
      List.concat_map mutant_profile_block mutant_num_list @
      [ SReturn (App (Var "update_jsonl_file_profile",
          [ Str jsonl_path; Var "metric_names"; PreOp (Deref, Var "metric_data"); Int nm; Int mutants_length ])) ])
  in
  let oc = open_out (asprintf "%s/bench/%s%s_profile.c" log_dir file mode_str) in
  output_string oc (Format.asprintf "%a" Pp.C.pp_program (includes @ decls @ [pmain]));
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

let build_run_bench_check ~log_dir ~file ~mode_str ~mutants_length ~config ~expected =
  let src_files = asprintf "%s/%s/%s*.c" log_dir mode_str file in
  let mutant_num_list = List.init mutants_length (fun i -> i + 1) in
  let mutants_h =
    List.concat_map (fun k ->
      [ FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "mutant%d" k; params = [(VOID, "")] }) ] @
      (if config.static then []
       else [ FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "set_tys%d" k; params = [(VOID, "")] }) ])
    ) mutant_num_list
  in
  let oc = open_out (asprintf "%s/bench/%s%s_check_mutants.h" log_dir file mode_str) in
  output_string oc (Format.asprintf "%a" Pp.C.pp_program mutants_h);
  close_out oc;
  let per_run_prelude n =
    (if config.static then [] else [SExp (App (Var (Printf.sprintf "set_tys%d" n), []))]) @
    (if config.hash then [SExp (App (Var "clear_crc_caches", []))] else [])
  in
  let includes = [
    Include "<stdio.h>"; Include "<gc.h>";
    Include "\"../../../libC/types.h\"";
    Include (Format.asprintf "\"%s%s_check_mutants.h\"" file mode_str);
  ] @
    if crc_active config then [Include "\"../../../libC/crc.h\""] else []
  in
  let decls = if config.static then [] else [Decl (No, PTR RANGE, "range_list", None)] in
  let mutant_check_block n =
    per_run_prelude n @
    [ SExp (App (Var ("mutant" ^ string_of_int n), []));
      SExp (App (Var "printf", [Str "\\n"]));
      SExp (App (Var "rewind", [Var "stdin"])) ]
  in
  let main =
    FunDef (No, { ret_ty = INT; fname = "main"; params = [] },
      [ SExp (App (Var "GC_INIT", [])) ] @
      List.concat_map mutant_check_block mutant_num_list @
      [ SReturn (Int 0) ])
  in
  let oc = open_out (asprintf "%s/bench/%s%s_check.c" log_dir file mode_str) in
  output_string oc (Format.asprintf "%a" Pp.C.pp_program (includes @ decls @ [main]));
  close_out oc;
  (* build *)
  let cmd = build_clang_cmd ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:false ~check:true () in
  fprintf std_formatter "@.%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad "clang(for check) fail";
  (* run: 標準出力をファイルに落として読み戻す（/dev/null に捨てない） *)
  let stdout_path = asprintf "%s/bench/%s%s_check.stdout" log_dir file mode_str in
  let cmd = asprintf "%s/bench/%s%s_check.out < samples/input/%s.txt > %s"
    log_dir file mode_str file stdout_path in
  fprintf std_formatter "%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Build_bad ".out(for check) fail";
  let ic = open_in stdout_path in
  let output = In_channel.input_all ic in
  close_in ic;
  let lines = String.split_on_char '\n' output in
  let lines = match List.rev lines with "" :: rest -> List.rev rest | _ -> lines in
  if List.length lines <> mutants_length then
    raise @@ Build_bad (Printf.sprintf
      "check: expected %d output lines (1 per mutant) but got %d - is print missing a trailing separator, or did a mutant crash silently?"
      mutants_length (List.length lines));
  List.mapi (fun i line -> (i + 1, line)) lines
  |> List.filter (fun (_, line) -> line <> expected)