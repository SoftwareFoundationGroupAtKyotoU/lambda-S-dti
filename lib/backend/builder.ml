open Format
open Config

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
