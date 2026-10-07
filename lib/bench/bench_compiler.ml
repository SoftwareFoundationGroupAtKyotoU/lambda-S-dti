(* ベンチマーク用の C ドライバ生成・並列コンパイルを担当するモジュール。
   実行(タイミング計測・GRIFT実行)は Bench_runner の役目。 *)
open Format
open Config
open Syntax.C
open Bench_target

let crc_active (config : Config.t) = not config.intoB && not config.static

let warmup = 5

(* 1 target 分のベンチドライバ (.c) 生成結果。clang 呼び出しはまだ行わない —
   コンパイルコマンド文字列を作るところまでで止め、実際の clang 起動は
   Bench_builder.compile_all (並列) に委ねる。 *)
type bench_job = {
  out_path : string;
  profile_out_path : string;
  compile_cmd : string;
  profile_compile_cmd : string;
  run_cmd : string;
  profile_run_cmd : string;
}

(* toC が mutant ごとに出力する reset_globals<n>() の呼び出し。I4 で C グローバルになった
   トップレベル変数が mutant<n>() の終了後もデータを掴み続け、同じプロセスで後に走る
   run・mutant の GC を重くしないよう、各 run の直後（計測区間の外）で呼ぶ。 *)
let reset_globals_call n = SExp (App (Var (Printf.sprintf "reset_globals%d" n), []))

(* _mutants.h / timing用.c / profile用.c を生成し、それぞれをビルドする
   clangコマンドと、ビルド後に実行するコマンドを bench_job として返す。
   ファイル書き込みのみの副作用で、Sys.command は一切呼ばない。 *)
let generate_bench_sources ~log_dir ~file ~mode_str ~itr ~mutants_length ~config : bench_job =
  (* mutant ファイルは <file>_<idx>.c という形式でのみ書かれる (compile_mutants
     参照)。単純な "<file>*.c" だと、同じ mode_str ディレクトリを共有する
     別 target のファイル名が <file> をプレフィックスとして含む場合
     (例: dynamize の "evenodd" と static の "evenodd_fs" — "evenodd*.c" が
     "evenodd_fs_1.c" にもマッチしてしまう)に誤って巻き込み、
     clang のリンクで "multiple definition" エラーになる。
     "_" + 数字で始まるものだけに絞ることでこれを避ける。 *)
  let src_files = asprintf "%s/%s/%s_[0-9]*.c" log_dir mode_str file in
  let mutant_num_list = List.init mutants_length (fun i -> i + 1) in
  (* _mutants.h 生成 *)
  let mutants_h =
    List.concat_map (fun k ->
      [ FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "mutant%d" k; params = [(VOID, "")] });
        FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "reset_globals%d" k; params = [(VOID, "")] }) ] @
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
    [ reset_globals_call n; SExp (App (Var "rewind", [Var "stdin"])) ]
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
    [ reset_globals_call n;
      SExp (App (Var "rewind", [Var "stdin"]));
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
  {
    out_path = asprintf "%s/bench/%s%s.out" log_dir file mode_str;
    profile_out_path = asprintf "%s/bench/%s%s_profile.out" log_dir file mode_str;
    compile_cmd = Builder.build_clang_cmd ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:false ();
    profile_compile_cmd = Builder.build_clang_cmd ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:true ();
    run_cmd = asprintf "%s/bench/%s%s.out < samples/input/%s.txt > /dev/null" log_dir file mode_str file;
    profile_run_cmd = asprintf "%s/bench/%s%s_profile.out < samples/input/%s.txt > /dev/null" log_dir file mode_str file;
  }

(* 正当性チェック用の軽量ハーネス: タイミング計測・メトリクス収集を一切せず、
   各 mutant を 1 回だけ実行して標準出力に区切りの改行を挟みながら答えを出す。
   実際の標準出力を mutant 数だけの行に分割し、期待値（ユーザー指定の1文字列、
   全 mutant で共通）と厳密比較する。不一致だった mutant index と実際の出力の
   一覧を返す（空リスト = 全 mutant 一致）。 *)
let build_run_bench_check ~log_dir ~file ~mode_str ~mutants_length ~config ~expected =
  (* generate_bench_sources と同じ理由で "_" + 数字で始まるものだけに絞る。 *)
  let src_files = asprintf "%s/%s/%s_[0-9]*.c" log_dir mode_str file in
  let mutant_num_list = List.init mutants_length (fun i -> i + 1) in
  let mutants_h =
    List.concat_map (fun k ->
      [ FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "mutant%d" k; params = [(VOID, "")] });
        FunDecl (No, { ret_ty = INT; fname = Printf.sprintf "reset_globals%d" k; params = [(VOID, "")] }) ] @
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
      reset_globals_call n;
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
  let cmd = Builder.build_clang_cmd ~config ~bench:true ~log_dir ~file ~mode_str ~src_files ~profile:false ~check:true () in
  fprintf std_formatter "@.%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Runner.Build_bad "clang(for check) fail";
  (* run: 標準出力をファイルに落として読み戻す（/dev/null に捨てない） *)
  let stdout_path = asprintf "%s/bench/%s%s_check.stdout" log_dir file mode_str in
  let cmd = asprintf "%s/bench/%s%s_check.out < samples/input/%s.txt > %s"
    log_dir file mode_str file stdout_path in
  fprintf std_formatter "%s@." cmd;
  let i = Sys.command cmd in
  if i != 0 then raise @@ Runner.Build_bad ".out(for check) fail";
  let ic = open_in stdout_path in
  let output = In_channel.input_all ic in
  close_in ic;
  let lines = String.split_on_char '\n' output in
  let lines = match List.rev lines with "" :: rest -> List.rev rest | _ -> lines in
  if List.length lines <> mutants_length then
    raise @@ Runner.Build_bad (Printf.sprintf
      "check: expected %d output lines (1 per mutant) but got %d - is print missing a trailing separator, or did a mutant crash silently?"
      mutants_length (List.length lines));
  List.mapi (fun i line -> (i + 1, line)) lines
  |> List.filter (fun (_, line) -> line <> expected)

let config_of_target ~file ~eager ~hash ~monotonic ~tvs_opt = function
  | S      -> Config.create ~eager ~hash ~monotonic ~tvs_opt ~file:(Some file) ~compile:true ()
  | A      -> Config.create ~eager ~hash ~monotonic ~tvs_opt ~file:(Some file) ~alt:true ~compile:true ()
  | B      -> Config.create ~eager ~hash ~tvs_opt ~file:(Some file) ~intoB:true ~compile:true ()
  | STATIC -> Config.create ~eager ~hash ~monotonic ~tvs_opt ~file:(Some file) ~static:true ~compile:true ()

(* -------- 1ファイル×1モード分の mutant を全て C にコンパイルし、
   log_dir/mode_str/ 以下に .c ファイルとして書き出す。ベンチ（prepare_target）と
   正当性チェック（test/check_mutants.ml）の両方から共有される前処理。
   ?record（デフォルト true）: mutant ごとの after_mutate 等を記録した .jsonl を
   書くかどうか。この記録はベンチ結果の一部であって、正当性チェックには不要な
   ので、test/check_mutants.ml からは false を渡して余分なファイル書き込みを
   避ける。
   ある mutant の C 生成が失敗しても残りの mutant は続けて処理し、失敗した
   mutant ごとのエラーメッセージを返す（空 = 全 mutant 成功）。失敗を
   握りつぶして clang まで進むと、mutantN の定義が無いというリンクエラーで
   初めて発覚することになるため。 *)
let compile_mutants ?(record=true) ~log_dir ~mode_str ~config ~ordinal ~total_targets (t : target)
  : Bench_progress.t * string list =
  let writer = if record then Some (Bench_output.open_writer ~log_dir ~mode_str ~file:t.file) else None in
  let ppf = Utils.Format.empty_formatter in
  let null_fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
  let label = Printf.sprintf "%s_%s" mode_str t.file in
  let prog = Bench_progress.create ~label ~total:(List.length t.mutants) ~ordinal ~total_targets in
  let c_dir = Printf.sprintf "%s/%s" log_dir mode_str in
  if not (Sys.file_exists c_dir) then Core_unix.mkdir c_dir;
  let bench_dir = Printf.sprintf "%s/bench" log_dir in
  if not (Sys.file_exists bench_dir) then Core_unix.mkdir bench_dir;
  let errors =
    List.concat (List.mapi (fun i p ->
      let idx = i + 1 in
      try
        let after_mutate_str = Format.asprintf "%a" Pp.ITGL.pp_program p in
        let initial_state = Pipeline.init_state p ~config in
        (* --- Compilation --- *)
        let c_code =
          initial_state
          |> Pipeline.typing_ITGL ppf (* save ty in state *)
          |> Pipeline.translate_to_CC ppf ~config ~bench_ppf:null_fmt ~bench:idx |> fst
          |> Pipeline.kNorm_funs ppf ~config
          |> Pipeline.closure ppf ~config
          |> Pipeline.toC ppf ~config ~bench:idx
        in
        (* write c_code in c file *)
        let filename = Format.asprintf "%s/%s/%s_%d.c" log_dir mode_str t.file idx in
        let oc = open_out filename in
        Printf.fprintf oc "%s" c_code;
        close_out oc;
        (* write mutant information in json file (record=true のときのみ) *)
        (match writer with
         | Some w ->
           Bench_output.write_mutant w
             (Bench_output.mutant_json ~mode_str ~idx
                ~after_mutate:after_mutate_str ~times_sec:[])
         | None -> ());
        Bench_progress.tick prog; (* ← 変異1件完了ごとに更新 *)
        []
      with e ->
        [ Format.asprintf "%s mutant%d: %s@\n%a" label idx (Printexc.to_string e) Pp.ITGL.pp_program p ]
    ) t.mutants)
  in
  (match writer with Some w -> Bench_output.close_writer w | None -> ());
  (prog, errors)

(* -------- 1ファイル × 1モード（ターゲット）を、並列コンパイルできる
   段階まで準備する ------------------------------------------------- *)
type prepared_target = {
  t : target;
  mode_str : string;
  b : bench_job;
}

(* mutant の C コード生成 + ベンチドライバ (.c) 生成のみを行う。
   clang は一切呼ばない（軽い純粋な OCaml 処理なので直列のままで十分）。 *)
let prepare_target ~log_dir ~itr ~ordinal ~total_targets (t : target) : (prepared_target, string list) result =
  let mode_str = Bench_target.ablation_mode_str t in
  try
    let config = config_of_target ~file:t.file ~eager:t.eager ~hash:t.hash ~monotonic:t.monotonic ~tvs_opt:t.tvs_opt t.mode in
    let prog, errors = compile_mutants ~log_dir ~mode_str ~config ~ordinal ~total_targets t in
    Bench_progress.print ~final:false prog;
    if errors <> [] then Error errors
    else
      let b = generate_bench_sources ~log_dir ~file:t.file ~mode_str ~itr
                ~mutants_length:(List.length t.mutants) ~config in
      Ok { t; mode_str; b }
  with e -> Error [ Printf.sprintf "%s_%s: %s" mode_str t.file (Printexc.to_string e) ]

let jobs_of_prepared (p : prepared_target) : Bench_builder.job list =
  [ { Bench_builder.out_path = p.b.out_path; cmd = p.b.compile_cmd };
    { Bench_builder.out_path = p.b.profile_out_path; cmd = p.b.profile_compile_cmd } ]

(* 1バッチ(dynamize または static)分の準備済み target。コード生成フェーズで
   作り、コンパイルフェーズ（compile_batch）で clang にかけ、全バッチの
   コンパイルが成功した場合にのみ Bench_runner.run_batch で実行する。 *)
type batch = {
  label : string;
  targets : prepared_target list;
}

(* 1バッチ分の全 target をコード生成する。1つでも失敗があればエラー一覧を返す。 *)
let prepare_batch ~log_dir ~itr ~label (targets : target list) : batch * string list =
  let total_targets = List.length targets in
  let results = List.mapi (fun i t -> prepare_target ~log_dir ~itr ~ordinal:(i + 1) ~total_targets t) targets in
  let prepared = List.filter_map (function Ok p -> Some p | Error _ -> None) results in
  let errors = List.concat_map (function Ok _ -> [] | Error es -> es) results in
  ({ label; targets = prepared }, errors)

(* 全target一括の並列コンパイル。Bench_builder.compile_all は make プロセス
   自体の終了を待つので、ここが完全に終わるまでは呼び出し元へ戻らない。
   失敗した target ごとのエラー（ログの場所つき）を返す。 *)
let compile_batch ~log_dir ~jobs (b : batch) : string list =
  Bench_builder.compile_all ~log_dir ~label:b.label ~jobs (List.concat_map jobs_of_prepared b.targets);
  List.filter_map (fun p ->
    if Sys.file_exists p.b.out_path && Sys.file_exists p.b.profile_out_path then None
    else Some (Printf.sprintf "%s_%s: clang failed (see %s.log / %s.log)"
                 p.mode_str p.t.file p.b.out_path p.b.profile_out_path)
  ) b.targets

(* STATIC は dynamize では走らせない。分母にも含めない *)
let dynamize_targets targets = List.filter (fun t -> t.mode <> STATIC) targets

(* STATIC モードは config が eager=true / hash=false に固定されるため、
   eager×hash の 4 通りは同一の実行になる。ファイルごとに 1 つへ畳む。
   STATIC 以外(S/A モード)の target はそのまま通す — file を "_fs" 付きに
   リネームした上で、各 (mode, eager, hash, monotonic) 組み合わせごとに
   「mutant を1つも適用していない(＝完全に静的な)ソース」をコンパイル・
   実行し、dynamize 側の同条件と比較するためのベースラインを作る。 *)
let dedup_static (targets : target list) : target list =
  let seen = Hashtbl.create 16 in
  List.filter (fun t ->
    match t.mode with
    | STATIC ->
      if Hashtbl.mem seen t.file then false
      else (Hashtbl.add seen t.file (); true)
    | _ -> true
  ) targets

let static_targets targets =
  dedup_static targets
  |> List.map (fun t -> { t with file = t.file ^ "_fs"; mutants = [List.hd t.mutants] })
  |> List.map (fun t -> if t.mode = STATIC then { t with eager = true; hash = false; monotonic = false } else t)

(* ==================== GRIFT側 ==================== *)

(* 1 grift target 分の入力。analysis / subsets は parse・mutate フェーズで
   ML 側と突き合わせ済みのもの。 *)
type grift_target = {
  file : string;
  monotonic : bool;
  analysis : Bench_grift.analysis;
  subsets : int list list;
}

(* ML/C 側の batch に対応する GRIFT 側のバッチ。 *)
type grift_batch = {
  label : string;
  prepared : Bench_grift.grift_prepared list;
}

type grift_compiled_batch = {
  label : string;
  compiled : Bench_grift.grift_compiled list;
}

(* コード生成フェーズ: 全 grift target 分の grift ソース生成・ジョブ組み立て
   (直列)。コンパイルはまだ行わない。 *)
let prepare_grift_batch ~log_dir ~itr ~static ~label (targets : grift_target list) : grift_batch * string list =
  let total_targets = List.length targets in
  let results =
    List.mapi (fun i (g : grift_target) ->
      try
        Ok (Bench_grift.prepare ~log_dir ~itr ~static ~file:g.file ~monotonic:g.monotonic
              ~analysis:g.analysis ~subsets:g.subsets ~ordinal:(i + 1) ~total_targets)
      with e -> Error (Printf.sprintf "%s %s: %s" label g.file (Printexc.to_string e))
    ) targets
  in
  ({ label; prepared = List.filter_map Result.to_option results },
   List.filter_map (function Ok _ -> None | Error e -> Some e) results)

(* コンパイルフェーズ: 全grift target・全mutant分のジョブをまとめて1回だけ
   並列コンパイルする。 *)
let compile_grift_batch ~log_dir ~jobs (b : grift_batch) : grift_compiled_batch * string list =
  Bench_builder.compile_all ~log_dir ~label:b.label ~jobs (List.concat_map Bench_grift.jobs_of_prepared b.prepared);
  let compiled = List.map Bench_grift.finalize b.prepared in
  let errors =
    List.concat_map (fun (c : Bench_grift.grift_compiled) ->
      List.concat_map (fun (m : Bench_grift.grift_prepared_mutant) ->
        List.filter_map (fun (_, (j : Bench_builder.job)) ->
          if Sys.file_exists j.out_path then None
          else Some (Printf.sprintf "%s %s#%d: grift compile failed (see %s.log)" b.label c.file m.idx j.out_path)
        ) m.jobs
      ) c.prepared
    ) compiled
  in
  ({ label = b.label; compiled }, errors)
