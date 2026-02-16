open Unix
(* open Core *)
(* open Lambda_S1_dti.Utils *)
open Lambda_S_dti

type mode = 
| SEI | SEC | AEI | AEC | BEI | BEC
| SLI | SLC | ALI | ALC | BLI | BLC
| STATICI | STATICC

(* Base of Benchmark settings *)
let itr = 500
let files = [
  (* "church_2"; *)
  (* "church_4"; *)
  (* "church_65532"; *)
  (* "easy"; *)
  "evenodd";
  "fib";
  "fold";
  "fold_mono";
  "loop";
  "loop_mono";
  "map";
  "map_mono";
  "mklist";
  "tak";
  "zipwith";
  "zipwith_mono";
]
let modes = [
  SEI;
  SEC;
  AEI;
  AEC;
  BEI;
  BEC;
  SLI;
  SLC;
  ALI;
  ALC;
  BLI;
  BLC;
  STATICI;
  STATICC;
  ]   
  (* [SEC; SLI] : SEC と SLI を実行 *)

(* ------------------ *)
let string_of_mode = function
  | SEI -> "SEI"
  | SEC -> "SEC"
  | AEI -> "AEI"
  | AEC -> "AEC"
  | BEI -> "BEI"
  | BEC -> "BEC"
  | SLI -> "SLI"
  | SLC -> "SLC"
  | ALI -> "ALI"
  | ALC -> "ALC"
  | BLI -> "BLI"
  | BLC -> "BLC"
  | STATICI -> "STATICI"
  | STATICC -> "STATICC"

let mode_of_string = function
  | "SEI" -> SEI
  | "SEC" -> SEC
  | "AEI" -> AEI
  | "AEC" -> AEC
  | "BEI" -> BEI
  | "BEC" -> BEC
  | "SLI" -> SLI
  | "SLC" -> SLC
  | "ALI" -> ALI
  | "ALC" -> ALC
  | "BLI" -> BLI
  | "BLC" -> BLC
  | "STATICI" -> STATICI
  | "STATICC" -> STATICC
  | _ -> failwith "mode_of_string"
  
let split_pairs lst =
  List.fold_right
    (fun (a, b) (as_list, bs_list) -> (a :: as_list, b :: bs_list))
    lst ([], [])

let bench mode fmt itr decl = (* TODO: configに書き換え *)
  let tyenv = Syntax.Environment.empty in
  let _ = Typing.CC.type_of_program tyenv decl in
  (* Format.fprintf fmt "mutated program's type is %a\n" Pp.pp_ty u; *)
  match mode with
  | SLI ->
    let env = Syntax.Environment.empty in
    let translated = Translate.CC.translate tyenv (Pipeline.CC.tv_renew decl) in
    Pipeline.log_section fmt "after Translation (λS∀mp)";
    Format.fprintf fmt "%a@." Pp.LS1.pp_program translated;
    Format.pp_print_flush fmt ();
    Bench_utils.measure_execution_time (fun () -> Eval.LS1.eval_program env translated) itr
    |> split_pairs
    |> snd
  | ALI ->
    let env = Syntax.Environment.empty in
    let translated = Translate.CC.translate_alt tyenv (Pipeline.CC.tv_renew decl) in
    Pipeline.log_section fmt "after Translation (λS∀mp)";
    Format.fprintf fmt "%a@." Pp.LS1.pp_program translated;
    Format.pp_print_flush fmt ();
    Bench_utils.measure_execution_time (fun () -> Eval.LS1.eval_program env translated) itr
    |> split_pairs
    |> snd
  | BEI -> 
    let env = Syntax.Environment.empty in
    let translated = Pipeline.CC.tv_renew decl in
    Pipeline.log_section fmt "after Translation (λS∀mp)";
    Format.fprintf fmt "%a@." Pp.CC.pp_program translated;
    Format.pp_print_flush fmt ();
    Bench_utils.measure_execution_time (fun () -> Eval.CC.eval_program env translated) itr
    |> split_pairs
    |> snd
  | SEI | AEI | BLI | STATICI -> raise @@ Failure "yet"
  | SEC | AEC | BEC | SLC | ALC | BLC | STATICC -> raise @@ Failure "bench Compiler"

(* メモリ計測（設定に応じて）を JSON に *)
let mem_json mode file idx ~compile =
  let label = Printf.sprintf "%s/%s#%d" (string_of_mode mode) file idx in
  if compile then     
    let run () = ignore (Core_unix.system "logs/bench.out") in
    Bench_utils.measure_mem_to_json ~label run
  else raise @@ Failure "yet" 
  (* match mode with
  | SI ->
      let translated = Translate.CC.translate tyenv (Pipeline.CC.tv_renew decl) in
      let run () = 
        ignore (Eval.LS1.eval_program Syntax.Environment.empty translated) in
      Bench_utils.measure_mem_to_json ~label run
  | AI ->
      let translated = Translate.CC.translate_alt tyenv (Pipeline.CC.tv_renew decl) in
      let run () = 
        ignore (Eval.LS1.eval_program Syntax.Environment.empty translated) in
      Bench_utils.measure_mem_to_json ~label run
  | BI ->
      let translated = Pipeline.CC.tv_renew decl in
      let run () = 
        ignore (Eval.CC.eval_program Syntax.Environment.empty translated) in
      Bench_utils.measure_mem_to_json ~label run *)
  (* | SC | AC | BC ->  *)

(* -------- Parsing & mutation (1回で両モードに使い回す) --------------- *)
let parse_and_mutate (file : string) =
  let target_path = Printf.sprintf "samples/src/%s.ml" file in
  let _, lexeme = Pipeline.lex Format.std_formatter (Some target_path) in
  let decl  = Parser.toplevel Lexer.main lexeme in
  let lst_mutated = Mutate.mutate_all decl in
  (lst_mutated : Syntax.ITGL.program list)

(* -------- 1ファイル × 1モード（ターゲット）を実行 ------------------ *)
let bench_file_mode
    ~log_dir
    ~itr
    ~(ordinal:int)
    ~(total_targets:int)
    ~(file:string)
    ~(mode:mode)
    ~(mutants:Syntax.ITGL.program list)
  =
  (* modeに応じたconfigの生成 *)
  let config = match mode with
  | SEI -> Config.create ~alt:false ~intoB:false ~eager:true ~compile:false ~static:false ~opt_file:(Some file) ()
  | SEC -> Config.create ~alt:false ~intoB:false ~eager:true ~compile:true ~static:false ~opt_file:(Some file) ()
  | AEI -> Config.create ~alt:true ~intoB:false ~eager:true ~compile:false ~static:false ~opt_file:(Some file) ()
  | AEC -> Config.create ~alt:true ~intoB:false ~eager:true ~compile:true ~static:false ~opt_file:(Some file) ()
  | BEI -> Config.create ~alt:false ~intoB:true ~eager:true ~compile:false ~static:false ~opt_file:(Some file) ()
  | BEC -> Config.create ~alt:false ~intoB:true ~eager:true ~compile:true ~static:false ~opt_file:(Some file) ()
  | SLI -> Config.create ~alt:false ~intoB:false ~eager:false ~compile:false ~static:false ~opt_file:(Some file) ()
  | SLC -> Config.create ~alt:false ~intoB:false ~eager:false ~compile:true ~static:false ~opt_file:(Some file) ()
  | ALI -> Config.create ~alt:true ~intoB:false ~eager:false ~compile:false ~static:false ~opt_file:(Some file) ()
  | ALC -> Config.create ~alt:true ~intoB:false ~eager:false ~compile:true ~static:false ~opt_file:(Some file) ()
  | BLI -> Config.create ~alt:false ~intoB:true ~eager:false ~compile:false ~static:false ~opt_file:(Some file) ()
  | BLC -> Config.create ~alt:false ~intoB:true ~eager:false ~compile:true ~static:false ~opt_file:(Some file) ()
  | STATICI -> Config.create ~alt:false ~intoB:true ~eager:true ~compile:false ~static:true ~opt_file:(Some file) ()
  | STATICC -> Config.create ~alt:false ~intoB:true ~eager:true ~compile:true ~static:true ~opt_file:(Some file) ()
  in

  Format.fprintf Format.std_formatter "debug: bench_file_mode\n";
  (* text用，json用のocとfmtを取得 *)
  let oc_opt, fmt, json_oc, json_first = 
    let null_fmt = Format.make_formatter (fun _buf _pos _len -> ()) (fun () -> ()) in
    match Bench_utils.out_mode with
    | Text -> 
      let file_path = Printf.sprintf "%s/%s_%s.log" log_dir (string_of_mode mode) file in
      let oc = open_out file_path in
      Some oc, Format.formatter_of_out_channel oc, None, ref true
    | JsonLines ->
      let jsonl_path = Printf.sprintf "%s/%s_%s.jsonl" log_dir (string_of_mode mode) file in
      let oc = open_out jsonl_path in
      None, null_fmt, Some oc, ref true
    | Json -> 
      let json_path = Printf.sprintf "%s/%s_%s.json"  log_dir (string_of_mode mode) file in
      let oc = open_out json_path in
      Out_channel.output_string oc "{ \"file\": \""; Out_channel.output_string oc file; Out_channel.output_string oc "\", ";
      Out_channel.output_string oc "\"mode\": \""; Out_channel.output_string oc (string_of_mode mode); Out_channel.output_string oc "\", ";
      Out_channel.output_string oc "\"settings\": {\"mem_mode\": \""; 
      Out_channel.output_string oc (match Bench_utils.mem_mode with Off->"off" | Fast->"fast" | Corebench->"corebench");
      Out_channel.output_string oc "\", \"fast_runs\": "; Out_channel.output_string oc (string_of_int Bench_utils.fast_runs);
      Out_channel.output_string oc "}, \"mutants\": [\n";
      None, null_fmt, Some oc, ref true
  in

  let ppf = Utils.Format.empty_formatter in

  (* ターゲット用 Progress を開始 *)
  let label = Printf.sprintf "%s_%s" (string_of_mode mode) file in
  let prog = Bench_utils.Target_progress.create
               ~label ~total:(List.length mutants)
               ~ordinal ~total_targets
  in

  (* compileモードなら，.c用のディレクトリを作成 *)
  if config.compile then
    let c_dir = Printf.sprintf "%s/%s" log_dir (string_of_mode mode) in
    if not (Sys.file_exists c_dir) then Core_unix.mkdir c_dir;
    let bench_dir = Printf.sprintf "%s/bench" log_dir in
    if not (Sys.file_exists bench_dir) then Core_unix.mkdir bench_dir;
  
  let counter = ref 0 in
  List.iteri (fun i p ->
    try( 
      (* Printf.fprintf stdout "debug: iter is %d\n" i; *)
      let idx = i + 1 in
      (* ---- Mutant 見出し ---- *)
      Option.iter (fun oc ->
        Printf.fprintf oc "\n(*** Mutant %d ***)\n%!" idx
      ) oc_opt;
      Option.iter (fun oc ->
        incr counter;
        Printf.fprintf oc "\n(%d):\n" !counter
      ) oc_opt;

      (* Coercion / Cast insertion *)
      (* compileモードなら，コンパイルして.cに書き込み *)
      let decl, tyenv = 
        if config.compile then begin
          let c_code, decl, tyenv = 
            if config.intoB then 
              let _, tyenv, kfunenvs, _ = Stdlib.pervasives_LB ~config in
              let _, decl, _ = Pipeline.translate_to_CC ppf tyenv p ~config ~bench_ppf:fmt in
              let c_code = Pipeline.cc_compile ppf [decl] tyenv kfunenvs ~config ~bench_ppf:fmt ~bench:idx in
              c_code, decl, tyenv
            else
              let _, tyenv, kfunenvs, _ = Stdlib.pervasives_LS ~config in
              let _, decl, _ = Pipeline.translate_to_CC ppf tyenv p ~config ~bench_ppf:fmt in
              let c_code = Pipeline.cc_compile ppf [decl] tyenv kfunenvs ~config ~bench_ppf:fmt ~bench:idx in
              c_code, decl, tyenv
          in
          let filename = Format.asprintf "%s/%s/%s%d.c" log_dir (string_of_mode mode) file idx in
          let oc = open_out filename in
          Printf.fprintf oc "%s" c_code;
          close_out oc;
          decl, tyenv
        end else 
          let _, tyenv, _, _ = Stdlib.pervasives_LB ~config in
          let _, decl, _ = Pipeline.translate_to_CC ppf tyenv p ~config ~bench_ppf:fmt in
          let decl = Pipeline.CC.tv_renew decl in
          decl, tyenv
      in

      (* 実行時間のBenchmarking *)
      let lst_elapsed_time =
        try 
          if not config.compile then bench mode fmt itr decl
          else []
        with
        | Syntax.Blame _ -> Format.fprintf fmt "blame"; []
        | Typing.Type_error str -> Format.fprintf fmt "type error %s \n" str; []
        | Typing.Type_bug str -> Format.fprintf fmt "type bug %s \n" str; []
        | Translate.Translation_bug str -> Format.fprintf fmt "translation %s in bench\n" str; []
        | KNormal.KNormal_error str -> Format.fprintf fmt "knorm_error %s in bench\n" str; []
        | KNormal.KNormal_bug str -> Format.fprintf fmt "knorm_bug %s in bench\n" str; []
        | ToC.ToC_bug str -> Format.fprintf fmt "toc_bug %s in bench\n" str; []
        | _ -> Format.fprintf fmt "some error happened in bench\n"; []
      in

      (* File output of benchmarking score *)
      Option.iter (fun oc ->
        match lst_elapsed_time with
        | [] -> Printf.fprintf oc "\n"
        | _  -> List.iter (fun t -> Printf.fprintf oc "%f\n" t) lst_elapsed_time
      ) oc_opt;

      (* JSON 出力用に各種文字列へ *)
      let after_mutate_str      = Format.asprintf "%a" Pp.ITGL.pp_program p in
      let after_insertion_str   = Format.asprintf "%a" Pp.CC.pp_program decl in
      let after_translation_str =
        if config.intoB then 
          Format.asprintf "%a" Pp.CC.pp_program decl
        else
          let translated = Pipeline.translate_to_LS1 ppf tyenv decl ~config in
          Format.asprintf "%a" Pp.LS1.pp_program translated
      in

      (* 実行時間（従来の itr 回計測）を JSON に *)
      let times_sec_json = Bench_utils.J.list (List.map (fun t -> Bench_utils.J.float t) lst_elapsed_time) in

      let mem = mem_json mode file idx ~compile:config.compile in

      (* 1ミュータントの JSON オブジェクト *)
      let mutant_json =
        Bench_utils.J.obj [
          ("mode", Bench_utils.J.str (string_of_mode mode));
          ("mutant_index", Bench_utils.J.int idx);
          ("after_mutate", Bench_utils.J.str after_mutate_str);
          ("after_insertion", Bench_utils.J.str after_insertion_str);
          ("after_translation", Bench_utils.J.str after_translation_str);
          ("times_sec", times_sec_json);
          ("mem", (match mem with None -> `Null | Some j -> j));
          ("cast", `Null);
          ("inference", `Null);
          ("longest", `Null);
        ]
      in

      (* ファイルへ書き出し *)
      begin match json_oc, Bench_utils.out_mode with
      | None, _ -> ()
      | Some oc, JsonLines ->
          Bench_utils.J.to_channel_ln oc mutant_json
      | Some oc, Json ->
          if not !json_first then Out_channel.output_string oc ",\n";
          Yojson.Safe.to_channel oc mutant_json;
          json_first := false
      | Some _, Text -> raise @@ Failure "yet"
      end;

      Option.iter Out_channel.flush oc_opt;
      Bench_utils.Target_progress.tick prog;  (* ← 変異1件完了ごとに更新 *)
    )
    with
    | Failure message -> Format.fprintf fmt "Failure: %s\n" message
    | Translate.Translation_bug str -> Format.fprintf fmt "translation_bug: %s\n" str
    | Syntax.Blame _ -> Format.fprintf fmt "evaluation blame \n"
    | Eval.Eval_bug _ -> Format.fprintf fmt "evaluation bug!! \n"
    | _ -> Format.fprintf fmt "some error was happened\n"
  ) mutants;

  Option.iter Out_channel.close oc_opt;

  (match json_oc, Bench_utils.out_mode with
    | None, _ -> ()
    | Some oc, JsonLines -> Out_channel.close oc
    | Some oc, Json ->
       Out_channel.output_string oc "\n]}\n"; Out_channel.close oc
    | Some _, Text -> raise @@ Failure "yet");

  (* compileモードなら，build_run_benchでbenchmarking *)
  if config.compile then 
    Pipeline.build_run_bench ~log_dir ~file ~mode_str:(string_of_mode mode) ~itr ~mutants_length:(List.length mutants) ~config;

  (* ターゲットの進捗バーを確定（改行しない） *)
  Bench_utils.Target_progress.print ~final:false prog

let () =
  let files_ref = ref [] in
  let modes_ref = ref [] in
  let itr_ref = ref 0 in
  let static = ref false in
  let dynamize = ref false in
  let grift = ref false in
  let specs = [
    ("-m", Arg.String (fun s -> modes_ref := mode_of_string s :: !modes_ref), " Select mode");
    ("-i", Arg.Int (fun i -> itr_ref := i), " Specify itration");
    ("-c", Arg.Unit (fun () -> modes_ref := [SLC; SEC; ALC; AEC; BLC; BEC; STATICC] @ !modes_ref), " Benchmarking all compile mode");
    ("--static", Arg.Unit (fun () -> static := true), " Benchmarking fully-static programs");
    ("--dynamize", Arg.Unit (fun () -> dynamize := true), " Benchmarking mutated programs");
    ("--grift", Arg.Unit (fun () -> grift := true), " Benchmarking on grift");
    ("--all", Arg.Unit (fun () -> dynamize := true; static := true; grift := true), " Benchmarking all (--static --dynamize --grift)");
    ("--paper", Arg.Unit (fun () -> modes_ref := [SLC; ALC; STATICC] @ !modes_ref), " Banchmarking modes for paper (SLC, ALC, STATICC)")
    ]
  in
  Arg.parse specs (fun f -> files_ref := f :: !files_ref) " Usage: ./bench [file...] [-m mode]";

  (* 指定がなければ全部、あればそれを対象にする *)
  let files = if !files_ref = [] then files else !files_ref in
  let modes = if !modes_ref = [] then modes else !modes_ref in
  let itr = if !itr_ref = 0 then itr else !itr_ref in

  (* 1. 前処理: 全ファイルを parse→mutate *)
  Format.fprintf Format.std_formatter "debug: parse->mutate\n";
  let prepared : (string * Syntax.ITGL.program list) list =
    List.map (fun file -> (file, parse_and_mutate file)) files 
  in
    Format.fprintf Format.std_formatter "debug: parse->mutate done\n";

  (* モード展開してターゲット配列を作る *)
  Format.fprintf Format.std_formatter "debug: making targets lists\n";
  let targets : (string * mode * Syntax.ITGL.program list) list =
    List.concat_map (fun (file, muts) ->
      List.map (fun m -> (file, m, muts)) modes
    ) prepared
  in
  Format.fprintf Format.std_formatter "debug: making targets lists done\n";
  Format.fprintf Format.std_formatter "debug: targets lists number is %d\n" (List.length targets);
  Format.fprintf Format.std_formatter "debug: first target's mutants number is %d\n" (match targets with (_, _, h) :: _ -> List.length h | _ -> 0);
  let total_targets = List.length targets in

  (* 2. ログディレクトリ準備 *)
  let tm = localtime (time ()) in
  let timestamp =
    Printf.sprintf "%04d%02d%02d-%02d:%02d:%02d"
      (tm.tm_year + 1900) (tm.tm_mon + 1) tm.tm_mday (tm.tm_hour) (tm.tm_min) (tm.tm_sec)
  in
  let log_base_dir = "logs" in
  let log_dir = Printf.sprintf "%s/%s" log_base_dir timestamp in
  if not (Sys.file_exists log_base_dir) then Core_unix.mkdir log_base_dir;
  if not (Sys.file_exists log_dir) then Core_unix.mkdir log_dir;

  (* 3. 実行: 各ターゲットを順番に *)
  Format.fprintf Format.std_formatter "debug: main iteration\n";
  begin if !dynamize then
    List.iteri (fun i (file, mode, mutants) ->
      if mode = STATICI || mode = STATICC then () else
      bench_file_mode
        ~log_dir
        ~itr
        ~ordinal:(i + 1)
        ~total_targets
        ~file
        ~mode
        ~mutants
    ) targets
  else () end;

  begin if !static then 
    let targets = List.map (fun (file, m, muts) -> (file ^ "_fs", m, [List.hd muts])) targets in
    List.iteri (fun i (file, mode, mutants) ->
      bench_file_mode
        ~log_dir
        ~itr
        ~ordinal:(i + 1)
        ~total_targets
        ~file
        ~mode
        ~mutants
    ) targets
  else () end;

  begin if !grift then begin
    Format.fprintf Format.std_formatter "debug: grift\n";
    List.iter 
      (fun file -> 
        let i = Sys.command (Format.asprintf "python3 benchC/run_grift.py samples/src_grift/%s.grift samples/input/%s.txt -i %d" file file itr) in
        if i != 0 then failwith "python grift\n";
        ()
      ) 
      files;
    begin if !static then
      List.iter 
        (fun file -> 
          let i = Sys.command (Format.asprintf "python3 benchC/run_grift.py samples/src_grift/%s.grift samples/input/%s_fs.txt --static -i %d" file file itr) in
          if i != 0 then failwith "python grift (fully-static)\n";
          ()
        ) 
        files
    else () end
  end else () end;

  Printf.printf "\n";
  Printf.printf "debug: everything was done\n"
