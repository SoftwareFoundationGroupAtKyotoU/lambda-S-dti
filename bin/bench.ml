open Unix
open Core
(* open Lambda_S1_dti.Utils *)
open Lambda_S_dti

type mode = 
| SEI | SEC | AEI | AEC | BEI | BEC
| SLI | SLC | ALI | ALC | BLI | BLC

(* ------------------ *)
(* Benchmark settings *)
let itr = 1
let files = [
  (* "church_small"; *)
  (* "church"; *)
  "church_big"; 
  (* OK, 9791.4s   *)
  "tak";
  "easy";
  "fib";
  "evenodd";
  "loop";
  (* "loop_poly"; same as loop *)
  "mklist";
  "map";
  (* "map_mono"; *)
  "fold";
  (* "fold_mono"; *)
  "zipwith";
  (* "zipwith_mono"; *)
  (* "polypoly"; NG *)
]
let modes = [
  (* SEI; *)
  (* SEC; *)
  (* AEI; *)
  (* AEC; *)
  (* BEI; *)
  (* BEC; *)
  (* SLI; *)
  SLC;
  (* ALI; *)
  (* ALC; *)
  (* BLI; *)
  (* BLC; *)
  ]   
  (* [SEC; SLI] : SEC と SLI を実行 *)

  
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
  
let log_base_dir = "logs"

(* ------------------ *)

let split_pairs lst =
  List.fold_right
    ~f:(fun (a, b) (as_list, bs_list) -> (a :: as_list, b :: bs_list))
    lst ~init:([], [])

let bench mode fmt itr decl =
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
  | SEI | AEI | BLI -> raise @@ Failure "yet"
  | SEC | AEC | BEC | SLC | ALC | BLC -> raise @@ Failure "bench Compiler"

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
  let target_path = Printf.sprintf "samples/%s.ml" file in
  let src = In_channel.read_all target_path in
  let lexeme = Lexing.from_string src in
  (* let tyenv = Syntax.Environment.empty in *)
  let decl  = Parser.toplevel Lexer.main lexeme in
  let lst_mutated = Mutate.mutate_all (decl (*tyenv*)) in
  (* src は今は未使用だが、必要なら返す *)
  (lst_mutated : Syntax.ITGL.program list)

(* -------- 1ファイル × 1モード（ターゲット）を実行 ------------------ *)
let bench_file_mode
    ~log_dir
    ~(ordinal:int)
    ~(total_targets:int)
    ~(file:string)
    ~(mode:mode)
    ~(mutants:Syntax.ITGL.program list)
  =
  (* modeに応じたconfigの生成 *)
  let config = match mode with
  | SEI -> Config.create ~alt:false ~intoB:false ~eager:true ~compile:false ()
  | SEC -> Config.create ~alt:false ~intoB:false ~eager:true ~compile:true ()
  | AEI -> Config.create ~alt:true ~intoB:false ~eager:true ~compile:false ()
  | AEC -> Config.create ~alt:true ~intoB:false ~eager:true ~compile:true ()
  | BEI -> Config.create ~alt:false ~intoB:true ~eager:true ~compile:false ()
  | BEC -> Config.create ~alt:false ~intoB:true ~eager:true ~compile:true ()
  | SLI -> Config.create ~alt:false ~intoB:false ~eager:false ~compile:false ()
  | SLC -> Config.create ~alt:false ~intoB:false ~eager:false ~compile:true ()
  | ALI -> Config.create ~alt:true ~intoB:false ~eager:false ~compile:false ()
  | ALC -> Config.create ~alt:true ~intoB:false ~eager:false ~compile:true ()
  | BLI -> Config.create ~alt:false ~intoB:true ~eager:false ~compile:false ()
  | BLC -> Config.create ~alt:false ~intoB:true ~eager:false ~compile:true ()
  in

  Printf.fprintf stdout "debug: bench_file_mode\n" ;
  (* text用，json用のocとfmtを取得 *)
  let oc_opt, fmt, json_oc, json_first = 
    let null_fmt = Format.make_formatter (fun _buf _pos _len -> ()) (fun () -> ()) in
    match Bench_utils.out_mode with
    | Text -> 
      let file_path = Printf.sprintf "%s/%s" log_dir (string_of_mode mode ^ "_" ^ file ^ ".log") in
      let oc = Out_channel.create file_path in
      Some oc, Format.formatter_of_out_channel oc, None, ref true
    | JsonLines ->
      let json_path = Printf.sprintf "%s/%s_%s.jsonl" log_dir (string_of_mode mode) file in
      let oc = Out_channel.create json_path in
      None, null_fmt, Some oc, ref true
    | Json -> 
      let json_path = Printf.sprintf "%s/%s_%s.json"  log_dir (string_of_mode mode) file in
      let oc = Out_channel.create json_path in
      Out_channel.output_string oc "{ \"file\": \""; Out_channel.output_string oc file; Out_channel.output_string oc "\", ";
      Out_channel.output_string oc "\"mode\": \""; Out_channel.output_string oc (string_of_mode mode); Out_channel.output_string oc "\", ";
      Out_channel.output_string oc "\"settings\": {\"mem_mode\": \""; 
      Out_channel.output_string oc (match Bench_utils.mem_mode with Off->"off" | Fast->"fast" | Corebench->"corebench");
      Out_channel.output_string oc "\", \"fast_runs\": "; Out_channel.output_string oc (string_of_int Bench_utils.fast_runs);
      Out_channel.output_string oc "}, \"mutants\": [\n";
      None, null_fmt, Some oc, ref true
  in

  let tyenv = Syntax.Environment.empty in
  let ppf = Utils.Format.empty_formatter in

  (* ターゲット用 Progress を開始 *)
  let label = Printf.sprintf "%s_%s" (string_of_mode mode) file in
  let prog = Bench_utils.Target_progress.create
               ~label ~total:(List.length mutants)
               ~ordinal ~total_targets
  in

  if config.compile then
    let c_dir = Printf.sprintf "%s/%s" log_dir (string_of_mode mode) in
    if not (Sys_unix.file_exists_exn c_dir) then Core_unix.mkdir c_dir;
    let bench_dir = Printf.sprintf "%s/bench" log_dir in
    if not (Sys_unix.file_exists_exn bench_dir) then Core_unix.mkdir bench_dir;
  
  let counter = ref 0 in
  List.iteri mutants (fun i p ->
    try( 
      (* Printf.fprintf stdout "debug: iter is %d\n" i; *)
      let idx = i + 1 in
      (* ---- Mutant 見出し ---- *)
      Option.iter oc_opt (fun oc ->
        Printf.fprintf oc "\n(*** Mutant %d ***)\n%!" idx
      );

      Option.iter oc_opt (fun oc ->
        incr counter;
        Printf.fprintf oc "\n(%d):\n" !counter
      );

      (* Coercion insertion *)
      let _, decl, _ = Pipeline.translate_to_CC ppf tyenv p ~intoB:config.intoB ~bench_ppf:fmt in

      (* Benchmarking *)
      let lst_elapsed_time =
        try 
          if not config.compile then bench mode fmt itr decl
          else
            let decl = Pipeline.CC.tv_renew decl in
            let c_code = 
              if config.intoB then 
                let _, _, kfunenvs, _ = Stdlib.pervasives_LB ~debug:false ~compile:true in
                Pipeline.cc_compile ppf [decl] tyenv kfunenvs ~intoB:config.intoB ~alt:config.alt ~eager:config.eager ~static:config.static ~bench_ppf:fmt ~bench:idx
              else
                let _, _, kfunenvs, _ = Stdlib.pervasives_LS ~alt:config.alt ~debug:false ~compile:true in
                Pipeline.cc_compile ppf [decl] tyenv kfunenvs ~intoB:config.intoB ~alt:config.alt ~eager:config.eager ~static:config.static ~bench_ppf:fmt ~bench:idx
            in
            let oc = Out_channel.create (Format.asprintf "%s/%s/%s%d.c" log_dir (string_of_mode mode) file idx) in
            Printf.fprintf oc "%s" c_code;
            close_out oc;
            []
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
      Option.iter oc_opt (fun oc ->
        match lst_elapsed_time with
        | [] -> Printf.fprintf oc "\n"
        | _  -> List.iter lst_elapsed_time (fun t -> Printf.fprintf oc "%f\n" t)
      );

      (* JSON 出力用に各種文字列へ（※テキストログを出さないモードでも生成できる） *)
      let after_mutate_str    = Format.asprintf "%a" Pp.ITGL.pp_program p in
      let after_insertion_str = Format.asprintf "%a" Pp.CC.pp_program decl in
      let after_translation_str =
        if config.intoB then 
          Format.asprintf "%a" Pp.CC.pp_program decl
        else
          let translated = Pipeline.translate_to_LS1 ppf tyenv decl ~alt:(config.alt && not config.compile) in
          Format.asprintf "%a" Pp.LS1.pp_program translated
      in

      (* 実行時間（従来の itr 回計測）を JSON に *)
      let times_sec_json = Bench_utils.J.list (List.map lst_elapsed_time (fun t -> Bench_utils.J.float t)) in

      let mem = mem_json mode file idx ~compile:config.compile in

      (* 1ミュータントの JSON オブジェクト *)
      let mutant_json =
        Bench_utils.J.obj [
          ("mutant_index", Bench_utils.J.int idx);
          ("after_mutate", Bench_utils.J.str after_mutate_str);
          ("after_insertion", Bench_utils.J.str after_insertion_str);
          ("after_translation", Bench_utils.J.str after_translation_str);
          ("times_sec", times_sec_json);
          ("mem", (match mem with None -> `Null | Some j -> j));
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

      Option.iter oc_opt Out_channel.flush;
      Bench_utils.Target_progress.tick prog;  (* ← 変異1件完了ごとに更新 *)
    )
    with
    | Failure message -> Format.fprintf fmt "Failure: %s\n" message
    | Translate.Translation_bug str -> Format.fprintf fmt "translation_bug: %s\n" str
    | Syntax.Blame _ -> Format.fprintf fmt "evaluation blame \n"
    | Eval.Eval_bug _ -> Format.fprintf fmt "evaluation bug!! \n"
    | _ -> Format.fprintf fmt "some error was happened\n"
  );

  Option.iter oc_opt Out_channel.close;

  (match json_oc, Bench_utils.out_mode with
    | None, _ -> ()
    | Some oc, JsonLines -> Out_channel.close oc
    | Some oc, Json ->
       Out_channel.output_string oc "\n]}\n"; Out_channel.close oc
    | Some _, Text -> raise @@ Failure "yet");

  if config.compile then Pipeline.build_run_bench ~log_dir ~file ~mode_str:(string_of_mode mode) ~itr ~mutants_length:(List.length mutants) ~intoB:config.intoB ~alt:config.alt ~eager:config.eager ~static:config.static;

  (* ターゲットの進捗バーを確定（改行しない） *)
  Bench_utils.Target_progress.print ~final:false prog

let () =
  (* 1. 前処理: 全ファイルを parse→mutate *)
  Printf.fprintf stdout "debug: parse->mutate\n";
  let prepared : (string * Syntax.ITGL.program list) list =
    List.map files (fun file -> (file, parse_and_mutate file))
  in
    Printf.fprintf stdout "debug: parse->mutate done\n";

  (* モード展開してターゲット配列を作る *)
  Printf.fprintf stdout "debug: making targets lists\n";
  let targets : (string * mode * Syntax.ITGL.program list) list =
    List.concat_map prepared ~f:(fun (file, muts) ->
      List.map modes ~f:(fun m -> (file, m, muts))
    )
  in
  Printf.fprintf stdout "debug: making targets lists done\n";
  Printf.fprintf stdout "debug: targets lists number is %d\n" (List.length targets);
  Printf.fprintf stdout "debug: first target's mutants number is %d\n" (match targets with (_, _, h) :: _ -> List.length h | _ -> 0);
  let total_targets = List.length targets in

  (* 2. ログディレクトリ準備 *)
  let tm = localtime (time ()) in
  let timestamp =
    Printf.sprintf "%04d%02d%02d-%02d:%02d:%02d"
      (tm.tm_year + 1900) (tm.tm_mon + 1) tm.tm_mday (tm.tm_hour) (tm.tm_min) (tm.tm_sec)
  in
  let log_dir = Printf.sprintf "%s/%s" log_base_dir timestamp in
  if not (Sys_unix.file_exists_exn log_base_dir) then Core_unix.mkdir log_base_dir;
  if not (Sys_unix.file_exists_exn log_dir) then Core_unix.mkdir log_dir;

  Printf.fprintf stdout "debug: main iteration\n";
  (* 3. 実行: 各ターゲットを順番に *)
  List.iteri targets ~f:(fun i (file, mode, mutants) ->
    bench_file_mode
      ~log_dir
      ~ordinal:(i + 1)
      ~total_targets
      ~file
      ~mode
      ~mutants
  );
  Printf.printf "\n";
  Printf.printf "debug: everything was done\n"
