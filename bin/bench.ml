open Unix
open LambdaCSPolyMP.Utils
open LambdaCSPolyMP

open Support.Error
open Format
open Translation
open Pp

type mode = C | S
let string_of_mode = function
  | C -> "C"
  | S -> "S"

(* ------------------ *)
(* Benchmark settings *)
let itr = 100
let files = [
  (* "church_small"; *)
  (* "church"; *)
  (* "church_big";
  "tak";
  "fib";
  "evenodd";
  "loop";
  "loop_poly";
  "mklist";
  "map";
  "fold";
  "zipwith"; *)
  "polypoly";
]
let modes = [C; S]   (* C と S を両方実行 *)
let log_base_dir = "logs"

(* Measurement options (source-controlled) *)
type mem_mode = Off | Fast | Corebench
let mem_mode : mem_mode = Fast          (* Off | Fast | Corebench *)
let fast_runs = 10                      (* Fast モードの1ミュータントあたりの実行回数 *)
let cb_quota_sec = 0.15                 (* Corebench モード: 1 テストあたりの時間上限(秒) *)
let cb_stabilize_gc_between_runs = false
let cb_silence_stdout = true            (* Core_benchの標準出力(推定時間など)を抑止 *)
let show_progress = true                (* 進捗バーを標準出力に出すか *)

(* 出力フォーマット：Text（従来）, Json（1ファイルに配列）, JsonLines（NDJSON） *)
type out_mode = Text | Json | JsonLines
let out_mode : out_mode = JsonLines  (* 推奨: NDJSON。1行=1ミュータント *)

(* 追加: Text ログを作るか？ *)
let text_log_enabled =
  match out_mode with Text -> true | Json | JsonLines -> false
(* ------------------ *)

let split_pairs lst =
  List.fold_right
    (fun (a, b) (as_list, bs_list) -> (a :: as_list, b :: bs_list))
    lst ([], [])


(* ログの見出し用ヘルパ *)
let log_section (fmt:Format.formatter) (title:string) =
  Format.fprintf fmt "@.@[<v>--- %s ---@]@." title

module J = struct
  open Yojson.Safe

  let strf fmt = Format.asprintf fmt

  let opt f = function None -> `Null | Some x -> f x
  let float_opt = opt (fun x -> `Float x)
  let float x = `Float x
  let int x = `Int x
  let bool b = `Bool b
  let str s = `String s
  let list xs = `List xs
  let obj xs = `Assoc xs

  let to_channel_ln oc (j:Yojson.Safe.t) =
    Yojson.Safe.to_channel oc j; output_char oc '\n'
end



(* === Core_bench を使った alloc/gc/time 抽出 === *)
open Core
module Bench = Core_bench.Bench
module AR   = Bench.Analysis_result
module Reg  = AR.Regression
module Coef = AR.Coefficient
module Var  = Bench.Variable

(* core_bench が出す標準出力を一時的に /dev/null へ退避 *)
let with_silenced_stdout (f : unit -> 'a) : 'a =
  if not cb_silence_stdout then f ()
  else begin
    Out_channel.flush stdout; Out_channel.flush stderr;
    let saved   = Core_unix.dup Core_unix.stdout in
    let devnull = Core_unix.openfile "/dev/null" ~mode:[Core_unix.O_WRONLY] ~perm:0o666 in
    Core_unix.dup2 ~src:devnull ~dst:Core_unix.stdout ();
    Core_unix.close devnull;
    match f () with
    | v ->
        Out_channel.flush stdout;
        Core_unix.dup2 ~src:saved ~dst:Core_unix.stdout ();
        Core_unix.close saved;
        v
    | exception exn ->
        Out_channel.flush stdout;
        Core_unix.dup2 ~src:saved ~dst:Core_unix.stdout ();
        Core_unix.close saved;
        raise exn
  end

module Fast_alloc = struct
  let bytes_per_word =
    match Core.Word_size.word_size with
    | Core.Word_size.W32 -> 4
    | Core.Word_size.W64 -> 8

  let measure_and_log ~fmt ~label ~runs (thunk: unit -> unit) =
    (* Blame 等は事前検出してスキップ *)
    let ok =
      try thunk (); true with
      | LambdaCSPolyMP.EvalC.Blame _ ->
          log_section fmt "mem(fast) skipped"; Format.fprintf fmt "reason: Blame (C)@."; false
      | LambdaCSPolyMP.EvalS.Blame _ ->
          log_section fmt "mem(fast) skipped"; Format.fprintf fmt "reason: Blame (S)@."; false
      | exn ->
          log_section fmt "mem(fast) skipped";
          Format.fprintf fmt "reason: exception = %s@." (Core.Exn.to_string exn);
          false
    in
    if not ok then () else begin
      Gc.full_major ();
      let t0 = Core.Time_ns.now () in
      let s0 = Gc.quick_stat () in
      for _i = 1 to runs do thunk () done;
      Gc.full_major ();
      let s1 = Gc.quick_stat () in
      let dt_ns = Core.Time_ns.Span.to_ns (Core.Time_ns.diff (Core.Time_ns.now ()) t0) in
      let runs_f = Float.of_int runs in
      let per_run_ns = dt_ns /. runs_f in
      let fsub a b = a -. b in
      let words_minor = fsub s1.minor_words s0.minor_words /. runs_f in
      let words_major = fsub s1.major_words s0.major_words /. runs_f in
      let words_prom  = fsub s1.promoted_words s0.promoted_words /. runs_f in
      let gc_minor = float (s1.minor_collections - s0.minor_collections) /. runs_f in
      let gc_major = float (s1.major_collections - s0.major_collections) /. runs_f in
      let gc_comp  = float (s1.compactions        - s0.compactions)        /. runs_f in

      log_section fmt (Printf.sprintf "mem(fast) per run; runs=%d" runs);
      Format.fprintf fmt
        "@[<v2>%s@,\
         time:  %.0f ns/Run@,\
         alloc: minor=%.0f words/Run  major=%.0f words/Run  promoted=%.0f words/Run@,\
         alloc(bytes): minor=%.0f B/Run  major=%.0f B/Run  promoted=%.0f B/Run@,\
         gc:   minor=%.3f /Run  major=%.3f /Run  compactions=%.3f /Run@]@."
        label
        per_run_ns
        words_minor words_major words_prom
        (words_minor *. float bytes_per_word)
        (words_major *. float bytes_per_word)
        (words_prom  *. float bytes_per_word)
        gc_minor gc_major gc_comp
    end
end


module CB = struct
  let bytes_per_word =
    match Core.Word_size.word_size with
    | Core.Word_size.W32 -> 4
    | Core.Word_size.W64 -> 8

  let run_config =
    Bench.Run_config.create
      ~quota:(Bench.Quota.Span (Core.Time.Span.of_sec cb_quota_sec))
      ~stabilize_gc_between_runs:cb_stabilize_gc_between_runs
      ()

  let coef_per_run (reg : Reg.t) : float option =
    Array.find_map (AR.Regression.coefficients reg) ~f:(fun (c : Coef.t) ->
      match Coef.predictor c with
      | `Runs -> Some (Coef.estimate c)
      | _ -> None
    )

  let bench_one_and_log ~fmt ~(cb_label:string) (thunk: unit -> unit) =
    (* プレフライトで例外検出してスキップ *)
    let ok =
      try thunk (); true with
      | LambdaCSPolyMP.EvalC.Blame _ ->
          log_section fmt "core_bench (skipped)"; Format.fprintf fmt "reason: Blame (C)@."; false
      | LambdaCSPolyMP.EvalS.Blame _ ->
          log_section fmt "core_bench (skipped)"; Format.fprintf fmt "reason: Blame (S)@."; false
      | exn ->
          log_section fmt "core_bench (skipped)";
          Format.fprintf fmt "reason: exception = %s@." (Core.Exn.to_string exn);
          false
    in
    if not ok then () else begin
      let test = Bench.Test.create ~name:cb_label (fun () -> thunk ()) in
      let do_measure () =
        let ms = Bench.measure ~run_config [test] in
        match ms with
        | [m] -> Bench.analyze ~analysis_configs:Bench.Analysis_config.default m
        | _   -> Error (Error.of_string "measurement failed")
      in
      let analyzed =
        if cb_silence_stdout then with_silenced_stdout do_measure else do_measure ()
      in
      match analyzed with
      | Ok res ->
          let regs = AR.regressions res in
          let pick (resp : Var.t) : float option =
            Array.find_map regs ~f:(fun r ->
              if Core.Poly.(Reg.responder r = resp)
              then coef_per_run r
              else None)
          in
          let nanos    = pick `Nanos in
          let a_minor  = pick `Minor_allocated in
          let a_major  = pick `Major_allocated in
          let a_prom   = pick `Promoted in
          let gc_minor = pick `Minor_collections in
          let gc_major = pick `Major_collections in
          let gc_comp  = pick `Compactions in
          let w2b = Option.map ~f:(fun w -> w *. float_of_int bytes_per_word) in

          log_section fmt (Printf.sprintf "core_bench (per run; quota=%.2fs; stabilize=%b)"
                             cb_quota_sec cb_stabilize_gc_between_runs);
          Format.fprintf fmt
            "@[<v2>%s@,\
             time:  %s ns/Run@,\
             alloc: minor=%s words/Run  major=%s words/Run  promoted=%s words/Run@,\
             alloc(bytes): minor=%s B/Run  major=%s B/Run  promoted=%s B/Run@,\
             gc:   minor=%s /Run  major=%s /Run  compactions=%s /Run@]@."
            cb_label
            (Option.value_map nanos    ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map a_minor  ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map a_major  ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map a_prom   ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map (w2b a_minor) ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map (w2b a_major) ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map (w2b a_prom ) ~default:"-" ~f:(Printf.sprintf "%.0f"))
            (Option.value_map gc_minor ~default:"-" ~f:(Printf.sprintf "%.3f"))
            (Option.value_map gc_major ~default:"-" ~f:(Printf.sprintf "%.3f"))
            (Option.value_map gc_comp  ~default:"-" ~f:(Printf.sprintf "%.3f"))
      | Error _ ->
          log_section fmt "core_bench (analysis failed)";
          Format.fprintf fmt "n/a@."
    end
end


(* -------- Progress UI -------------------------------------------------- *)
(* -------- Target Progress UI (per file x mode) ------------------------- *)
module Target_progress = struct
  type t = {
    label : string;
    total : int;
    mutable done_ : int;
    start_t : float;
    width : int;
  }

  let create ~label ~total ~ordinal ~total_targets =
    (* 見出しを出してからバーを開始 *)
    Printf.printf "\n==> [%d/%d] %s (%d mutants)\n%!"
      ordinal total_targets label total;
    { label; total; done_ = 0; start_t = gettimeofday (); width = 28 }

  let print ?(final=false) (p:t) =
    if show_progress then begin
      let now     = gettimeofday () in
      let done_i  = p.done_ in
      let total_i = max 1 p.total in
      let frac    = Float.of_int done_i /. Float.of_int total_i in
      let elapsed = now -. p.start_t in
      let eta     = if Float.(frac > 0.0) then elapsed *. (1.0 -. frac) /. frac else Float.nan in
      let filled  = Int.of_float (Float.min 1.0 frac *. Float.of_int p.width) in
      let bar     = (String.make filled '#') ^ (String.make (p.width - filled) '-') in
      Printf.printf "\r%-16s [%s] %d/%d (%.1f%%)  t=%.1fs  ETA:%s%!"
        p.label bar done_i total_i (100. *. frac) elapsed
        (if Float.is_nan eta then " ?" else Printf.sprintf " %.1fs" eta);
      if final then Printf.printf "\n%!";
    end

  let tick (p:t) =
    p.done_ <- p.done_ + 1;
    print p
end

(* -------- Measurement -------------------------------------------------- *)
let measure_execution_time f itr =
  let result = ref [] in
  List.iter
    (List.range 0 itr)
    (fun _ ->
      let start_time = gettimeofday () in
      let v = f () in
      let end_time = gettimeofday () in
      let elapsed_time = end_time -. start_time in
      result := (v, elapsed_time) :: !result);
  !result

let measure_mem_to_json ~label (thunk: unit -> unit) : Yojson.Safe.t option =
  match mem_mode with
  | Off -> None
  | Fast ->
      (* Fast_alloc を呼びなおして値を作る（ログは emit_text_log のときだけ） *)
      let ok =
        try thunk (); true with
        | LambdaCSPolyMP.EvalC.Blame _ -> false
        | LambdaCSPolyMP.EvalS.Blame _ -> false
        | _ -> false
      in
      if not ok then None else begin
        Gc.full_major ();
        let t0 = Core.Time_ns.now () in
        let s0 = Gc.quick_stat () in
        for _i = 1 to fast_runs do thunk () done;
        Gc.full_major ();
        let s1 = Gc.quick_stat () in
        let dt_ns = Core.Time_ns.Span.to_ns (Core.Time_ns.diff (Core.Time_ns.now ()) t0) in
        let runs_f = float fast_runs in
        let per_run_ns = dt_ns /. runs_f in
        let fsub a b = a -. b in
        let words_minor = fsub s1.minor_words s0.minor_words /. runs_f in
        let words_major = fsub s1.major_words s0.major_words /. runs_f in
        let words_prom  = fsub s1.promoted_words s0.promoted_words /. runs_f in
        let gc_minor = float (s1.minor_collections - s0.minor_collections) /. runs_f in
        let gc_major = float (s1.major_collections - s0.major_collections) /. runs_f in
        let gc_comp  = float (s1.compactions        - s0.compactions)        /. runs_f in
        let bytes_per_word =
          match Core.Word_size.word_size with
          | Core.Word_size.W32 -> 4
          | Core.Word_size.W64 -> 8
        in
        let open J in
        Some (obj [
          ("mode", str "fast");
          ("runs", int fast_runs);
          ("time_ns_per_run", float per_run_ns);
          ("alloc_words_per_run",
            obj [("minor", float words_minor); ("major", float words_major); ("promoted", float words_prom)]);
          ("alloc_bytes_per_run",
            obj [("minor", float (words_minor *. float_of_int bytes_per_word));
                 ("major", float (words_major *. float_of_int bytes_per_word));
                 ("promoted", float (words_prom  *. float_of_int bytes_per_word))]);
          ("gc_per_run",
            obj [("minor", float gc_minor); ("major", float gc_major); ("compactions", float gc_comp)]);
        ])
      end
  | Corebench ->
      let open Core in
      let open Bench in
      let open J in
      let test = Test.create ~name:label (fun () -> thunk ()) in
      let do_measure () =
        let ms = Bench.measure ~run_config:CB.run_config [test] in
        match ms with
        | [m] -> Bench.analyze ~analysis_configs:Bench.Analysis_config.default m
        | _   -> Error (Error.of_string "measurement failed")
      in
      let analyzed =
        if cb_silence_stdout then with_silenced_stdout do_measure else do_measure ()
      in
      match analyzed with
      | Error _ -> None
      | Ok res ->
          let regs = AR.regressions res in
          let coef_per_run (reg : Reg.t) : float option =
            Array.find_map (AR.Regression.coefficients reg) ~f:(fun (c : Coef.t) ->
              match Coef.predictor c with
              | `Runs -> Some (Coef.estimate c)
              | _ -> None)
          in
          let pick (resp : Var.t) : float option =
            Array.find_map regs ~f:(fun r ->
              if Core.Poly.(Reg.responder r = resp) then coef_per_run r else None)
          in
          let nanos    = pick `Nanos in
          let a_minor  = pick `Minor_allocated in
          let a_major  = pick `Major_allocated in
          let a_prom   = pick `Promoted in
          let gc_minor = pick `Minor_collections in
          let gc_major = pick `Major_collections in
          let gc_comp  = pick `Compactions in
          let bytes_per_word =
            match Core.Word_size.word_size with
            | Core.Word_size.W32 -> 4
            | Core.Word_size.W64 -> 8
          in
          let w2b = Option.map ~f:(fun w -> w *. float_of_int bytes_per_word) in
          Some (obj [
            ("mode", str "corebench");
            ("quota_sec", J.float cb_quota_sec);
            ("stabilize_gc_between_runs", J.bool cb_stabilize_gc_between_runs);
            ("time_ns_per_run", float_opt nanos);
            ("alloc_words_per_run",
              obj [("minor", float_opt a_minor); ("major", float_opt a_major); ("promoted", float_opt a_prom)]);
            ("alloc_bytes_per_run",
              obj [("minor", float_opt (w2b a_minor));
                   ("major", float_opt (w2b a_major));
                   ("promoted", float_opt (w2b a_prom))]);
            ("gc_per_run",
              obj [("minor", float_opt gc_minor); ("major", float_opt gc_major); ("compactions", float_opt gc_comp)]);
          ])


let bench mode fmt itr decl =
  let tyenv  = []
  and env = [] in
  match mode with
  | C ->
    let open EvalC in
    let _id, _vs, lst_elapsed_time =
      match decl with
      | Syntax.LambdaCPolyMp.Prog _ ->
          let vs, ts =
            measure_execution_time (fun () -> evalP decl env) itr
            |> split_pairs
          in ("-", vs, ts)
      | Syntax.LambdaCPolyMp.Decl (id, _) ->
          let vs, ts =
            measure_execution_time (fun () -> evalP decl env) itr
            |> split_pairs
          in (id, vs, ts)
    in
    lst_elapsed_time

  | S ->
    let open EvalS in
    let translated =
      match decl with
      | Syntax.LambdaCPolyMp.Prog e ->
          Syntax.LambdaSPolyMp.Prog (Translation.transT tyenv e)
      | Syntax.LambdaCPolyMp.Decl (id, e) ->
          Syntax.LambdaSPolyMp.Decl (id, Translation.transT tyenv e)
    in
    log_section fmt "after Translation (λS∀mp)";
    Format.fprintf fmt "%a@." Pp.LambdaSPolyMp.print_rawdecl translated;
    Format.pp_print_flush fmt ();
    let _id, _vs, lst_elapsed_time =
      match decl with
      | Syntax.LambdaCPolyMp.Prog _ ->
          let vs, ts =
            measure_execution_time (fun () -> evalP translated env) itr
            |> split_pairs
          in ("-", vs, ts)
      | Syntax.LambdaCPolyMp.Decl (id, _) ->
          let vs, ts =
            measure_execution_time (fun () -> evalP translated env) itr
            |> split_pairs
          in (id, vs, ts)
    in
    lst_elapsed_time

(* -------- Parsing & mutation (1回で両モードに使い回す) --------------- *)
let parse_and_mutate (file : string) =
  let target_path = Printf.sprintf "samples/%s.gtplc" file in
  let src = In_channel.read_all target_path in
  let lexeme = Lexing.from_string src in
  let tyenv = [] in
  let decl  = Parser.toplevel Lexer.main lexeme in
  let lst_mutated = Mutate.mutate_all (decl tyenv) in
  (* src は今は未使用だが、必要なら返す *)
  (lst_mutated : Syntax.LambdaCPolyMp.program list)

(* -------- 1ファイル × 1モード（ターゲット）を実行 ------------------ *)
let bench_file_mode
    ~log_dir
    ~(ordinal:int)
    ~(total_targets:int)
    ~(file:string)
    ~(mode:mode)
    ~(mutants:Syntax.LambdaCPolyMp.program list)
  =
  let tyenv = [] in
  let oc_opt, fmt =
    if text_log_enabled then
      let file_path =
        Printf.sprintf "%s/%s" log_dir (string_of_mode mode ^ "_" ^ file ^ ".log")
      in
      let oc = Out_channel.create file_path in
      (Some oc, Format.formatter_of_out_channel oc)
    else
      let null_fmt =
        Format.make_formatter (fun _buf _pos _len -> ()) (fun () -> ())
      in
      (None, null_fmt)
  in

  let json_path =
    match out_mode with
    | Text -> None
    | JsonLines -> Some (Printf.sprintf "%s/%s_%s.jsonl" log_dir (string_of_mode mode) file)
    | Json -> Some (Printf.sprintf "%s/%s_%s.json"  log_dir (string_of_mode mode) file)
  in
  let json_oc, json_first =
    match json_path, out_mode with
    | None, _ -> (None, ref true)
    | Some path, JsonLines ->
        let oc = Out_channel.create path in
        (Some oc, ref true)
    | Some path, Json ->
        let oc = Out_channel.create path in
        Out_channel.output_string oc "{ \"file\": \""; Out_channel.output_string oc file; Out_channel.output_string oc "\", ";
        Out_channel.output_string oc "\"mode\": \""; Out_channel.output_string oc (string_of_mode mode); Out_channel.output_string oc "\", ";
        Out_channel.output_string oc "\"settings\": {\"mem_mode\": \""; 
        Out_channel.output_string oc (match mem_mode with Off->"off" | Fast->"fast" | Corebench->"corebench");
        Out_channel.output_string oc "\", \"fast_runs\": "; Out_channel.output_string oc (string_of_int fast_runs);
        Out_channel.output_string oc "}, \"mutants\": [\n";
        (Some oc, ref true)
  in

  (* ターゲット用 Progress を開始 *)
  let label = Printf.sprintf "%s_%s" (string_of_mode mode) file in
  let prog = Target_progress.create
               ~label ~total:(List.length mutants)
               ~ordinal ~total_targets
  in

  let counter = ref 0 in
  List.iteri mutants (fun i p ->
    try( 
      let idx = i + 1 in
      (* ---- Mutant 見出し ---- *)
      Option.iter oc_opt (fun oc ->
        Printf.fprintf oc "\n(*** Mutant %d ***)\n%!" idx
      );

      (* 1) 変異直後（λC∀mp：mutate 後） *)
      log_section fmt "after Mutate (λC∀mp)";
      Format.fprintf fmt "%a@." Pp.LambdaCPolyMp.print_rawdecl p;
      Format.pp_print_flush fmt ();

      Option.iter oc_opt (fun oc ->
        incr counter;
        Printf.fprintf oc "\n(%d):\n" !counter
      );

      (* Coercion insertion *)
      let decl, _ = Insertion.LambdaCPolyMp.insertTypeOfDecl tyenv p in
      log_section fmt "after Insertion (λC∀mp)";
      Format.fprintf fmt "%a@." Pp.LambdaCPolyMp.print_rawdecl decl;
      Format.pp_print_flush fmt ();

      (* Benchmarking *)
      let lst_elapsed_time =
        try bench mode fmt itr decl
        with
        | LambdaCSPolyMP.EvalC.Blame _
        | LambdaCSPolyMP.EvalS.Blame _ -> []
      in

      (* File output of benchmarking score *)
      Option.iter oc_opt (fun oc ->
        match lst_elapsed_time with
        | [] -> Printf.fprintf oc "\n"
        | _  -> List.iter lst_elapsed_time (fun t -> Printf.fprintf oc "%f\n" t)
      );

      (* JSON 出力用に各種文字列へ（※テキストログを出さないモードでも生成できる） *)
      let after_mutate_str    = Format.asprintf "%a" Pp.LambdaCPolyMp.print_rawdecl p in
      let after_insertion_str = Format.asprintf "%a" Pp.LambdaCPolyMp.print_rawdecl decl in
      let after_translation_str =
        match mode with
        | C -> None
        | S ->
            let tyenv = [] in
            let translated =
              match decl with
              | Syntax.LambdaCPolyMp.Prog e ->
                  Syntax.LambdaSPolyMp.Prog (Translation.transT tyenv e)
              | Syntax.LambdaCPolyMp.Decl (id, e) ->
                  Syntax.LambdaSPolyMp.Decl (id, Translation.transT tyenv e)
            in
            Some (Format.asprintf "%a" Pp.LambdaSPolyMp.print_rawdecl translated)
      in

      (* 実行時間（従来の itr 回計測）を JSON に *)
      let times_sec_json =
        J.list (List.map lst_elapsed_time (fun t -> J.float t))
      in

      (* メモリ計測（設定に応じて）を JSON に *)
      let mem_json =
        let label = Printf.sprintf "%s/%s#%d" (string_of_mode mode) file idx in
        match mode with
        | C ->
            let run () = let open EvalC in ignore (evalP decl []) in
            measure_mem_to_json ~label run
        | S ->
            (* 翻訳は上で生成済み after_translation_str 用に2度目の trans を避けたいならキャッシュ可 *)
            let translated =
              match decl with
              | Syntax.LambdaCPolyMp.Prog e ->
                  Syntax.LambdaSPolyMp.Prog (Translation.transT [] e)
              | Syntax.LambdaCPolyMp.Decl (id, e) ->
                  Syntax.LambdaSPolyMp.Decl (id, Translation.transT [] e)
            in
            let run () = let open EvalS in ignore (evalP translated []) in
            measure_mem_to_json ~label run
      in

      (* 1ミュータントの JSON オブジェクト *)
      let mutant_json =
        J.obj [
          ("mutant_index", J.int idx);
          ("after_mutate", J.str after_mutate_str);
          ("after_insertion", J.str after_insertion_str);
          ("after_translation", (match after_translation_str with None -> `Null | Some s -> J.str s));
          ("times_sec", times_sec_json);
          ("mem", (match mem_json with None -> `Null | Some j -> j));
        ]
      in

      (* ファイルへ書き出し *)
      begin match json_oc, out_mode with
      | None, _ -> ()
      | Some oc, JsonLines ->
          J.to_channel_ln oc mutant_json
      | Some oc, Json ->
          if not !json_first then Out_channel.output_string oc ",\n";
          Yojson.Safe.to_channel oc mutant_json;
          json_first := false
      end;


      Option.iter oc_opt Out_channel.flush;
      Target_progress.tick prog;  (* ← 変異1件完了ごとに更新 *)
    )
    with
    | Insertion.TypeError (p, s, tyenv_e, ty) ->
        pr std_formatter ("\n[Type error]\n%a@." ^^ s) print_pos p (Pp.print_type tyenv_e) ty;
    | Insertion.TypeError2 (p, s, _, ty1, ty2) ->
        pr std_formatter ("\n[Type error]\n%a@." ^^ s) print_pos p (Pp.print_rawtype) ty1 (Pp.print_rawtype) ty2;
    | Insertion.CoercionTypeError (p, s, tyenv_e, cty1, cty2) ->
        pr std_formatter ("\n[Type error]\n%a@." ^^ s)
          print_pos p (Pp.print_coercion_type tyenv_e) cty1
          (Pp.print_coercion_type tyenv_e) cty2;
  );

  Option.iter oc_opt Out_channel.close;

  (match json_oc, out_mode with
    | None, _ -> ()
    | Some oc, JsonLines -> Out_channel.close oc
    | Some oc, Json ->
       Out_channel.output_string oc "\n]}\n"; Out_channel.close oc);

  (* ターゲットの進捗バーを確定（改行しない） *)
  Target_progress.print ~final:false prog

let () =
  (* 1. 前処理: 全ファイルを parse→mutate *)
  let prepared : (string * Syntax.LambdaCPolyMp.program list) list =
    List.map files (fun file -> (file, parse_and_mutate file))
  in

  (* モード展開してターゲット配列を作る *)
  let targets : (string * mode * Syntax.LambdaCPolyMp.program list) list =
    List.concat_map prepared ~f:(fun (file, muts) ->
      List.map modes ~f:(fun m -> (file, m, muts))
    )
  in
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

  (* 3. 実行: 各ターゲットを順番に *)
  List.iteri targets ~f:(fun i (file, m, mutants) ->
    bench_file_mode
      ~log_dir
      ~ordinal:(i + 1)
      ~total_targets
      ~file
      ~mode:m
      ~mutants
  );
  Printf.printf "\n";
