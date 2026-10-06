(* ベンチマークの前処理フェーズ群（restriction 解決 → ソース存在 → input 存在 →
   parse → スロット対応 → mutate）。

   各フェーズは全対象を最後まで処理してエラーを集め、エラーが1件でもあれば
   そのフェーズの終わりで全エラーを表示して終了する（run 参照）。
   次のフェーズには進まないので、例えば input が1つ欠けているだけで
   parse・コード生成・clang を最後まで回してから失敗する、ということは無い。
   restriction による意図的な除外は [Skip] の info を出すだけでエラーにしない。

   bin/bench.ml はこの後にコード生成・コンパイル・計測のフェーズを続ける。
   test/check_mutants.ml も prepare_all でここまでを共有する。 *)

open Bench_target

(* ==================== フェーズ実行 ==================== *)

let run ~(num : int) ~(name : string) (f : unit -> 'a * string list) : 'a =
  Format.printf "@.=== [Phase %d] %s ===@." num name;
  let v, errors = f () in
  if errors <> [] then begin
    Format.eprintf "@.[Abort at phase %d: %s] %d error(s):@." num name (List.length errors);
    List.iter (fun e -> Format.eprintf "  - %s@." e) errors;
    exit 1
  end;
  v

(* 対象ごとの結果を (成功した値の列, 全エラー) にまとめる *)
let collect (f : 'a -> ('b, string list) result) (xs : 'a list) : 'b list * string list =
  let rs = List.map f xs in
  (List.filter_map Result.to_option rs,
   List.concat_map (function Ok _ -> [] | Error es -> es) rs)

let guard (what : string) (f : unit -> 'a) : ('a, string list) result =
  try Ok (f ()) with e -> Error [ Printf.sprintf "%s: %s" what (Printexc.to_string e) ]

(* ==================== Phase 1: restriction の解決 ==================== *)

let plan ~axes ~ml ~grift (names : string list) : plan list * string list =
  collect (fun name ->
    match Bench_config.find_target name with
    | None -> Error [ Printf.sprintf "%s: unknown target (see --list)" name ]
    | Some spec -> Ok (plan_of_spec ~axes ~ml ~grift spec)
  ) names
  |> fun (plans, errors) ->
  let plans =
    List.filter (fun p ->
      p.ml || needs_grift p || begin
        Format.eprintf "[Skip] %s: nothing left to measure after axis restriction@." (plan_name p);
        false
      end) plans
  in
  (plans, errors)

(* ==================== Phase 2: ソースの存在 ==================== *)

let untyped_path p = Bench_config.sample_path ~lang:`Gradti ~typed:false p.spec
let typed_path p = Bench_config.sample_path ~lang:`Gradti ~typed:true p.spec
let grift_path p = Bench_config.sample_path ~lang:`Grift p.spec

(* ML 側を測らない（grift のみの）場合でも、grift の let rec 対応
   （fix_names）とスロット数の突き合わせに untyped ソースを使う。 *)
let required_sources (p : plan) : (string * string) list =
  [ ("untyped source", untyped_path p) ] @
  (if needs_typed p then [ ("typed source", typed_path p) ] else []) @
  (if needs_grift p then [ ("grift source", grift_path p) ] else [])

let check_files (required : plan -> (string * string) list) (plans : plan list) : unit * string list =
  ((), List.concat_map (fun p ->
       List.filter_map (fun (what, path) ->
         if Sys.file_exists path then None
         else Some (Printf.sprintf "%s: %s not found (%s)" (plan_name p) what path)
       ) (required p)
     ) plans)

let check_sources = check_files required_sources

(* ==================== Phase 3: input の存在 ==================== *)

(* dynamize（ML）と grift の dynamize 計測は <f>.txt、static（ML・grift）は <f>_fs.txt を読む *)
let required_inputs ~dynamize ~static (p : plan) : (string * string) list =
  let name = plan_name p in
  (if (p.ml && dynamize) || needs_grift p then [ ("input", Bench_config.input_path name) ] else []) @
  (if static && (p.ml || needs_grift p) then [ ("static input", Bench_config.input_path ~static:true name) ] else [])

let check_inputs ~dynamize ~static = check_files (required_inputs ~dynamize ~static)

(* ==================== Phase 4: parse ==================== *)

type parsed = {
  plan : plan;
  untyped : Syntax.ITGL.program Pipeline.state;
  typed : Syntax.ITGL.program Pipeline.state option;
  grift : Bench_grift.analysis option;
}

let parse_bundled (path : string) : Syntax.ITGL.program Pipeline.state =
  let ppf = Utils.Format.empty_formatter in
  let config = Config.create ~compile:true () in
  let channel, lexbuf = Pipeline.lex ppf (Some path) in
  Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
    (* init_state once: it resets Type_env's record-type/field tables as a
       side effect, so calling it per statement would forget any `type ... = { ... }`
       declared earlier in the same file by the time a later statement refers to it. *)
    let init_state = Pipeline.init_state () ~config in
    let rec loop acc =
      match Pipeline.parse ppf lexbuf init_state with
      | state -> loop (state :: acc)
      | exception Lexer.Eof -> acc
    in
    Pipeline.bundle_states_ITGL (loop []))

let parse_plan (p : plan) : (parsed, string list) result =
  let name = plan_name p in
  let untyped = guard (name ^ ": parse untyped") (fun () -> parse_bundled (untyped_path p)) in
  let typed =
    if not (needs_typed p) then Ok None
    else guard (name ^ ": parse typed") (fun () -> Some (parse_bundled (typed_path p)))
  in
  (* grift 側の返り値型スロットは ML 側の let rec に合わせる（Bench_grift.slots_of_define）。
     let rec の名前は typed/untyped で共通なので untyped から取る。 *)
  let grift =
    match untyped with
    | Error _ -> Ok None
    | Ok u ->
      if not (needs_grift p) then Ok None
      else guard (name ^ ": parse grift") (fun () ->
        Some (Bench_grift.analyze ~fix_names:(Pipeline.fix_names u) (Bench_grift.read_file (grift_path p))))
  in
  match untyped, typed, grift with
  | Ok untyped, Ok typed, Ok grift -> Ok { plan = p; untyped; typed; grift }
  | _ ->
    Error (List.concat_map (function Ok _ -> [] | Error es -> es)
             [ Result.map ignore untyped; Result.map ignore typed; Result.map ignore grift ])

let parse (plans : plan list) : parsed list * string list = collect parse_plan plans

(* ==================== Phase 5: スロット対応 ==================== *)

type corresponded = {
  parsed : parsed;
  n : int;                              (* untyped のスロット数（= 正準スロット数） *)
  typed_map : int list array option;    (* untyped スロット i → typed スロット番号列（添字 i-1） *)
}

let correspond_parsed (x : parsed) : (corresponded, string list) result =
  let name = plan_name x.plan in
  let prefix = List.map (fun e -> Printf.sprintf "%s: %s" name e) in
  let untyped_t = Pipeline.mutation_term x.untyped in
  let n = Mutate.analyze untyped_t in
  let mono = x.plan.spec.mono_copies in
  (* 対応表に書かれた名前がソースに実在するか *)
  let missing names_in what names =
    List.filter_map (fun f ->
      if List.mem f names_in then None
      else Some (Printf.sprintf "mono_copies: %s is not let-bound in the %s source" f what)
    ) names
  in
  let base_errors = missing (Mutate.let_names untyped_t) "untyped" (List.map fst mono) in
  let typed_result =
    match x.typed with
    | None -> Ok None
    | Some typed ->
      let typed_t = Pipeline.mutation_term typed in
      let copy_errors = missing (Mutate.let_names typed_t) "typed" (List.concat_map snd mono) in
      let canon f =
        match List.find_opt (fun (_, copies) -> List.mem f copies) mono with
        | Some (base, _) -> base
        | None -> f
      in
      (match copy_errors, Mutate.correspond ~untyped:untyped_t ~typed:typed_t ~canon with
       | [], Ok map -> Ok (Some map)
       | errs, Ok _ -> Error errs
       | errs, Error errs' -> Error (errs @ errs'))
  in
  let grift_errors =
    match x.grift with
    | Some a when Bench_grift.n_slots a <> n ->
      [ Printf.sprintf "slot count mismatch: untyped has %d, grift has %d" n (Bench_grift.n_slots a) ]
    | _ -> []
  in
  match base_errors, typed_result, grift_errors with
  | [], Ok typed_map, [] -> Ok { parsed = x; n; typed_map }
  | _ ->
    Error (prefix (base_errors @ (match typed_result with Error es -> es | Ok _ -> []) @ grift_errors))

let correspond (xs : parsed list) : corresponded list * string list = collect correspond_parsed xs

(* ==================== Phase 6: mutate ==================== *)

type prepared = {
  plan : plan;
  subsets : int list list;              (* untyped のスロット番号での部分集合列（grift と共有） *)
  vm : variant_mutants option;          (* ML 側を測らない場合 None *)
  grift : Bench_grift.analysis option;
}

let mutate_corresponded (c : corresponded) : (prepared, string list) result =
  let x = c.parsed in
  let name = plan_name x.plan in
  let subsets =
    Mutate.subsets_auto ~threshold:Bench_config.mutation_slot_threshold
      ~samples_per_slot:Bench_config.samples_per_slot c.n
  in
  let ppf = Utils.Format.empty_formatter in
  let vm =
    if not x.plan.ml then Ok None
    else
      let untyped = guard (name ^ ": mutate untyped") (fun () -> Pipeline.mutate_with_indices ppf x.untyped subsets) in
      let typed =
        match x.typed, c.typed_map with
        | Some typed, Some map ->
          let to_typed s = List.concat_map (fun i -> map.(i - 1)) s |> List.sort_uniq compare in
          guard (name ^ ": mutate typed") (fun () ->
            Some (Pipeline.mutate_with_indices ppf typed (List.map to_typed subsets)))
        | _ -> Ok None
      in
      match untyped, typed with
      | Ok untyped, Ok typed -> Ok (Some ({ untyped; typed } : variant_mutants))
      | _ ->
        Error (List.concat_map (function Ok _ -> [] | Error es -> es)
                 [ Result.map ignore untyped; Result.map ignore typed ])
  in
  Result.map (fun vm -> { plan = x.plan; subsets; vm; grift = x.grift }) vm

let mutate (cs : corresponded list) : prepared list * string list = collect mutate_corresponded cs

(* ==================== Phase 1〜6 をまとめて ==================== *)

let prepare_all ~axes ~dynamize ~static ~grift (names : string list) : prepared list =
  let ml = dynamize || static in
  let plans = run ~num:1 ~name:"resolve restrictions" (fun () -> plan ~axes ~ml ~grift names) in
  run ~num:2 ~name:"check sources" (fun () -> check_sources plans);
  run ~num:3 ~name:"check inputs" (fun () -> check_inputs ~dynamize ~static plans);
  let parsed = run ~num:4 ~name:"parse" (fun () -> parse plans) in
  let corresponded = run ~num:5 ~name:"slot correspondence" (fun () -> correspond parsed) in
  run ~num:6 ~name:"mutate" (fun () -> mutate corresponded)

(* ML 側（dynamize/static）で測る対象だけを取り出す *)
let ml_prepared (ps : prepared list) : (plan * variant_mutants) list =
  List.filter_map (fun p -> Option.map (fun vm -> (p.plan, vm)) p.vm) ps
