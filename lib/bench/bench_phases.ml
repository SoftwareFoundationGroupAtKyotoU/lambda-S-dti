(* Preprocessing phases 1-6 shared by bin/bench.ml and test/check_mutants.ml:
   resolve restrictions -> check sources -> check inputs -> parse -> match slots -> mutate.
   Each phase collects every target's errors and aborts at the end of that phase if any. *)

open Bench_target

(* ==================== フェーズ実行 ==================== *)

(* Run one phase: print its header, then print all errors and exit 1 if any were collected. *)
let run ~(num : int) ~(name : string) (f : unit -> 'a * string list) : 'a =
  Format.printf "@.=== [Phase %d] %s ===@." num name;
  let v, errors = f () in
  if errors <> [] then begin
    Format.eprintf "@.[Abort at phase %d: %s] %d error(s):@." num name (List.length errors);
    List.iter (fun e -> Format.eprintf "  - %s@." e) errors;
    exit 1
  end;
  v

(* Apply f to every item; split the results into successes and all errors. *)
let collect (f : 'a -> ('b, string list) result) (xs : 'a list) : 'b list * string list =
  let rs = List.map f xs in
  (List.filter_map Result.to_option rs,
   List.concat_map (function Ok _ -> [] | Error es -> es) rs)

(* Turn an exception into an error message prefixed with `what`. *)
let guard (what : string) (f : unit -> 'a) : ('a, string list) result =
  try Ok (f ()) with e -> Error [ Printf.sprintf "%s: %s" what (Printexc.to_string e) ]

(* ==================== Phase 1: restriction の解決 ==================== *)

(* Look up each name and build its plan; drop plans with nothing left to measure. *)
let plan ~axes ~gradti ~grift (names : string list) : plan list * string list =
  collect (fun name ->
    match Bench_config.find_target name with
    | None -> Error [ Printf.sprintf "%s: unknown target (see --list)" name ]
    | Some spec -> Ok (plan_of_spec ~axes ~gradti ~grift spec)
  ) names
  |> fun (plans, errors) ->
  let plans =
    List.filter (fun p ->
      p.gradti || needs_grift p || begin
        Format.eprintf "[Skip] %s: nothing left to measure after axis restriction@." (plan_name p);
        false
      end) plans
  in
  (plans, errors)

(* ==================== Phase 2: ソースの存在 ==================== *)

(* Source paths of a plan. *)
let untyped_path p = Bench_config.sample_path ~lang:`Gradti ~typed:false p.spec
let typed_path p = Bench_config.sample_path ~lang:`Gradti ~typed:true p.spec
let grift_path p = Bench_config.sample_path ~lang:`Grift p.spec

(* Source files a plan needs: untyped always; typed/grift only when requested. *)
let required_sources (p : plan) : (string * string) list =
  [ ("untyped source", untyped_path p) ] @
  (if needs_typed p then [ ("typed source", typed_path p) ] else []) @
  (if needs_grift p then [ ("grift source", grift_path p) ] else [])

(* Report every required (description, path) pair whose file does not exist. *)
let check_files (required : plan -> (string * string) list) (plans : plan list) : unit * string list =
  ((), List.concat_map (fun p ->
       List.filter_map (fun (what, path) ->
         if Sys.file_exists path then None
         else Some (Printf.sprintf "%s: %s not found (%s)" (plan_name p) what path)
       ) (required p)
     ) plans)

let check_sources = check_files required_sources

(* ==================== Phase 3: input の存在 ==================== *)

(* stdin files a plan needs, depending on --dynamize / --static / grift. *)
let required_inputs ~dynamize ~static (p : plan) : (string * string) list =
  let name = plan_name p in
  (if (p.gradti && dynamize) || needs_grift p then [ ("input", Bench_config.input_path name) ] else []) @
  (if static && (p.gradti || needs_grift p) then [ ("static input", Bench_config.input_path ~static:true name) ] else [])

let check_inputs ~dynamize ~static = check_files (required_inputs ~dynamize ~static)

(* ==================== Phase 4: parse ==================== *)

(* Parsed sources of one plan (typed/grift only when needed). *)
type parsed = {
  plan : plan;
  untyped : Syntax.ITGL.program Pipeline.state;
  typed : Syntax.ITGL.program Pipeline.state option;
  grift : Bench_grift.analysis option;
}

(* Parse every top-level statement of a file and bundle them into a single program state. *)
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

(* Parse the untyped source, plus typed/grift sources if the plan needs them. *)
let parse_plan (p : plan) : (parsed, string list) result =
  let name = plan_name p in
  let untyped = guard (name ^ ": parse untyped") (fun () -> parse_bundled (untyped_path p)) in
  let typed =
    if not (needs_typed p) then Ok None
    else guard (name ^ ": parse typed") (fun () -> Some (parse_bundled (typed_path p)))
  in
  (* grift 側の返り値型スロットは Gradti 側の let rec に合わせる（Bench_grift.slots_of_define）。
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

(* A parsed plan plus its slot count and the untyped -> typed slot map. *)
type corresponded = {
  parsed : parsed;
  n : int;                              (* untyped のスロット数（= 正準スロット数） *)
  typed_map : int list array option;    (* untyped スロット i → typed スロット番号列（添字 i-1） *)
}

(* Count untyped slots, check the mono_copies names, map untyped slots to typed slots,
   and check that grift has the same slot count. *)
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
      (* Map a mono-copy name (e.g. two0) back to its untyped name (two). *)
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

(* Final output of phases 1-6 for one file: what gets turned into compile targets. *)
type prepared = {
  plan : plan;
  subsets : int list list;              (* untyped のスロット番号での部分集合列（grift と共有） *)
  vm : variant_mutants option;          (* Gradti 側を測らない場合 None *)
  grift : Bench_grift.analysis option;
}

(* Choose the slot subsets once, then build the untyped (and typed) mutants from them. *)
let mutate_corresponded (c : corresponded) : (prepared, string list) result =
  let x = c.parsed in
  let name = plan_name x.plan in
  let subsets =
    Mutate.subsets_auto ~threshold:Bench_config.mutation_slot_threshold
      ~samples_per_slot:Bench_config.samples_per_slot c.n
  in
  let ppf = Utils.Format.empty_formatter in
  let vm =
    if not x.plan.gradti then Ok None
    else
      let untyped = guard (name ^ ": mutate untyped") (fun () -> Pipeline.mutate_with_indices ppf x.untyped subsets) in
      let typed =
        match x.typed, c.typed_map with
        | Some typed, Some map ->
          (* Translate an untyped slot subset into the matching typed slot numbers. *)
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

(* Run phases 1-6 in order; returns only when every phase succeeded. *)
let prepare_all ~axes ~dynamize ~static ~grift (names : string list) : prepared list =
  let gradti = dynamize || static in
  let plans = run ~num:1 ~name:"resolve restrictions" (fun () -> plan ~axes ~gradti ~grift names) in
  run ~num:2 ~name:"check sources" (fun () -> check_sources plans);
  run ~num:3 ~name:"check inputs" (fun () -> check_inputs ~dynamize ~static plans);
  let parsed = run ~num:4 ~name:"parse" (fun () -> parse plans) in
  let corresponded = run ~num:5 ~name:"slot correspondence" (fun () -> correspond parsed) in
  run ~num:6 ~name:"mutate" (fun () -> mutate corresponded)

(* Keep only files measured on the Gradti side, paired with their mutants. *)
let gradti_prepared (ps : prepared list) : (plan * variant_mutants) list =
  List.filter_map (fun p -> Option.map (fun vm -> (p.plan, vm)) p.vm) ps
