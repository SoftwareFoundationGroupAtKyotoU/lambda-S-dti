(* Static benchmark settings: the target list, per-target restrictions, and source/input paths. *)

(* Timed iterations per mutant when -i is not given. *)
let default_itr = 500
(* Untimed warm-up runs per mutant before the timed iterations, for our drivers and
   grift's alike (without it, grift's first iterations run ~1.8x slower). *)
let warmup = 5
(* Initial Boehm GC heap (KB) when --heap-size is not given; applied to our binaries
   (-D GC_INITIAL_HEAP_SIZE, in bytes) and to grift (-m <KB>) alike. *)
let default_heap_kb = 8 * 1024
(* Every run writes into logs/<timestamp>/. *)
let log_root = "logs"

(* フェーズ 9（計測）で実行するバイナリを固定する CPU 番号（--cpu）。
   計測中のプロセスがコア間を移動しないようにする。どのコアも同じ性能で、
   周波数は負荷に応じて動的に変わる（schedutil）ので、固定しても周波数は
   揃わない（立ち上がりは warmup で吸収する）。コンパイル（フェーズ 8）には
   適用しないので、並列コンパイルは全コアを使える。 *)
let run_cpu : int option ref = ref None

(* 計測用の実行コマンドの先頭に付けるプレフィックス *)
let run_prefix () =
  match !run_cpu with
  | None -> ""
  | Some n -> Printf.sprintf "taskset -c %d " n

(* Targets with >= mutation_slot_threshold slots are sampled
   (samples_per_slot * n mutants) instead of enumerating all 2^n. *)
let mutation_slot_threshold = 6
let samples_per_slot = 10

(* Benchmark suite = subdirectory under samples/src_gradti/{typed,untyped}/ and samples/src_grift/. *)
type suite = Original | GriftBenchmark | GtpBenchmark

(* Per-target limits on which configurations may be measured.
   `Some b` pins that axis to b (flipping it away from b is skipped); None = unrestricted. *)
type axis_restriction = {
  (* Some false = never measure eager. *)
  eager_only : bool option;
  (* Some true = never measure guarded (non-monotonic) references. *)
  monotonic_only : bool option;
  (* Some true = this benchmark provably has no let-bound function whose
     tvs_opt-prunable type variables actually survive Ftv.KNorm.ftv_fund
     (lib/utils/var/ftv.ml) — i.e. toggling tvs_opt produces byte-identical
     generated C, so the tvs_opt=false ("t") measurement is redundant.
     Determined empirically (compiling mutant 1 under mode=A with
     tvs_opt on/off and diffing the generated C), not by inspection alone,
     since recursive self-calls to a polymorphic function can reintroduce
     an AppTy node that keeps a type variable "used" even when the body
     never touches a ref/array/cast. *)
  tvs_only : bool option;
  (* Whether to run the grift comparison. *)
  grift : bool;
}

(* Measure everything, including the grift comparison. *)
let no_restriction = { eager_only = None; monotonic_only = None; tvs_only = None; grift = true }

(* Preset restrictions (currently not referenced by any target). *)
let pure_functional_bench = { no_restriction with eager_only = Some false; monotonic_only = Some true }

let inpure_bench_without_eagerness = { no_restriction with eager_only = Some false }

(* One benchmark program: name, suite, restriction, and the typed-source mono-copy table. *)
type target_spec = {
  name : string;
  suite : suite;
  restriction : axis_restriction;
  mono_copies : (string * string list) list;
}

(* Shorthand constructor used by the tables below. *)
let target ?(mono_copies = []) suite name restriction = { name; suite; restriction; mono_copies }

(* Default target list (what ./bench runs with no file arguments). *)
let targets : target_spec list = [
  (* ---- grift_benchmark ---- *)
  target GriftBenchmark "array"        no_restriction;
  target GriftBenchmark "blacksholes"  no_restriction;
  target GriftBenchmark "fft"          no_restriction;
  target GriftBenchmark "matmult"      no_restriction;
  target GriftBenchmark "n_body"       no_restriction;
  target GriftBenchmark "quicksort"    no_restriction;  (* DIFFERS *)
  target GriftBenchmark "ray"          no_restriction;
  (* target GriftBenchmark "sieve"     no_restriction; *)
  target GriftBenchmark "tak"          no_restriction;
  (* ---- GTP_benchmark ---- *)
  target GtpBenchmark   "fsm"          { no_restriction with grift = false };  (* DIFFERS *)
  (* ---- original ---- *)
  target Original "church-65536"       { no_restriction with grift = false }   (* DIFFERS *)
    ~mono_copies:[ "exp",  ["exp0"; "exp1"];
                   "two",  ["two0"; "two1"; "two2"];
                   "four", ["four0"; "four1"] ];
  target Original "evenodd"            no_restriction;
  target Original "fib"                no_restriction;
  target Original "loop"               no_restriction;  (* DIFFERS *)
  (* original_list *)
  target Original "fold"               { no_restriction with grift = false };
  target Original "incsum"             { no_restriction with grift = false };
  target Original "map"                { no_restriction with grift = false };
  target Original "mklist"             { no_restriction with grift = false };
  target Original "zipwith"            { no_restriction with grift = false };
]

(* Targets that run only when named explicitly. *)
let extra_targets : target_spec list = [
  target Original "church-2"           { no_restriction with grift = false };
  target Original "church-4"           { no_restriction with grift = false }
    ~mono_copies:[ "two", ["two0"; "two1"] ];
  target Original "easy"               { no_restriction with grift = false };
  target Original "fsm_check"          { no_restriction with grift = false };  (* 正当性チェック用 *)
]

(* Names of the default targets (used when no file is given, and by --list). *)
let all_targets = List.map (fun t -> t.name) targets

(* Look up a target by name in both the default and the extra lists. *)
let find_target (name : string) : target_spec option =
  List.find_opt (fun t -> t.name = name) (targets @ extra_targets)

(* Directory name of a suite. *)
let suite_dir = function
  | Original -> "original"
  | GriftBenchmark -> "grift_benchmark"
  | GtpBenchmark -> "GTP_benchmark"

(* Source path: samples/src_gradti/<typed|untyped>/<suite>/<name>.ml or samples/src_grift/<suite>/<name>.grift. *)
let sample_path ~(lang:[`Gradti | `Grift]) ?(typed=false) (spec : target_spec) : string =
  match lang with
  | `Gradti ->
    let variant = if typed then "typed" else "untyped" in
    Printf.sprintf "samples/src_gradti/%s/%s/%s.ml" variant (suite_dir spec.suite) spec.name
  | `Grift ->
    Printf.sprintf "samples/src_grift/%s/%s.grift" (suite_dir spec.suite) spec.name

(* stdin file: samples/input/<name>.txt (dynamize) or <name>_fs.txt (static). *)
let input_path ?(static=false) (target : string) : string =
  Printf.sprintf "samples/input/%s%s.txt" target (if static then "_fs" else "")

(* stdin file for test/check_mutants.ml (file is <name> or <name>_fs): samples/input/check/<file>.txt
   if it exists, else the benchmark input. The check only compares outputs, so heavy targets get a
   small input there; compile_test/mutation_test.sh's expected values follow it. *)
let check_input_path (file : string) : string =
  let small = Printf.sprintf "samples/input/check/%s.txt" file in
  if Sys.file_exists small then small else Printf.sprintf "samples/input/%s.txt" file

(* grift executable; override with the GRIFT environment variable. *)
let grift_cmd = try Sys.getenv "GRIFT" with Not_found -> "grift"
