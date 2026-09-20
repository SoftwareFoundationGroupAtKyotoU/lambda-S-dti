let default_itr = 500
let log_root = "logs"

let grift_benchmarks = [
  "array";
  (* "blacksholes"; *)
  (* "fft"; *)
  "matmult";
  (* "n-body"; *)
  "quicksort";
  (* "ray"; *)
  (* "sieve"; *)
  "tak";
]
let originals = [
  "church-2";
  "church-4";
  "church-65532";
  (* "easy"; *)
  "evenodd";
  "fib";
  "loop";
  "loop-mono";
  (* original_list *)
  "fold";
  "fold-mono";
  "incsum";
  "map";
  "map-mono";
  "mklist";
  "zipwith";
  "zipwith-mono";
]
let gtp_benchmarks = [
  "fsm";
]
(* GTP_benchmark は型注釈スロット数 n が既存対象（最大でも十数個）より桁違いに
   多くなりうるため、全部分集合 (2^n 通り) の代わりに fully-typed / fully-dynamic
   の両端を残しつつ残りをランダム抽出する（合計はちょうど samples_per_slot * n）。 *)
let gtp_samples_per_slot = 10
let all_targets = grift_benchmarks @ gtp_benchmarks @ originals

type suite = Original | GriftBenchmark | GtpBenchmark

let suite_of (target : string) : suite =
  if List.mem target grift_benchmarks then GriftBenchmark
  else if List.mem target gtp_benchmarks then GtpBenchmark
  else Original

let suite_dir = function
  | Original -> "original"
  | GriftBenchmark -> "grift_benchmark"
  | GtpBenchmark -> "GTP_benchmark"

let sample_path ~(lang:[`Gradti | `Grift]) ?(typed=false) (target : string) : string =
  match lang with
  | `Gradti ->
    let variant = if typed then "typed" else "untyped" in
    Printf.sprintf "samples/src_gradti/%s/%s/%s.ml" variant (suite_dir (suite_of target)) target
  | `Grift ->
    Printf.sprintf "samples/src_grift/%s/%s.grift" (suite_dir (suite_of target)) target

let input_path ?(static=false) (target : string) : string =
  Printf.sprintf "samples/input/%s%s.txt" target (if static then "_fs" else "")

let grift_cmd = try Sys.getenv "GRIFT" with Not_found -> "grift"

type axis_restriction = {
  eager_only : bool option;
  monotonic_only : bool option;
}

let no_restriction = { eager_only = None; monotonic_only = None }

let pure_functional_bench = { eager_only = Some false; monotonic_only = Some true }

let inpure_bench_without_eagerness = { eager_only = Some false; monotonic_only = None }

let restrictions : (string * axis_restriction) list = [
  "church-65532", pure_functional_bench;
  "evenodd",      pure_functional_bench;
  "fib",          pure_functional_bench;
  "loop-mono",    pure_functional_bench;
  "loop",         pure_functional_bench;
  "array",        inpure_bench_without_eagerness;
  "matmult",      inpure_bench_without_eagerness;
  "quicksort",    inpure_bench_without_eagerness;
  "tak",          pure_functional_bench;
]

let restriction_of (file : string) : axis_restriction =
  match List.assoc_opt file restrictions with
  | Some r -> r
  | None -> no_restriction