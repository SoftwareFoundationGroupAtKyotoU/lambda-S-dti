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
let all_targets = grift_benchmarks @ originals

let sample_path ~(lang:[`Gradti | `Grift]) (target : string) : string =
  let sub = if List.mem target grift_benchmarks then "grift_benchmark" else "original" in
  match lang with
  | `Gradti -> Printf.sprintf "samples/src_gradti/untyped/%s/%s.ml" sub target
  | `Grift  -> Printf.sprintf "samples/src_grift/%s/%s.grift" sub target

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