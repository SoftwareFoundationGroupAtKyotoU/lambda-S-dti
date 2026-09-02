let default_itr = 500
let log_root = "logs"

let grift_benchmarks = [
  (* "array"; *)
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
  (* "church-2"; *)
  (* "church-4"; *)
  (* "church-65532"; *)
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

let input_path ?(fs=false) (target : string) : string =
  Printf.sprintf "samples/input/%s%s.txt" target (if fs then "_fs" else "")

