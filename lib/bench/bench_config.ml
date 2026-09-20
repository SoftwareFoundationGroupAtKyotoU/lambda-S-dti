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
}

let no_restriction = { eager_only = None; monotonic_only = None; tvs_only = None }

let pure_functional_bench = { eager_only = Some false; monotonic_only = Some true; tvs_only = None }

let inpure_bench_without_eagerness = { eager_only = Some false; monotonic_only = None; tvs_only = None }

(* tvs_only の値は投機的な判断ではなく、investigate/check_tvs.ml で
   実際に mode=A(alt+lazy+hash+monotonic) の mutant1 を tvs_opt=true/false
   それぞれでコンパイルし、生成された C が完全一致するかを確認して決めた
   (再帰的な自己参照が AppTy を通じて型変数を「使用済み」に戻すケースが
   あるため、ソースを読むだけでは判定を誤りうる — 例: quicksort は
   swap が単相なのに全体としては DIFFERS になる)。 *)
let restrictions : (string * axis_restriction) list = [
  "church-65532", pure_functional_bench;                                    (* DIFFERS *)
  "evenodd",      { pure_functional_bench with tvs_only = Some true };
  "fib",          { pure_functional_bench with tvs_only = Some true };
  "loop-mono",    { pure_functional_bench with tvs_only = Some true };
  "loop",         pure_functional_bench;                                    (* DIFFERS *)
  "array",        { inpure_bench_without_eagerness with tvs_only = Some true };
  "matmult",      { inpure_bench_without_eagerness with tvs_only = Some true };
  "quicksort",    inpure_bench_without_eagerness;                           (* DIFFERS *)
  "tak",          { pure_functional_bench with tvs_only = Some true };
  "fold",         { no_restriction with tvs_only = Some true };
  "fold-mono",    { no_restriction with tvs_only = Some true };
  "incsum",       { no_restriction with tvs_only = Some true };
  "map",          { no_restriction with tvs_only = Some true };
  "map-mono",     { no_restriction with tvs_only = Some true };
  "mklist",       { no_restriction with tvs_only = Some true };
  "zipwith",      { no_restriction with tvs_only = Some true };
  "zipwith-mono", { no_restriction with tvs_only = Some true };
  (* church-2/church-4/fsm: DIFFERS, and no other axis restriction applies,
     so they are intentionally absent (resolve to no_restriction). *)
]

let restriction_of (file : string) : axis_restriction =
  match List.assoc_opt file restrictions with
  | Some r -> r
  | None -> no_restriction