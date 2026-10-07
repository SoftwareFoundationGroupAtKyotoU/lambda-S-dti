let default_itr = 500
(* Untimed warm-up runs per mutant before the timed iterations, for our drivers and
   grift's alike (without it, grift's first iterations run ~1.8x slower). *)
let warmup = 5
let log_root = "logs"

(* フェーズ 9（計測）で実行するバイナリを固定する CPU 番号（--cpu）。
   コア毎に動作周波数が違う(例: 2.0GHz と 3.9GHz)ため、固定しないと同じ
   バイナリでもプロセス毎に実行時間が 2 倍程度ばらつく。コンパイル
   (フェーズ 8)には適用しないので、並列コンパイルは全コアを使える。 *)
let run_cpu : int option ref = ref None

(* 計測用の実行コマンドの先頭に付けるプレフィックス *)
let run_prefix () =
  match !run_cpu with
  | None -> ""
  | Some n -> Printf.sprintf "taskset -c %d " n

(* スロット数 n が大きい対象（GTP_benchmark の fsm や、grift_benchmark の
   blacksholes/fft/n_body/ray 等）では、全部分集合 (2^n 通り) の列挙が
   非現実的になる。スイートに関係なく、スロット数が mutation_slot_threshold
   以上の対象は Mutate.subsets_auto が自動的にサンプリング（fully-typed /
   fully-dynamic の両端を残しつつ残りをランダム抽出、合計ちょうど
   samples_per_slot * n）に切り替える。 *)
let mutation_slot_threshold = 6
let samples_per_slot = 10

type suite = Original | GriftBenchmark | GtpBenchmark

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
  (* false = grift 比較の対象外（.grift を持たない等）。true のまま .grift が
     無ければ、--grift 時にソース存在確認フェーズでエラーになる。 *)
  grift : bool;
}

let no_restriction = { eager_only = None; monotonic_only = None; tvs_only = None; grift = true }

let pure_functional_bench = { no_restriction with eager_only = Some false; monotonic_only = Some true }

let inpure_bench_without_eagerness = { no_restriction with eager_only = Some false }

(* 1 ベンチマーク対象の設定。
   mono_copies: typed ソースで、untyped では多相に使われている関数を単相版に
   複製している場合の対応表 (untyped 側の let 束縛名, typed 側の複製名たち)。
   untyped/typed のスロット対応付け（Mutate.correspond）で複製名を元の名前に
   読み替えるのに使う。書かれた名前がソースに無ければエラーになる。 *)
type target_spec = {
  name : string;
  suite : suite;
  restriction : axis_restriction;
  mono_copies : (string * string list) list;
}

let target ?(mono_copies = []) suite name restriction = { name; suite; restriction; mono_copies }

(* 全ベンチマーク対象（引数なしで ./bench を実行したときの対象でもある）。
   すべての対象に restriction を明示する。
   tvs_only の値は投機的な判断ではなく、investigate/check_tvs.ml で
   実際に mode=A(alt+lazy+hash+monotonic) の mutant1 を tvs_opt=true/false
   それぞれでコンパイルし、生成された C が完全一致するかを確認して決める
   (再帰的な自己参照が AppTy を通じて型変数を「使用済み」に戻すケースが
   あるため、ソースを読むだけでは判定を誤りうる — 例: quicksort は
   swap が単相なのに全体としては DIFFERS になる)。 *)
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
  (* church-65536 に mult と sixteen を足して 65536 * 16 を計算する *)
  target Original "church-1048576"     { no_restriction with grift = false }
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

(* 既定のベンチ対象（all_targets）には含めないが、名前を明示すれば
   ./bench や test/check_mutants.exe の対象にできるもの。 *)
let extra_targets : target_spec list = [
  target Original "church-2"           { no_restriction with grift = false };
  target Original "church-4"           { no_restriction with grift = false }
    ~mono_copies:[ "two", ["two0"; "two1"] ];
  target Original "easy"               { no_restriction with grift = false };
  target Original "fsm_check"          { no_restriction with grift = false };  (* 正当性チェック用 *)
]

let all_targets = List.map (fun t -> t.name) targets

let find_target (name : string) : target_spec option =
  List.find_opt (fun t -> t.name = name) (targets @ extra_targets)

let suite_dir = function
  | Original -> "original"
  | GriftBenchmark -> "grift_benchmark"
  | GtpBenchmark -> "GTP_benchmark"

let sample_path ~(lang:[`Gradti | `Grift]) ?(typed=false) (spec : target_spec) : string =
  match lang with
  | `Gradti ->
    let variant = if typed then "typed" else "untyped" in
    Printf.sprintf "samples/src_gradti/%s/%s/%s.ml" variant (suite_dir spec.suite) spec.name
  | `Grift ->
    Printf.sprintf "samples/src_grift/%s/%s.grift" (suite_dir spec.suite) spec.name

let input_path ?(static=false) (target : string) : string =
  Printf.sprintf "samples/input/%s%s.txt" target (if static then "_fs" else "")

let grift_cmd = try Sys.getenv "GRIFT" with Not_found -> "grift"
