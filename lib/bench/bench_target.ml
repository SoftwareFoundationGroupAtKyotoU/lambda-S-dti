type mode = S | A | B | STATIC

(* if you want to measure B, add B in modes *)
let modes = [S; A; STATIC]

let string_of_mode = function
  | S -> "S"
  | A -> "A"
  | B -> "B"
  | STATIC -> "STATIC"

let full_mode_name mode eager hash monotonic =
  Printf.sprintf "%s%s%s%s"
    (string_of_mode mode)
    (if eager     then "E" else "L")
    (if hash      then "H" else "N")
    (if monotonic then "M" else "G")

type target = {
  file : string; mode : mode; eager : bool; hash : bool; monotonic : bool;
  tvs_opt : bool;
  mutants : Syntax.ITGL.program list;
}

(* -------- Parsing & mutation (1回で両モードに使い回す) --------------- *)
let parse_and_mutate ?(typed=false) (file : string) : Syntax.ITGL.program list =
  let path = Bench_config.sample_path ~lang:`Gradti ~typed file in
  let ppf = Utils.Format.empty_formatter in
  let config = Config.create ~compile:true () in
  let channel, lexbuf = Pipeline.lex ppf (Some path) in
  (* init_state once: it resets Type_env's record-type/field tables as a
     side effect, so calling it per statement would forget any `type ... = { ... }`
     declared earlier in the same file by the time a later statement refers to it. *)
  let init_state = Pipeline.init_state () ~config in
  let rec loop acc =
    match Pipeline.parse ppf lexbuf init_state with
    | state -> loop (state :: acc)
    | exception Lexer.Eof -> acc
  in
  let states = loop [] in
  close_in channel;
  let state = Pipeline.bundle_states_ITGL states in
  match Bench_config.suite_of file with
  | Bench_config.GtpBenchmark ->
    (* GTP_benchmark 対象は型注釈スロット数が既存対象より桁違いに多く、
       全部分集合の全列挙 (2^n 通り) では計算不能になりうるためサンプリングする。 *)
    Pipeline.mutate_sampled ~samples_per_slot:Bench_config.gtp_samples_per_slot ppf state
  | Bench_config.Original | Bench_config.GriftBenchmark ->
    Pipeline.mutate_all ppf state

let restrict_axis (only : bool option) (requested : bool list) : bool list =
  match only with
  | None -> requested
  | Some b -> if List.mem b requested then [b] else []

let expand_targets ~eagernesses ~hash_modes ~monotonicities (prepared : (string * Syntax.ITGL.program list) list) : target list =
  List.concat_map (fun (file, mutants) ->
    let r = Bench_config.restriction_of file in
    let file_eagernesses = restrict_axis r.eager_only eagernesses in
    let file_monotonicities = restrict_axis r.monotonic_only monotonicities in
    if file_eagernesses = [] || file_monotonicities = [] then begin
      Format.eprintf
        "[Skip] %s: no (eager,monotonic) combination survives its axis restriction given the requested flags@." file;
      []
    end else
      List.concat_map (fun mode ->
        List.concat_map (fun eager ->
          List.concat_map (fun hash ->
            List.map (fun monotonic ->
              { file; mode; eager; hash; monotonic; tvs_opt = false; mutants }
            ) file_monotonicities
          ) hash_modes
        ) file_eagernesses
      ) modes
  ) prepared

let restrict_grift_targets ~monotonicities files =
  List.concat_map (fun file ->
    let r = Bench_config.restriction_of file in
    let file_monotonicities = restrict_axis r.monotonic_only monotonicities in
    if file_monotonicities = [] then begin
      Format.eprintf
        "[Skip grift] %s: no monotonic combination survives its axis restriction given the requested flags@." file;
      []
    end else
      List.map (fun b -> (file, b)) file_monotonicities
  ) files

(* ==================== 軸別アブレーション ====================
   総当たり(expand_targets)の代わりに、「fully-optimized 基準値(ALHMT)を
   固定し、要求された軸だけ1つずつ反転する」方式でターゲットを作る。
   複数軸を同時に要求しても軸間の直積は取らない(基準点は常に1つだけ)。 *)

type axis = Id_opt | Eagerness | Hash | Monotonic | Tvs

let axis_name = function
  | Id_opt -> "id_opt"
  | Eagerness -> "eagerness"
  | Hash -> "hash"
  | Monotonic -> "monotonic"
  | Tvs -> "tvs"

(* "fully-optimized" 基準値: alt(A) / lazy(L) / hash-consing(H) / monotonic(M) / tvs_opt(T) *)
let baseline_eager = false
let baseline_hash = true
let baseline_monotonic = true
let baseline_tvs_opt = true

let baseline_target file mutants : target =
  { file; mode = A; eager = baseline_eager; hash = baseline_hash;
    monotonic = baseline_monotonic; tvs_opt = baseline_tvs_opt; mutants }

let flip_target (axis : axis) (base : target) : target =
  match axis with
  | Id_opt -> { base with mode = S }
  | Eagerness -> { base with eager = not base.eager }
  | Hash -> { base with hash = not base.hash }
  | Monotonic -> { base with monotonic = not base.monotonic }
  | Tvs -> { base with tvs_opt = not base.tvs_opt }

(* id_opt/hash には per-file restriction を設けない(要件通り)。
   eagerness/monotonic/tvs は既存の axis_restriction フィールドで、
   反転後の値がそのファイルで許可されるかを判定する。 *)
let axis_allowed (axis : axis) (r : Bench_config.axis_restriction) (base : target) : bool =
  match axis with
  | Id_opt | Hash -> true
  | Eagerness -> restrict_axis r.eager_only [not base.eager] <> []
  | Monotonic -> restrict_axis r.monotonic_only [not base.monotonic] <> []
  | Tvs -> restrict_axis r.tvs_only [not base.tvs_opt] <> []

(* ファイルごとに基準ターゲットを1つ生成し、要求された axes それぞれに
   ついて許可されれば反転ターゲットを1つ追加する。呼び出し側(bin/bench.ml)
   は全軸フラグをまとめてこの関数に一度だけ渡すこと — そうすることで
   軸を何個指定しても基準点(ALHMT)の重複コンパイルを避けられる。 *)
let expand_ablation_targets ~(axes : axis list) (prepared : (string * Syntax.ITGL.program list) list) : target list =
  List.concat_map (fun (file, mutants) ->
    let r = Bench_config.restriction_of file in
    let base = baseline_target file mutants in
    if restrict_axis r.eager_only [base.eager] = [] ||
       restrict_axis r.monotonic_only [base.monotonic] = [] ||
       restrict_axis r.tvs_only [base.tvs_opt] = [] then begin
      Format.eprintf
        "[Skip] %s: fully-optimized baseline (ALHMT) is incompatible with this file's axis restriction@." file;
      []
    end else
      base :: List.filter_map (fun ax ->
        if axis_allowed ax r base then Some (flip_target ax base)
        else begin
          Format.eprintf
            "[Skip] %s: %s axis excluded by this file's axis restriction@." file (axis_name ax);
          None
        end) axes
  ) prepared

(* 出力ラベル用の mode 文字列。 *)
let ablation_mode_str (t : target) : string =
  Printf.sprintf "%s%s%s%s%s"
    (string_of_mode t.mode)
    (if t.eager then "E" else "L")
    (if t.hash then "H" else "h")
    (if t.monotonic then "M" else "G")
    (if t.tvs_opt then "T" else "t")