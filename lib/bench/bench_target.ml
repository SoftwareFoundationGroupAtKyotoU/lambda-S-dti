type mode = S | A | B | STATIC

let string_of_mode = function
  | S -> "S"
  | A -> "A"
  | B -> "B"
  | STATIC -> "STATIC"

type target = {
  file : string; mode : mode; eager : bool; hash : bool; monotonic : bool;
  tvs_opt : bool; typed : bool;
  mutants : Syntax.ITGL.program list;
}

(* typed/untyped 軸のアブレーション用に、1ファイル分の untyped/typed 両方の
   mutant 列をまとめて持つ。Typed 軸が要求されていない場合は typed = None。
   typed の k 番目の mutant は untyped の k 番目と同じスロット選択を
   （Mutate.correspond の対応表経由で）Dyn 化したもの。 *)
type variant_mutants = {
  untyped : Syntax.ITGL.program list;
  typed : Syntax.ITGL.program list option;
}

let restrict_axis (only : bool option) (requested : bool list) : bool list =
  match only with
  | None -> requested
  | Some b -> if List.mem b requested then [b] else []

(* ==================== 軸別アブレーション ====================
   「fully-optimized 基準値(ALHMT)を固定し、要求された軸だけ1つずつ反転する」
   方式でターゲットを作る。複数軸を同時に要求しても軸間の直積は取らない
   (基準点は常に1つだけ)。ベンチ(bin/bench.ml)と正当性チェック
   (test/check_mutants.ml)の両方がこのロジックを共有する。 *)

type axis = Id_opt | Eagerness | Hash | Monotonic | Tvs | Typed

let all_axes = [Id_opt; Eagerness; Hash; Monotonic; Tvs; Typed]

let axis_name = function
  | Id_opt -> "id_opt"
  | Eagerness -> "eagerness"
  | Hash -> "hash"
  | Monotonic -> "monotonic"
  | Tvs -> "tvs"
  | Typed -> "typed"

(* 各軸の CLI フラグと説明。bin/bench.ml と test/check_mutants.ml で共有する。 *)
let axis_flag = function
  | Id_opt -> "--id_opt", "id-specialization (mode A vs S)"
  | Eagerness -> "--eagerness", "eager vs lazy"
  | Hash -> "--hash", "hash-consing on vs off"
  | Monotonic -> "--monotonic", "monotonic vs guarded reference semantics"
  | Tvs -> "--tvs_opt", "tvs_opt on vs off"
  | Typed -> "--typed", "typed/ vs untyped/ sources"

(* 立てられた軸フラグを受け取る Arg spec 群と、Arg.parse 後に要求された
   axis 列を返す関数の組。 *)
let axis_specs () : (Arg.key * Arg.spec * Arg.doc) list * (unit -> axis list) =
  let requested = ref [] in
  let specs = List.map (fun ax ->
    let flag, what = axis_flag ax in
    (flag, Arg.Unit (fun () -> if not (List.mem ax !requested) then requested := ax :: !requested),
     Printf.sprintf " Ablate %s against the untypedALHMT baseline" what)) all_axes
  in
  specs, (fun () -> List.filter (fun ax -> List.mem ax !requested) all_axes)

(* "fully-optimized" 基準値: alt(A) / lazy(L) / hash-consing(H) / monotonic(M) / tvs_opt(T)。
   typed/untyped 軸の基準は untyped — こちらがより一般的な（型注釈を書かない）
   書き方であり、比較の主軸は untypedALHMT に置く。 *)
let baseline_eager = false
let baseline_hash = true
let baseline_monotonic = true
let baseline_tvs_opt = true
let baseline_typed = false

let baseline_target file (vm : variant_mutants) : target =
  { file; mode = A; eager = baseline_eager; hash = baseline_hash;
    monotonic = baseline_monotonic; tvs_opt = baseline_tvs_opt;
    typed = baseline_typed; mutants = vm.untyped }

let flip_target (axis : axis) (vm : variant_mutants) (base : target) : target =
  match axis with
  | Id_opt -> { base with mode = S }
  | Eagerness -> { base with eager = not base.eager }
  | Hash -> { base with hash = not base.hash }
  | Monotonic -> { base with monotonic = not base.monotonic }
  | Tvs -> { base with tvs_opt = not base.tvs_opt }
  | Typed ->
    (match vm.typed with
     | Some typed_mutants -> { base with typed = true; mutants = typed_mutants }
     | None -> invalid_arg "flip_target: typed mutants were not prepared")

(* id_opt/hash/typed には per-file restriction を設けない。
   eagerness/monotonic/tvs は axis_restriction の各フィールドで、
   反転後の値がそのファイルで許可されるかを判定する。typed は要求されたら
   必ず測る（typed ソースが無ければソース存在確認フェーズでエラーになる）。 *)
let axis_allowed (axis : axis) (r : Bench_config.axis_restriction) : bool =
  match axis with
  | Id_opt | Hash | Typed -> true
  | Eagerness -> restrict_axis r.eager_only [not baseline_eager] <> []
  | Monotonic -> restrict_axis r.monotonic_only [not baseline_monotonic] <> []
  | Tvs -> restrict_axis r.tvs_only [not baseline_tvs_opt] <> []

(* ==================== restriction の解決（フェーズ 1） ====================
   ファイルごとに「何を測るか」を restriction だけから確定する。ここで
   除外されたもの（restriction による意図的な除外）は [Skip] の info を
   出すだけでエラーにはしない。以降のフェーズはこの plan が要求するもの
   （ソース・input・typed/grift）が揃っていなければエラーにする。 *)
type plan = {
  spec : Bench_config.target_spec;
  ml : bool;                (* ML 側 (dynamize/static) で ALHMT 基準を測るか *)
  flips : axis list;        (* 基準から反転して測る軸（restriction を通ったもの） *)
  grift_monos : bool list;  (* grift で測る monotonicity（空 = grift 比較しない） *)
}

let plan_name (p : plan) = p.spec.name
let needs_typed (p : plan) = List.mem Typed p.flips
let needs_grift (p : plan) = p.grift_monos <> []

let plan_of_spec ~(axes : axis list) ~(ml : bool) ~(grift : bool) (spec : Bench_config.target_spec) : plan =
  let file = spec.name in
  let r = spec.restriction in
  let ml =
    ml &&
    if restrict_axis r.eager_only [baseline_eager] = [] ||
       restrict_axis r.monotonic_only [baseline_monotonic] = [] ||
       restrict_axis r.tvs_only [baseline_tvs_opt] = [] then begin
      Format.eprintf
        "[Skip] %s: fully-optimized baseline (ALHMT) is incompatible with this file's axis restriction@." file;
      false
    end else true
  in
  let flips =
    if not ml then []
    else List.filter (fun ax ->
      axis_allowed ax r || begin
        Format.eprintf "[Skip] %s: %s axis excluded by this file's axis restriction@." file (axis_name ax);
        false
      end) axes
  in
  (* --grift は軸フラグの有無に関わらず、fully-optimized 基準値の
     monotonic=true(ALHMT の M)側のみで GRIFTCM と比較する独立した計測。 *)
  let grift_monos =
    if not grift then []
    else if not r.grift then begin
      Format.eprintf "[Skip grift] %s: excluded by this file's restriction@." file; []
    end else
      match restrict_axis r.monotonic_only [baseline_monotonic] with
      | [] ->
        Format.eprintf
          "[Skip grift] %s: no monotonic combination survives its axis restriction given the requested flags@." file;
        []
      | ms -> ms
  in
  { spec; ml; flips; grift_monos }

(* ファイルごとに基準ターゲットを1つ生成し、plan で許可された反転軸ごとに
   反転ターゲットを1つ追加する。軸を何個指定しても基準点(ALHMT)は
   ファイルごとに1つしか生成されない(=重複コンパイルしない)。 *)
let expand_ablation_targets (prepared : (plan * variant_mutants) list) : target list =
  List.concat_map (fun ((p : plan), vm) ->
    let base = baseline_target p.spec.name vm in
    base :: List.map (fun ax -> flip_target ax vm base) p.flips
  ) prepared

(* --static 用: 完全静的プログラムでの「fully-optimized(基準+反転) vs
   STATIC モード」比較。dynamize_targets をそのまま使い回すことで、S/A側の
   基準+反転を再計算しない。STATIC 側の基準ターゲットだけファイルごとに
   1つ追加する(Bench_compiler.static_targets が eager/hash/monotonic を
   STATIC 用の固定値に上書きし、mutants を fully-typed の1件に絞る)。 *)
let with_static_baselines (prepared : (plan * variant_mutants) list) (dynamize_targets : target list) : target list =
  List.map (fun ((p : plan), vm) -> { (baseline_target p.spec.name vm) with mode = STATIC }) prepared
  @ dynamize_targets

(* 出力ラベル用の mode 文字列。{typed/untyped}{ALHMT/...} の形にする
   （typed/untyped も他の軸と同じ扱いにする、というアブレーション軸拡張の一部）。 *)
let ablation_mode_str (t : target) : string =
  Printf.sprintf "%s%s%s%s%s%s"
    (if t.typed then "typed" else "untyped")
    (string_of_mode t.mode)
    (if t.eager then "E" else "L")
    (if t.hash then "H" else "h")
    (if t.monotonic then "M" else "G")
    (if t.tvs_opt then "T" else "t")