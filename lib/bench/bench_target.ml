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
   mutant 列をまとめて持つ。typed ソースが無い（あるいは呼び出し側が
   Typed 軸を要求していない）場合は typed = None。 *)
type variant_mutants = {
  untyped : Syntax.ITGL.program list;
  typed : Syntax.ITGL.program list option;
}

(* -------- Parsing & mutation (1回で両モードに使い回す) --------------- *)
let parse_bundled ?(typed=false) (file : string) : Syntax.ITGL.program Pipeline.state =
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
  Pipeline.bundle_states_ITGL states

let parse_and_mutate ?(typed=false) (file : string) : Syntax.ITGL.program list =
  let state = parse_bundled ~typed file in
  (* スイートに関係なく、スロット数だけを見て全列挙かサンプリングかを決める
     （Bench_config.mutation_slot_threshold 参照）。 *)
  Pipeline.mutate_auto
    ~threshold:Bench_config.mutation_slot_threshold
    ~samples_per_slot:Bench_config.samples_per_slot
    Utils.Format.empty_formatter state

(* ML 側で let rec 定義されている関数名。grift 側の返り値型スロットの有無を
   これに合わせる（Bench_grift.prepare 参照）。let rec の名前は typed/untyped
   で共通なので、常に存在する untyped ソースから取る。 *)
let fix_names (file : string) : string list =
  Pipeline.fix_names (parse_bundled file)

let restrict_axis (only : bool option) (requested : bool list) : bool list =
  match only with
  | None -> requested
  | Some b -> if List.mem b requested then [b] else []

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

(* 前処理: 全ファイルを parse→mutate。対象ソースが存在しない場合は
   （例: untyped/GTP_benchmark/ がまだ無い等）他の対象を巻き込んで
   落ちないよう、[Skip] 警告を出してそのターゲットだけ除外する。
   比較の主軸は untypedALHMT なので untyped は常に読む。typed/ 側は
   Typed 軸が要求されたときだけ（存在すれば）追加で読む。 *)
let prepare ~(axes : axis list) (files : string list) : (string * variant_mutants) list =
  List.filter_map (fun file ->
    let untyped_path = Bench_config.sample_path ~lang:`Gradti ~typed:false file in
    if not (Sys.file_exists untyped_path) then begin
      Format.eprintf "[Skip] %s: sample not found (%s)@." file untyped_path;
      None
    end else begin
      let untyped = parse_and_mutate ~typed:false file in
      let typed =
        if not (List.mem Typed axes) then None
        else
          let typed_path = Bench_config.sample_path ~lang:`Gradti ~typed:true file in
          if Sys.file_exists typed_path then Some (parse_and_mutate ~typed:true file)
          else begin
            Format.eprintf "[Skip] %s: typed sample not found (%s); typed axis unavailable for this target@." file typed_path;
            None
          end
      in
      Some (file, { untyped; typed })
    end
  ) files

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
     | None -> base (* axis_allowed already filters this case out *))

(* id_opt/hash には per-file restriction を設けない(要件通り)。
   eagerness/monotonic/tvs は既存の axis_restriction フィールドで、
   反転後の値がそのファイルで許可されるかを判定する。typed は
   typed/ ソースが実際に存在し、かつ呼び出し側が用意できていた場合のみ許可する。 *)
let axis_allowed (axis : axis) (r : Bench_config.axis_restriction) (vm : variant_mutants) (base : target) : bool =
  match axis with
  | Id_opt | Hash -> true
  | Eagerness -> restrict_axis r.eager_only [not base.eager] <> []
  | Monotonic -> restrict_axis r.monotonic_only [not base.monotonic] <> []
  | Tvs -> restrict_axis r.tvs_only [not base.tvs_opt] <> []
  | Typed -> vm.typed <> None

(* ファイルごとに基準ターゲットを1つ生成し、要求された axes それぞれに
   ついて許可されれば反転ターゲットを1つ追加する。呼び出し側(bin/bench.ml)
   は全軸フラグをまとめてこの関数に一度だけ渡すこと — そうすることで
   軸を何個指定しても基準点(ALHMT)の重複コンパイルを避けられる。 *)
let expand_ablation_targets ~(axes : axis list) (prepared : (string * variant_mutants) list) : target list =
  List.concat_map (fun (file, vm) ->
    let r = Bench_config.restriction_of file in
    let base = baseline_target file vm in
    if restrict_axis r.eager_only [base.eager] = [] ||
       restrict_axis r.monotonic_only [base.monotonic] = [] ||
       restrict_axis r.tvs_only [base.tvs_opt] = [] then begin
      Format.eprintf
        "[Skip] %s: fully-optimized baseline (ALHMT) is incompatible with this file's axis restriction@." file;
      []
    end else
      base :: List.filter_map (fun ax ->
        if axis_allowed ax r vm base then Some (flip_target ax vm base)
        else begin
          Format.eprintf
            "[Skip] %s: %s axis excluded by this file's axis restriction@." file (axis_name ax);
          None
        end) axes
  ) prepared

(* --static 用: 完全静的プログラムでの「fully-optimized(基準+反転) vs
   STATIC モード」比較。dynamize_targets をそのまま使い回すことで、S/A側の
   基準+反転を再計算しない。STATIC 側の基準ターゲットだけファイルごとに
   1つ追加する(Bench_compiler.static_targets が eager/hash/monotonic を
   STATIC 用の固定値に上書きし、mutants を fully-typed の1件に絞る)。 *)
let with_static_baselines (prepared : (string * variant_mutants) list) (dynamize_targets : target list) : target list =
  List.map (fun (file, vm) -> { (baseline_target file vm) with mode = STATIC }) prepared
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