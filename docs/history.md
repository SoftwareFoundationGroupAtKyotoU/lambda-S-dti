# history — これまでの実装の変遷

[CLAUDE.md](../CLAUDE.md) から参照される用途別ドキュメントの一つ。「何を・なぜやったか」の記録。
使い方は [howto.md](howto.md)、残作業は [todo.md](todo.md) を参照。

**新しい話題ほど上、古い話題ほど下**に並べている。`git log` が正の情報源であり、このファイルおよび [docs/history/](history/) 以下は要約に過ぎない（個々のコミットの詳細は `git log`/`git show` を参照）。著者名の表記は `oshimayuki1124`/`Oshima Yuki`/`Yuki Oshima` などコミットごとに揺れているが、すべて同一人物（`yukioshima11124457@gmail.com`）。

---

## bench のライブラリ化・インタプリタ計測廃止 — `f2a9c0a`（2026-09-02）

単一ファイルだった `bench/bench.ml`（430行超）を `bench_lib` ライブラリ
（`bench_config` / `bench_target` / `bench_runner` / `bench_output` / `bench_progress` /
`bench_json` ＋ `mutate`）と薄い `bench.ml` exe に分割し、`bench_utils.ml`（大半が
デッドコード）を削除。合わせて:

- **インタプリタ計測を bench から撤去**しコンパイル専用に。旧 `mem_json` の
  `Failure "interpreter yet"`、未実装の `Text` out_mode、core_bench ベースの
  メモリ計測（`Fast_alloc` / `CB` / `measure_mem_to_json`）を削除。mutation 後
  プログラムが型付け→キャスト挿入→評価まで通るかの回帰は新設
  `test/test_mutate.ml` の差分カバレッジテストへ移した（[todo.md](todo.md) 参照）。
- **mode 文字列から末尾 `C` を廃止**。旧 `SLHC`/`ALNC`/`STATICENC` の `C` は
  「compiler（インタプリタ `I` の対）」の意で、計測がコンパイル専用になったため不要。
  `full_mode_name` は `<S|A|STATIC><E|L><H|N>`（例 `SLH`）を返す。grift の C
  バックエンドを指す `GRIFTC` の `C` は別意味なので温存。`scripts/benchviz.py` ほか
  `plot_relative.py` / `report_absolute_times.py` / `report_herman.py` /
  `report_ratio_extremes.py` の mode 名参照も追従。
- **JSONL スキーマから `after_insertion` / `after_translation` を廃止**（`benchC/run_grift.py`
  の該当キー出力と consumer 側 `.get(...)` も整理）。1行は
  `mode, mutant_index, after_mutate, times_sec, mem, cast, inference, longest` の8フィールド。
- **`mutate.ml` の TApp 次元を完全除去**。現行 ITGL AST に `TAppExp` は無く、
  `count_tapp_nodes` はスタブ、`n_tapp` / `sel_tapp` / `apply` の `tappc` は常に空を
  引き回す死んだ次元だった。併せて未使用の `drop` / `IntMap` を削除。
- **`samples/` ツリーを再編**: `samples/src/` → `samples/src_gradti/{typed,untyped}/{original,grift_benchmark}/`、
  `samples/src_grift/` も `{original,grift_benchmark}/` に整理。ベンチ対象名を
  `-mono`（ハイフン）に統一し `samples/input/*_mono*.txt` をリネーム、
  `matmult_fs.txt` / `quicksort_fs.txt` / `array_fs.txt` を追加。
- 設定の一部を CLI フラグ化（`--out json|jsonl` / `--list`）。

## clang 最適化レベルの切り替え — `a2c97e2`（2026-08-08）

`Config.t` の `opt_file` フィールドを `file` にリネームし、新たに `opt_level : string`（`-O0`/`-O1`/`-O2`/`-O3`（デフォルト）/`-Os`/`-Oz`/`-Ofast`）を追加。`Config.create` で `valid_opt_levels` に対する妥当性検査を行う。`bin/main.ml` に対応する CLI フラグ（`-O0`〜`-Ofast`）を追加し、`lib/backend/builder.ml` の `build_clang_cmd` はこれまで各箇所にハードコードしていた `-O3` を `config.opt_level` から埋め込むように変更（bench 経由の profile ビルドは `-O0` 固定）。`bench/bench.ml`・`compile_test/dotests.sh` も新しい `file`/`opt_level` 引数名に追従。

## README にシンタックスリファレンスを追加 — `bac28d9`（2026-08-07）

これまで `README.md` の構文一覧が古く（pattern match/list/tuple/reference/array/loop が未記載）、`TODO.md` の内容は古い課題メモが中心だった。README に pattern matching（`match`/`function`、変数・リテラル・wildcard・list/tuple パターンとその入れ子）、list（`[e1; e2; ...]`, `::`）、tuple、reference（`ref`/`!`/`:=`）、array（`Array.make`/`.()`/`Array.length`）、loop（`for`/`while`、いずれも `fun`/`let rec` への脱糖）の構文と、対応する型構文（`list`/`tuple`/`ref`/`array`）を追記。合わせて `TODO.md` を `memo.md` にリネームし、古い内容を削除（現状の残作業は [todo.md](todo.md) に一元化されている）。

## capp のショートサーキット最適化 — `e04b71e`（2026-08-07）

`lib/backend/static_manage.ml` に `fast_inj`/`fast_proj`/`fast_proj_tp` ハッシュテーブルを追加し、`Let (x, Coercion c, ...)` の形で束縛された coercion `c` が「単純な injection」「単純な projection（tag/tuple）」のパターンに一致する場合、変数名 `x` をそのパターンに登録（`register_fast_crc`）。

`toC.ml` の `Cls.CApp (y, z)` 変換時にこのテーブルを引き、該当すれば汎用の `coerce()`/`toplevel_coerce()` 呼び出しではなく、専用の軽量関数（`toplevel_coerce_inj`/`toplevel_coerce_proj`/`toplevel_coerce_proj_tp`、`libC/capp.h`/`capp.c`）を直接呼ぶコードを生成する。これにより injection/projection の大半のケースで crc 構造体の動的ディスパッチを回避できる。

以前の CLAUDE.md には「injection 側のみシングルトン化済み、projection 側は blame 情報を持つため未着手」という TODO が書かれていたが、この commit で projection 側（tag 単体・tuple 双方）にも対応した。ただし「シングルトン化」ではなく「静的に判別可能なパターンを検出してインライン展開する」という別アプローチである点に注意（[todo.md](todo.md) 参照）。

## 二項演算子の表現統一 — `aa5e531`（2026-08-06）

演算子ごとに別コンストラクタを持つ AST（`Add`/`Sub`/... 相当）を `BinOp of binop * exp * exp` に統一。KNorm/Cls/toC/translate/eval/pp/fv/subst 等、パイプライン全段にまたがる変更。新しい二項演算子の追加や既存演算子の挙動変更が1箇所（`binop` 型とそのハンドラ）に閉じるようになった。

## Array（`TyArray` / `Array.make` / `.()` / `Array.length`）— 2026-07-25 〜 2026-08-06

`ref` と同じ設計パターン（`CArray of coercion * coercion` / `CMArray of ty * ty`）で配列を追加。

- `c3480d8`「add Array.length」（08-06）: `LengthExp` を全パイプライン段に追加。`compile_test/original/array/` にテスト一式を新設
- `c14f5ff`「add while, for, and benchmarks for array」（08-06）: `for`/`while` 構文をパーサレベルの脱糖として追加（新規 AST ノードなし）。`bench/` に array 用ベンチマークとサンプル（`matmult.ml`/`quicksort.ml`/`explosion_DTI.ml` 等）を追加
- `fceaaf0`（07-27）: `compile_test/dotests.sh` の高速化、`builder.ml` 拡張
- `f7dfb38`「complete array implementation」（07-27）: k-正規化・クロージャ変換・C バックエンド（`libC/arr.c`/`arr.h` 新設、`capp.c`/`crc.c`/`ty.c` 拡張）まで含めフルパイプライン対応完了
- `013159b`〜`f653ef8`（07-25, 07-26）: ITGL/ty/coercion への `TyArray` 追加、lexer/parser 対応、CC の eval、DTI 対応

## `lib/utils/` の再構成 — 2026-07 中旬〜下旬

`compose`/`normalize_coercion` 等が `lib/interpreter/eval.ml` に同居していた構成から、以下のようにファイル分割された（現行の正確なファイルマップは [CLAUDE.md](../CLAUDE.md) の「主要ファイルと役割」を参照）:

- `lib/utils/coercion.ml` — `compose` などの coercion 演算
- `lib/utils/unify.ml` / `type_utils.ml` — 型の unify・補助演算
- `lib/utils/modify/`（`fresh_tv.ml` / `normalize.ml` / `subst.ml`）— AST を書き換える系の関数群
- `lib/utils/var/`（`fv.ml` / `ftv.ml` / `tv.ml`）— 自由変数・自由型変数・型変数収集系

過去バージョンの CLAUDE.md はこれ以前のフラットな `lib/utils/*.ml` 構成を前提に書かれていたため、ファイルパスの記述が古くなっていた（本ドキュメント作成時に修正）。

## Reference（`ref` / `!` / `:=`）— 2026-05-27 〜 2026-07-25

`CRef of coercion * coercion`（読み出し逆変換 `c_r` + 書き込み変換 `c_w`）と `CMRef of ty * ty`（monotonic 版、型変数の一方向インスタンス化のみ許す）の2種類の coercion で reference を表現。`eed500e`「add refs in syntax and frontend」（05-27）が起点で、途中に下記の issue1/2 対応（多相関数のバグ修正）を挟みつつ `9ac0e3b`（07-25）まで続いた。

- **M1**: `pp_coercion`/`subst_coercion`/`type_of_coercion`/`unify TyRef` の基盤整備
- **M2**: ITGL → CC 翻訳（RefExp/DerefExp/SubstExp）+ CC インタプリタ eval + CC 型検査 + `tv_renew`
- **M3**: `compose` の `CRef`/`CMRef` 対応 + `cast TyRef`。monotonic は Deref/SubstExp の `unify_meet` 機構に透過的に任せ、non-monotonic は `CastRefV` でラップして force 時に解決。このタイミングで「`SubstExp` が代入値でなく古いセルの中身に write coercion を適用していた」バグを修正
- **M4**: k-正規化・クロージャ変換 → C バックエンド。`libC/ref.h`/`ref.c` を `STATIC`/`MONOTONIC`/coercion-wrap 分岐で実装、`capp.c` に `cast()` の `TYREF`・`coerce()` の `REF`（monotonic は `sc_push`/`consume` による suspended-cast キュー）を追加。`crc.c` に `compose_refs`・monotonic 版 `make_s_coercion`、`ty.c` に `unify_meet`/`ty_find`（型変数の union-find 経路圧縮）を実装
- 実装レビューで見つかったバグ（`tget`/`hd`/`tl` が入れ子 monotonic ref の `sc_push` 後に `consume()` を呼んでいなかった、`unify_meet`/`make_s_coercion` の `SUBSTITUTED` ケース漏れ、`make_s_coercion` の `TYTUPLE → DYN` で `G_AR` を誤用していた等）はその場で修正済み

`CMArray`（前述の array 実装）は `CMRef` と対称的な設計として追加された。

## 多相関数のバグ修正（issue1 / issue2）— 2026-06-04〜2026-06-11

ref 実装の途中に割り込む形で行われた、`ref` とは別テーマの作業。ldti コンパイラが一部の多相関数宣言に対応できていなかった問題（`let f x :'a = x` のような宣言を `f (); f 3` のように使うと型エラーになる、旧 `TODO.md` にあった既知の課題）への対応として、クロージャの型変数まわり（`fundef`/`funty`/`AppTyFun`/`MakeTyCls`）を再設計した。

- **7277a4e** (2026-06-11) 不要なコードを削除
- **6648ba7**/**1c9b2dc** (2026-06-04) issue1 用コンパイラテストを追加・修正
- **eda9dae**/**ed55367** (2026-06-04) issue2 用のテスト・インタプリタテストを追加
- **7e09faf** (2026-06-04) funty 対応の修正
- **56ae939** (2026-06-04) `AR` を見るべきところを `LI` で見ていたバグを修正
- **2107f51**/**408225a** (2026-06-04) `tyfun`/`tvs` に伴うテスト修正
- **7e1947f** (2026-06-04) match の型付けを refine、tvs 対応
- **132d23c** (2026-06-04) tvs 周りの修正
- **ff06bab** (2026-06-04) eval を tvs/fundef 対応に修正
- **d24f977** (2026-06-04) int の役割に応じてリネーム、funty 機能を追加
- **b75f824** (2026-06-04) funty の機能追加、クロージャ変換を fundef でまとめる
- **6ad8642** (2026-06-04) kNormal を fundef 対応に修正
- **e755b7e** (2026-06-04) tvs・FunTy を用いて翻訳を修正
- **604ad33** (2026-06-04) `let_tyabses` を `tyabses` にリネーム、構文変更に追従
- **c044622** (2026-06-04) `AppTyFun`/`MakeTyCls`/`FundefTy` を追加（issue2）、kNormal に fundef を追加、`Let` から tvs を除き `Funs` へ
- **ecf1386** (2026-05-29) `A` を `Dual` にリネーム

---

## プレヒストリ（ref / array 以前）

上記より前のすべての作業（2024-11-11〜2026-05-21、著者 `yukioshima11124457@gmail.com` による commit）は、量が多いため作業内容ごとに別ファイルへ分割している。**新しいフェーズから順に**並べる（＝一番下が最初期）。

1. [Phase G — 論文実験・pipeline統合・タプル対応](history/phase-g-pipeline-tuple.md)（2026-04-01〜2026-05-21）
2. [Phase F — grift比較ベンチマーク・静的最適化](history/phase-f-grift-optimization.md)（2026-02-03〜2026-03-16、最大のフェーズ）
3. [Phase E — lambda-S-dtiへの命名統一・CI整備・fully-staticコンパイラ](history/phase-e-rename-ci.md)（2026-01-02〜2026-01-23）
4. [Phase D — Cバックエンド立ち上げ・ベンチマーク基盤](history/phase-d-cbackend-bootstrap.md)（2025-09-27〜2025-12-31）
5. [Phase C — K正規化体系の修正](history/phase-c-knormal-fix.md)（2025-05-07〜2025-06-26）
6. [Phase B — GC導入・多相対応・lambdaS1DTIインタプリタ完成](history/phase-b-gc-polymorphism.md)（2025-01-06〜2025-04-28）
7. [Phase A — 最初期: K正規化・クロージャ変換の基礎実装](history/phase-a-foundation.md)（2024-11-11〜2024-12-07、最も古いフェーズ）
