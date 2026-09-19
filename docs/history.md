# history — これまでの実装の変遷

[CLAUDE.md](../CLAUDE.md) から参照される用途別ドキュメントの一つ。「何を・なぜやったか」の記録。
使い方は [howto.md](howto.md)、残作業は [todo.md](todo.md) を参照。

**新しい話題ほど上、古い話題ほど下**に並べている。`git log` が正の情報源であり、このファイルおよび [docs/history/](history/) 以下は要約に過ぎない（個々のコミットの詳細は `git log`/`git show` を参照）。著者名の表記は `oshimayuki1124`/`Oshima Yuki`/`Yuki Oshima` などコミットごとに揺れているが、すべて同一人物（`yukioshima11124457@gmail.com`）。

---

## `--static` 時に不要な monotonic dummy range を登録しないように — `5abbac7`（2026-09-19）

`toC_program` が `--static` 指定時にも `monotonic_dummy_range`（後述）を無条件で `RangeManager` に登録していたのを、非 static 時のみに修正。合わせて `compile_test/dotests.sh` の並列実行時競合対策（出力バイナリ名がファイルパス+オプションのみのハッシュのため、同じ組み合わせのテストが同時に走ると衝突する）に `Text file busy` エラーも捕捉してリトライするよう追加。

## deref/subst/get/put 向けの効率的な coercion 生成パス — `46a5692`（2026-09-19）

monotonic reference/array の `Deref`/`Subst`/`Get`/`Put` は、それまでランタイムの `make_s_coercion`（C 関数、実行時型情報 `ty*` の木を毎回たどって `crc` を組み立てる）を毎アクセス呼んでいた。この commit で `toC.ml` に `make_s_coercion_call` を追加し、静的に分かっている片方の型 `u`（ITGL の型注釈から来る）をコンパイル時に再帰的に分解し、`TyDyn` との合流点（実行時 RTTI のタグ判定が必要な葉）だけ `make_s_coercion_from_dyn`/`_to_dyn` 等の専用 C 関数へ、残りは `wrap_list`/`wrap_tuple`/`wrap_fn` で直接組み立てる C コードを生成するように変更（[Phase H の「capp のショートサーキット最適化」](history/phase-h-ref-array-bench-refactor.md)と同じ「静的に分かる部分をインライン展開し、動的な葉だけ実行時ディスパッチに落とす」設計）。`libC/crc.c`/`crc.h` に対応する `make_s_coercion_from_ground`/`to_ground`/`from_mref`/`to_mref`/`from_marray`/`to_marray` 等の分解済み API を追加。

## suspend フラグの導入・`toplevel_coerce_*` → `apply_coerce_*` リネーム — `4de44a7`（2026-09-18）

`coerce` に `uint8_t suspend` 引数を追加。monotonic ref/array への coercion 適用時、`suspend=1` なら従来通り `sc_push`（`consume()` まで遅延させる suspended-cast キュー、[Phase H の Reference 実装](history/phase-h-ref-array-bench-refactor.md)を参照）に積むが、`suspend=0` なら新設のヘルパー `ref_apply_monotonic_coercion`/`array_apply_monotonic_coercion` で即座に適用する。合わせて `toplevel_coerce_*`（`capp.c`/`capp.h`、[Phase H の capp ショートサーキット最適化](history/phase-h-ref-array-bench-refactor.md)由来）を `apply_coerce_*` に改名（「トップレベルからの呼び出し」ではなく「即時適用」を表す名前へ）。

## monotonic coercion 生成のバグ修正・静的配置・最適化（09-07〜09-16）

DTI のコア（型変数の実体化と coercion 合成）に対する一連のバグ修正・最適化。

- **c41fbf6**（09-07）「optimize for alloc crc_id」: `crc_id`（恒等 coercion）割り当ての最適化
- **74b8a9f**（09-10）「optimize the CID;;CID case」: `compose` の `CId ; CId` ショートカットを簡素化
- **15a5556**（09-11, WIP）: `libC/crc.c` の coercion intern table（hash-consing 用）とcompose メモ化キャッシュを、固定サイズのグローバル配列からポインタ + 遅延 `calloc`（`ensure_intern_table`/`ensure_compose_cache`）に変更し、`set_static_crcs` で登録された静的 crc 群を intern table 構築前にも線形探索でヒットさせられるようにした。`compose` を `compose`（`crc_id` ショートカット + `PROFILE` 時の再帰深さ計測）と `compose_body`（本体）に分離
- **2291694**（09-11）「add reset_crc to set_ty」: `set_ty`（`toC.ml`）に `reset_crc` を追加
- **7d941ca**（09-14）「FIX: add returning id in the tv coercion composition case」: 型変数の coercion 合成で `crc_id` を返し忘れていたケースを修正
- **4e6668a**（09-16）「FIX id;;;id bug, id;;;tv bug」: `CId ; CId ; ...`・`CId ; ...; CTvInj` のような合成パターンでの不具合を修正（`libC/capp.c`/`crc.c`/`crc.h`/`ty.c`）
- **c00201d**（09-16）「FIX: locate tmp coercion in static region」: `static_manage.ml`/`toC.ml`/`pipeline.ml` で、一時的な coercion 変数を静的領域に正しく配置するよう修正
- **1b73f10**（09-18）「FIX: more efficient translation: choose None when the ref type is static」: `translate.ml` で、ref の型が静的に確定している場合は deref/subst の型注釈に `None` を選ぶよう変更（前述の deref/subst 高速パスが「型注釈なし＝高速パス」を判定できるようにするための下地）

## `for`/`while` をネイティブ C の `for`/`while` 文へコンパイル — `17101bc`/`6d9ea4d`（2026-09-14）

[Phase H の Array 実装](history/phase-h-ref-array-bench-refactor.md)の際に「`fun`/`let rec` への脱糖のみで新規 AST ノードなし」として追加された `for`/`while` を、`ForExp`/`WhileExp`（ITGL/CC）→ `For`/`While`（KNorm/Cls）→ `SFor`/`SWhile`（C 出力）という専用 AST ノードに置き換え、パーサレベルの脱糖（クロージャ呼び出し + 再帰）をやめてパイプライン全段で直接扱うようにした。C バックエンドは実際の `for (...)`/`while (...)` 文を出力するため、ループ本体を毎回クロージャ呼び出しする際のオーバーヘッドがなくなる。型推論（`typing.ml`）・翻訳（`translate.ml`）・k-正規化・クロージャ変換・`fv`/`ftv`/`subst`/`fresh_tv`/`normalize`・pretty-printer まで全段の対応が必要になった大きめの変更。

## ベンチマークの並列コンパイル化・`builder.ml` の分割（09-06〜09-18）

計測フェーズ（直列でないと正確な時間計測ができない）とコンパイルフェーズ（並列化してよい）を分離する目的で、`lib/backend/builder.ml`（単一 clang コマンドの組み立てと実行の両方を持っていた）を分割:

- `lib/backend/builder.ml` — `build_clang_cmd`（clang コマンド文字列の組み立て）と `unique_base`（ファイル名+モードからの一意なベース名生成）のみを残す
- `lib/backend/runner.ml`（新設） — 単一プログラムのビルド・実行（`build_run`、`bin/main.ml` の `-c` モードが使う）
- `lib/bench/bench_builder.ml`（新設） — `job list`（out_path + コマンド文字列）から Makefile を生成し `make -j<N> -k --output-sync=target` を1回呼ぶことで、複数の clang 呼び出しをまとめて並列コンパイルする機構（`.DELETE_ON_ERROR:` で失敗ジョブの生成物を自動削除するため、`Sys.file_exists job.out_path` だけで成否判定できる）。`-j` の既定値は `nproc - 1`
- `lib/bench/bench_compiler.ml`（新設、約480行） — ベンチ対象ごとの mutant 生成・C ソース生成・ジョブ列挙・（`compile_dynamize`/`compile_static`/`compile_grift` 等）を担当。実行（計測）は分離された `lib/bench/bench_runner.ml` が、コンパイルが全ターゲット完了した後で直列に行う

付随して:
- **d21a368**（09-11）: ベンチ実行にウォームアップ（`warmup = 5`）を追加し、`benchC/bench_json.c` の `update_json_file_profile` を整理
- **af65c0a**（09-18）: `crc_active`（`not config.intoB && not config.static`）を計測条件の判定に使うよう修正し、`intoB`/`static` 時に誤って crc 関連の指標を計測・出力していた不具合を修正
- **ce7a74b**（09-18）「FIX: CI」: opam キャッシュキーに `-v2` を付与（`setup-ocaml` の opam レイアウト非互換対策）、`opam update` を1回リトライ、`OPAMCONFIRMLEVEL=unsafe-yes` で非対話プロンプトを自動承認

`d055fa7`（09-18）で grift 側（`bench_grift.ml`）にも同じ並列コンパイル機構を適用。

## mutant × mode の正当性を検証するテストハーネスを追加 — `581f9d9`/`ccc68cd`（2026-09-06, 09-18）

- **ccc68cd**（09-06）「show correct result of mutation」: mutation は mutant AST を pretty-print してソースへ戻し再コンパイルする方式のため、pretty-printer のバグがそのままミュータントの意味を壊しうる。暗黙型注釈の関数（`Impl`）を明示注釈として印字していた、`let rec` の多引数カリー化関数を正しく再構成できていなかった等の `lib/utils/pp.ml` の不具合を修正（`FixExp` は直接印字せず `let rec` の一部としてのみ扱うよう変更）。`parser.mly`/`fresh_tv.ml`/`normalize.ml`/`typing.ml`/`translate.ml` も関連修正
- **581f9d9**（09-18）「add mutation tests」: `test/check_mutants.ml`（新設 exe）と `compile_test/mutation_test.sh` を追加。全 mutant × 全 mode（`--eager`/`--lazy` × `--hash`/`--no-hash` × `--guarded`/`--monotonic`、`--dynamize`/`--static`）の標準出力を、ベンチ対象ごとに人手で登録した正解値と突き合わせる end-to-end 正当性テスト。`compile_test/dotests.sh` と同じ思想だが、対象は `lib/bench/*` の mutation 機構自体（`test/test_mutate.ml` の ML 側差分カバレッジとは別に、実際にコンパイル・実行した結果まで検証する）

## grift ベンチマーク対象の制限・monotonic/guarded 切り替え・サンプル整備（09-04〜09-18）

- **2338bbc**（09-18）「add restriction for each benchmarks」/**e24dcb7**（09-18）「add restriction for grift benchmarks」: `bench_config.ml`/`bench_target.ml` に、特定のベンチ対象を特定のモード組み合わせ（未対応の評価戦略や grift 側で計測不能なケースなど）から除外する仕組みを追加
- **4a19f0f**（09-18）「add switch for monotonic / guarded to bench」: `bin/bench.ml` に `--guarded`/`--monotonic` フラグを追加し、ベンチマークの reference/array 意味論を固定できるように（`test/check_mutants.ml` にも同名フラグがある）
- ベンチマークサンプルの追加・修正: **c179807**（array/matmult/quicksort/tak の grift 側サンプルと church_mono/church_poly 入力を追加）、**8d91774**（grift の array/quicksort サンプル修正）、**20c84c0**（ベンチマークが複数プログラムの列を扱えるように、`pipeline.ml`/`pipeline.mli` 変更）、**eb84c11**（09-10、quicksort 等の入力データを大幅拡大）、**2243675**（array 入力の変更）、**0a59fe3**/**46f2dac**（church-2/church-4 サンプルの追加・修正）

## 型変数(tvs)最適化・`fresh_tv` タイミングの変更 — `84bb60f`/`448d270`（2026-09-03, 09-04）

`bin/main.ml` に `--tvs_opt_off` フラグ（既定で最適化 on）を追加し、`Config.t` に `tvs_opt` フィールドを新設。`lib/backend/closure.ml`/`kNormal.ml`/`lib/utils/var/ftv.ml` に、クロージャが実際に使わない型変数を除去する最適化を追加。合わせて `fresh_tv.ml`（156行の書き換え）で型変数のリフレッシュ（一意な名前への付け替え）を行うタイミングをパイプライン内で見直し、進捗表示（`Bench_progress`）も正しいタイミングで出るよう修正。

## bench を `lib/bench/` + `bin/bench.ml` へ移行、grift 計測を Python から OCaml へ移植 — `f9ff6ee`（2026-09-04）

トップレベルの `bench/` ディレクトリ（OCaml ライブラリ）を廃止し、`lib/bench/`（ライブラリ）+ `bin/bench.ml`（薄い CLI エントリ、`bin/main.ml` と同じ `bin/` 配下）へ統合。合わせて `benchC/run_grift.py`（Python、429行、grift ベンチマークの mutate・実行・計測を担っていたスクリプト）を削除し、同等の機能を `lib/bench/bench_grift.ml`（OCaml、359行）として全面移植。`mutate.ml` も `lib/bench/` に移動。`lib/pipeline.mli` を新設し `pipeline.ml` の公開インターフェースを明示化。`test/test_interpreter.ml` もこの移動に追従。

（09-04 の同日に `.gitignore` へ `__pycache__`/`*.pyc` を追加した2commit があるのも、この Python スクリプト削除の後始末）

## CLAUDE.md と docs/ を追加 — `a9c8901`（2026-09-18）

このファイルを含む `CLAUDE.md`/`docs/howto.md`/`docs/todo.md`/`docs/history.md`/`docs/history/phase-{a..g}-*.md` が最初に追加された commit。それ以前のこのドキュメント群には版がない。

---

## プレヒストリ（Phase H 以前）

上記より前のすべての作業（2024-11-11〜2026-09-02、著者 `yukioshima11124457@gmail.com` による commit）は、量が多いため作業内容ごとに別ファイルへ分割している。**新しいフェーズから順に**並べる（＝一番下が最初期）。

1. [Phase H — Reference/Array実装・utils再構成・bench基盤の整理](history/phase-h-ref-array-bench-refactor.md)（2026-05-27〜2026-09-02）
2. [Phase G — 論文実験・pipeline統合・タプル対応](history/phase-g-pipeline-tuple.md)（2026-04-01〜2026-05-21）
3. [Phase F — grift比較ベンチマーク・静的最適化](history/phase-f-grift-optimization.md)（2026-02-03〜2026-03-16、最大のフェーズ）
4. [Phase E — lambda-S-dtiへの命名統一・CI整備・fully-staticコンパイラ](history/phase-e-rename-ci.md)（2026-01-02〜2026-01-23）
5. [Phase D — Cバックエンド立ち上げ・ベンチマーク基盤](history/phase-d-cbackend-bootstrap.md)（2025-09-27〜2025-12-31）
6. [Phase C — K正規化体系の修正](history/phase-c-knormal-fix.md)（2025-05-07〜2025-06-26）
7. [Phase B — GC導入・多相対応・lambdaS1DTIインタプリタ完成](history/phase-b-gc-polymorphism.md)（2025-01-06〜2025-04-28）
8. [Phase A — 最初期: K正規化・クロージャ変換の基礎実装](history/phase-a-foundation.md)（2024-11-11〜2024-12-07、最も古いフェーズ）
