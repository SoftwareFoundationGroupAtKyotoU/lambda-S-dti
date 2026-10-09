# howto — ビルド・実行・テスト

[CLAUDE.md](../CLAUDE.md) から参照される用途別ドキュメントの一つ。「どう動かすか」はここに集約する。
実装の変遷は [history.md](history.md)、未完了タスクは [todo.md](todo.md) を参照。

---

## ビルド

```bash
eval $(opam env)
dune build
dune install          # lSdti を opam prefix にインストール（compile_test で必要）
```

必要な外部依存（`README.md` にも詳細あり）:
- Boehm GC (`libgc-dev` / `bdw-gc`) — C バックエンドの GC
- cJSON (`libcjson-dev` / `cjson`) — ベンチマークの C 側計測ドライバ（`benchC/bench_json.c`）が
  JSONL に計測値を書き戻すのに使う（OCaml 側は `yojson`）

## 実行

```bash
lSdti file.ldti              # インタプリタモード（REPL 代わり）
lSdti file.ldti -c           # コンパイルモード（→ C → clang → 実行）
./_build/default/bin/main.exe --help   # dune install していない場合
```

### CLI オプション（`bin/main.ml` / `lib/config.ml`）

| オプション | 意味 |
|---|---|
| `-d` | debug モード（各種メッセージを stderr に出力） |
| `-c` | C コードへコンパイルして実行 |
| `-a` | 代替翻訳（alt translation）を使う |
| `-b` | LB（`intoB`）へ翻訳。`-a` や `--monotonic` と同時指定不可 |
| `-e` | list の coercion/cast 合成を eager に行う |
| `--non_monotonic` | monotonic reference/array を off にする（デフォルトは monotonic） |
| `--tvs_opt_off` | クロージャが使わない型変数を除去する最適化を off にする（デフォルトは on。`-c` 時のみ効く） |
| `-h` | hash-consing / compose のメモ化を有効化（`-c` 専用） |
| `--static` | 完全に静的な（`?` を含まない）プログラムのみを評価/コンパイル。指定時は内部的に `alt=false, intoB=true, eager=true, monotonic=false, hash=false` に固定される |
| `-O0`/`-O1`/`-O2`/`-O3`/`-Os`/`-Oz`/`-Ofast` | 生成 C コードの clang 最適化レベル（`-c` 専用、既定 `-O3`） |

`-a` と `-b` は同時指定不可。`--monotonic`（デフォルト）と `-b` も同時指定不可。インタプリタモード（`-c` なし）では `--static`/`-h` は未実装。

これらの組み合わせ（`eager` × `monotonic` × `intoB` など）はインタプリタの評価戦略を切り替えるフラグで、`test/test_interpreter.ml` で網羅テスト中（[todo.md](todo.md) 参照）。

## テスト

```bash
dune runtest                       # OUnit2 ユニットテスト（test/ 以下）
bash compile_test/dotests.sh       # コンパイルテスト一括実行（`-c`/`-c -a`/`-c -b --non_monotonic`/`-c --static` 全パターン）
bash compile_test/mutation_test.sh # 全 mutant × ベンチと同じアブレーションターゲット（untypedALHMT 基準 + 各軸を1つずつ反転、× dynamize/static）の
                                    # 標準出力が正解値と一致するかの end-to-end 検証（test/check_mutants.exe 経由）
```

`test/test_mutate.ml`（ML 側の mutation 機構自体のユニットテスト・スロット付番の一致確認）とは別に、`compile_test/mutation_test.sh` は実際に mutant をコンパイル・実行した結果まで検証する（[history.md](history.md) 参照）。

### compile_test の構造

```
compile_test/
├── dotests.sh          ← テストランナー（TEST_DIR を設定して tests.sh を source）
├── minCaml/            ← min-caml 由来の静的プログラム
├── paper/               ← LDTI 論文例
├── issues/              ← issue ごとの回帰テスト
└── original/
    ├── bool/    dynamic/   int/    list/   match/   ref/   tuple/  array/
```

各サブディレクトリの `tests.sh` に

```bash
run_test "file.ml" "expected"
```

を1行追加すると新しいテストケースが登録される。第3引数に `skip_static` を渡すと `--static` モードをスキップできる（`?` を含み静的評価できないプログラム用。例: `compile_test/original/array/dynamic.ml`）。

## ベンチマーク

lattice / mutation ベンチマーク。未型付けのサンプルを取り、`Mutate.mutate_all` で
「ユーザー型注釈のあらゆる部分集合を `?` に置換した mutant 群」に展開し、mode ×
評価戦略の各組み合わせで C にコンパイルして実行時間などを計測する。**コンパイル専用**。

ベンチは次のフェーズを順に実行する。各フェーズは全対象を最後まで処理してエラーを集め、1件でもあれば **そのフェーズの終わりで全エラーを表示して終了（exit 1）** し、次のフェーズには進まない（`Bench_phases.run`）。restriction による意図的な除外は `[Skip]` の info のみでエラーにしない。

| # | フェーズ | 落ちる条件 |
|---|---|---|
| 1 | restriction の解決 | 未知のターゲット名（`Bench_config.targets` / `extra_targets` に無い） |
| 2 | ソースの存在 | untyped（常に）/ typed（`--typed` 時）/ grift（`--grift` かつ restriction の `grift = true` 時）が無い |
| 3 | input の存在 | `samples/input/<name>.txt`（dynamize・grift）/ `<name>_fs.txt`（static）が無い |
| 4 | parse | untyped/typed の parse、grift の S 式解析（ML の let rec に対応する define が無い等） |
| 5 | スロット対応 | untyped↔typed のスロットが対応しない（`mono_copies` 参照）、`mono_copies` の名前がソースに無い、grift のスロット数が untyped と異なる |
| 6 | mutate | mutant の型推論失敗 |
| 7 | コード生成 | mutant の translate→kNorm→closure→toC 失敗、grift ソース生成失敗 |
| 8 | コンパイル | clang / grift のコンパイル失敗（全ターゲットを `make -j<N>` でまとめて並列コンパイル） |
| 9 | 計測 | （直列実行。ここでの失敗は従来どおり `[Skip]`） |

ログディレクトリはフェーズ 7 の直前に作るので、1〜6 で落ちた場合は何も書かれない。
`test/check_mutants.exe` もフェーズ 1〜6 を共有する（`Bench_phases.prepare_all`）。

typed ソースで多相関数を単相版に複製している対象（church-4 の `two` → `two0`/`two1` 等）は、`Bench_config` の `mono_copies` に `(untyped 側の名前, typed 側の複製名たち)` を書く。スロットは「囲む let 束縛名の経路（複製名は元の名前に読み替え）+ 経路内での出現序数」で対応付けられ（`Mutate.correspond`）、untyped のスロット i を Dyn 化する mutant では、対応する typed スロットを全て Dyn 化する。mutant 数と `mutant_index` の意味は untyped / typed / grift で常に一致する。

### モジュール構成（`lib/bench/` + `lib/backend/runner.ml`）

`bin/bench.ml` は薄い CLI エントリ（`bin/main.ml` と同じ `bin/` 配下）。実体は `lambda_S_dti` ライブラリ内の `lib/bench/`:

| モジュール | 役割 |
|---|---|
| `bench_config` | ベンチ対象の表（`targets`: 名前・スイート・restriction・`mono_copies`、既定外の `extra_targets`）・既定反復回数・`sample_path`/`input_path` |
| `mutate` | スロット列挙・mutant 生成（`analyze` / `mutate_term_with_indices` / `subsets_auto`）・untyped↔typed のスロット対応（`correspond`） |
| `bench_target` | `mode` 型・軸別アブレーション・restriction の解決（`plan_of_spec`）・ターゲット展開（`expand_ablation_targets`）・出力ラベル（`ablation_mode_str`） |
| `bench_phases` | 前処理フェーズ 1〜6（restriction 解決〜mutate）とフェーズ実行（`run`）。`prepare_all` で 1〜6 をまとめて実行 |
| `bench_builder` | `job list`（out_path + clang コマンド）から Makefile を生成し `make -j<N> -k --output-sync=target` で並列コンパイル。`-j` 既定値は `nproc - 1` |
| `bench_compiler` | コード生成（`prepare_batch` / `prepare_grift_batch`）と並列コンパイル（`compile_batch` / `compile_grift_batch`）。mutant ごとの C 生成（`compile_mutants`）はエラーを握りつぶさず返す |
| `bench_runner` | コンパイル済みターゲットの直列実行・計測（`run_batch` / `run_grift_batch`） |
| `bench_grift` | grift 側 lattice ベンチ（`.grift` を S 式として mutate → `grift` で compile/run）。旧 `benchC/run_grift.py`（Python）の OCaml 移植 |
| `bench_output` | mutant 1件の JSON 構築と jsonl/json 書き込み |
| `bench_progress` | 進捗バー |
| `bench_json` | 極小 JSON ビルダ |

単一プログラムのビルド・実行（`-c` モード、並列化不要）は `lib/backend/runner.ml`（`Runner.build_run`）が担う。`lib/backend/builder.ml` はどちらからも使われる「clang コマンド文字列を組み立てるだけ」の共通部分（`build_clang_cmd` / `unique_base`）。

### 入出力

- ソース: `samples/src_gradti/{typed,untyped}/{original,grift_benchmark,GTP_benchmark}/<name>.ml`。
  既定は `untyped`、`--typed` を付けると `typed` 側を読む（同名ターゲットでも
  スイート・バリアントによって中身が同一とは限らない点に注意）。
  対象がどのスイートに属するかは `Bench_config.targets` の各エントリで明示する。
  必要なソースファイルが存在しないターゲットがあれば、フェーズ 2 で全体が停止する。
  `GTP_benchmark` は型注釈スロット数 n が既存対象（最大でも十数個）より桁違いに
  多くなりうるため（`fsm` で 65）、他スイートのような全部分集合 (2^n 通り) の
  列挙ではなく `Mutate.sample_subsets_by_length`（fully-typed / fully-dynamic の
  両端 + 残り `gtp_samples_per_slot * n - 2` 個をランダム抽出、合計ちょうど
  `gtp_samples_per_slot * n` 件）を使う。以前あった `fsm --dynamize` の
  コード生成時 `Not_found` は解消済み（2026-09-27 確認: 全アブレーション軸 ×
  650 mutant でコード生成・コンパイルが通り、untypedALHMT では全 mutant の標準出力が一致）。
  fsm は 1 mutant あたり 2 行出力するため `test/check_mutants.exe`（1 mutant 1 行前提）では検査できない。
- driver 入力: `samples/input/<name>.txt`（`--static` は `<name>_fs.txt`。どのベンチも両者は同じ値）。
  grift_benchmark の入力は、Grift 論文の部分型付け実験（[Gradual-Typing/benchmarks](https://github.com/Gradual-Typing/benchmarks)
  の `scripts/grift_partial.sh`）と同じものを `inputs/` から取っている:
  fft = `medium1`（65536）、blacksholes = `blackscholes/in_4K`（1 行 1 項目に変換）、
  ray = `fast`（1）、array = `fast`（500 100000）、quicksort = `in_descend1000`。
  例外は n_body（20000。Grift の `fast` = 2000 は短すぎ、`slow` = 100000 は長すぎる）と
  tak（22 16 8。Grift の `slow` = 40 20 11 は 1 回 20 秒を超える）。
- ML 側は 1 プロセスで全 mutant を順に計測し、grift 側は mutant ごとに別プロセスで
  計測する（grift 側は driver を差し込めないため）。
- どちらも計測前に計測しない実行を `Bench_config.warmup`（5）回行う。grift 側は
  `(benchmark)` を warmup 回呼んでから `(time (benchmark))` を `-i` 回呼ぶ（入力はその分繰り返す）。
  warmup がないと grift の 1 回目は約 1.8 倍遅く、5 回目まで下がり続けていた。
  cast-profiler 用のバイナリはプロセス全体で数えるので warmup せず 1 回だけ実行する。
- grift 比較用ソース: `samples/src_grift/{original,grift_benchmark}/<name>.grift`。
  `--grift` は `grift`（racket 実装、`GRIFT` 環境変数でパス上書き可）を要する。
  `GTP_benchmark` には対応する `.grift` が無いため `--grift` では自動的にスキップされる。
- 出力: `logs/<YYYYMMDD-HH:MM:SS>/<MODE>_<name>.jsonl`（NDJSON、1行=1 mutant）。
  ほかに `logs/<ts>/<MODE>/<name>_<n>.c`（mutant ごとの生成 C）、
  `logs/<ts>/bench/`（計測ドライバと `.out`）、
  `--grift` 時は `GRIFT_<name>.jsonl` / `GRIFTC_<name>.jsonl` と `logs/<ts>/GRIFT/`。
- `<MODE>` は `<S|A|STATIC><E|L><H|N>`（例 `SLH` = S・lazy・no-hash、
  `STATICEN` = STATIC・eager・no-hash）。grift 側は `GRIFT`（racket バックエンド）/
  `GRIFTC`（C バックエンド）。
- ML 側 mutant と grift 側 mutant は **同じ `mutant_index`（スロットの出現順で
  番号付け）** で対応する。
- JSONL の各行のフィールド:
  `mode, mutant_index, after_mutate, times_sec, mem, cast, inference, longest`。
  `times_sec` / `mem` / `cast` / `inference` / `longest` は C 側の計測・profile
  ドライバ（`Bench_compiler.generate_bench_sources`、`benchC/bench_json.c`）が後から書き戻す。

### 実行（Docker）

**本番の計測は Docker で行う**。`grift` はイメージ内にしか入っておらず、
clang 18 / libgc などの環境もイメージで固定されているため。

```bash
make docker-bench ARGS="--dynamize --static fib tak -i 100"
make docker-bench ARGS="--all --id_opt --eagerness --hash --monotonic --tvs_opt --typed"
make plot                                        # scripts/plot_all.py で可視化（ホスト側）
```

- `make plot` などのスクリプトは、`logs/` 以下のタイムスタンプ名のディレクトリのうち最新のものを使う。
  名前を付け直したディレクトリ（例: `logs/array-quicksort-tak-church-loop`）は
  `BENCH_LOG_DIR=<名前> make plot` のように指定する。
- 何を描くかは `scripts/benchviz.py` の2つの表で決まる。
  - `TARGET_PAIRS`（mutant の計測ログ）: 各 `(base, comps)` について、comps 全部をまとめた図と comp 1つずつの図を、
    relative・scattered・metrics（cast/inference/mem/longest）・cumulative の4種類すべてで出す。
    今は `untypedALHMT` 基準で `untypedSLHMT`/`untypedALhMT`/`untypedALHMt`、`typedALHMT` 基準で `untypedALHMT`/`GRIFTCM`。
    比較対象のどれにもログが無いベンチ（Grift の無い fsm・church など）は描かない
  - `STATIC_SUMMARY_GROUPS`（静的実行 `*_fs` のログ）: `static_summary/` に、同じくまとめた図と1つずつの図を出す。
    `TARGET_PAIRS` と同じ組み合わせに加えて、`untypedSTATICEhGT` 基準で `untypedALHMT`/`typedALHMT`、同じ基準で `typedALHMT`/`GRIFTCM`/`GRIFTCMS`
- 累積性能グラフの overhead は「その mutant の平均実行時間 ÷ 基準モードの最も静的な mutant（mutant 1）の平均実行時間」。
  `cumulative/summary.md` の表は、まとめた組み合わせごとに出す

- `make docker-bench` は先に `make docker-build`（`docker build -t env .`）を実行する。
  イメージはビルド時点の作業ツリーを `COPY` して `dune build` するので、ソースを変えたら
  イメージを作り直さないと古いコードで計測してしまう。変更が無ければレイヤキャッシュで
  すぐ終わる。イメージ名は `DOCKER_IMAGE=...` で変えられる（既定 `env`）。
- 実体は次のコマンド。`logs/` だけを bind mount し、`HOST_UID`/`HOST_GID` を渡すことで、
  コンテナが書いた `logs/<ts>/` を実行後に呼び出し元ユーザーの所有に戻す（entrypoint.sh）。

  ```bash
  docker run --rm -e HOST_UID=$(id -u) -e HOST_GID=$(id -g) \
    -v $(pwd)/logs:/app/logs env bench <bench.exe の引数>
  ```

- 長時間の計測は `tmux` / `nohup` 上で走らせ、同じマシンで他の重い処理を同時に走らせないこと
  （フェーズ 9 は直列計測なので、他のプロセスの負荷がそのまま計測値に乗る）。
- 計測は `--cpu N` で1コアに固定すること。コアごとに動作周波数が異なり（同じマシンで
  2.0GHz のコアと 3.9GHz のコアがある）、固定しないと同じバイナリでもプロセスごとに
  実行時間が約 2 倍ばらつく。割り込みを受ける cpu0 は避け、`lscpu` で SMT の相方
  （例: cpu72 と cpu200）にも他の負荷が無いコアを選ぶ。Docker では `--cpuset-cpus` の範囲内の番号のみ使える。
- ホストで直接 `dune exec ./bin/bench.exe -- ...`（`make benchmark` も同じ）を実行してもよいが、
  `--grift` は使えない。フェーズ 1〜8 の確認（コード生成・コンパイルが通るか）など、
  計測値を使わない用途に限る。

### オプション

**注意**: `--dynamize` / `--static` / `--grift` / `--all` のいずれも指定しないと何も
実行されない。

| オプション | 意味 |
|---|---|
| `--dynamize` | mutant 群をベンチ |
| `--static` | 完全静的版（`<name>_fs`、fully-typed mutant 1 件のみ）をベンチ。STATIC モードの基準がファイルごとに1つ加わる |
| `--grift` | grift の C/LLVM バックエンドとの比較（基準 ALHMT の monotonic 側のみ、要 `grift`） |
| `--all` | `--dynamize --static --grift` |
| `--id_opt` | 軸: mode A ↔ S（id 特殊化） |
| `--eagerness` | 軸: lazy ↔ eager |
| `--hash` | 軸: hash-consing on ↔ off |
| `--monotonic` | 軸: monotonic ↔ guarded（reference/array） |
| `--tvs_opt` | 軸: tvs_opt on ↔ off |
| `--typed` | 軸: untyped/ ↔ typed/ ソース |
| `-i N` | 反復回数（既定 `Bench_config.default_itr` = 500） |
| `--jobs N` | 並列コンパイルの最大ジョブ数（既定 `nproc - 1`） |
| `--cpu N` | フェーズ 9（計測）の実行を `taskset -c N` で CPU N に固定する（コンパイルは並列のまま）。既定は固定しない |
| `--out json\|jsonl` | 出力形式（既定 `jsonl`） |
| `--list` | ベンチ対象名を表示して終了 |
| 位置引数 | ベンチ対象名（無指定で `Bench_config.all_targets`） |

軸フラグは「基準 `untypedALHMT`（mode A・lazy・hash・monotonic・tvs_opt・untyped）から
その軸だけを1つ反転したターゲット」を追加する。複数指定しても軸間の直積は取らず、
基準はファイルごとに1回だけ計測される。**軸フラグを1つも付けないと基準 ALHMT だけを計測する**
（全軸がほしければ6つとも付ける。`test/check_mutants.exe` は省略時に全軸なので挙動が異なる）。
restriction で除外された軸は `[Skip]` と表示して飛ばす。

### 所要時間

フェーズ 9 の計測時間は概ね「Σ（ターゲット × mutant 数 × (`-i` + warmup) × 1回の実行時間）」。
いちばん重いのは fsm で、1 回の実行が 1 mutant あたり約 1.2 秒かかる（650 mutant を
1 回ずつ流して約 13 分、ホストで測定）。したがって `-i 500` だと 1 ターゲット（1構成）だけで
100 時間を超える。全体を回す前に次のようにして見積もるとよい。

```bash
# フェーズ 1〜8 だけ確認（コンパイルまで通るか）。Phase 9 に入ったら Ctrl-C でよい
dune exec ./bin/bench.exe -- --dynamize --static <軸フラグ...> -i 1
# -i を小さくして対象ごとに流し、所要時間から -i 500 の場合を見積もる
make docker-bench ARGS="--dynamize tak -i 5"
```

---

## 言語構文

構文一覧は [README.md](../README.md) の Syntax セクションを参照。