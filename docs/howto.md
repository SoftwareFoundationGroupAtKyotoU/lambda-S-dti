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
bash compile_test/mutation_test.sh # mutant × mode（eager/lazy × hash/no-hash × guarded/monotonic × dynamize/static）の
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

コンパイル（並列化してよい）と計測（直列でないと正確な時間が取れない）を明確に分けたパイプラインになっている: 全ターゲットを先にまとめて並列コンパイルし（`make -j<N>` を1回呼ぶ）、1つでも失敗したらベンチ実行を一切行わず中断、全て成功していれば計測フェーズへ進む。

### モジュール構成（`lib/bench/` + `lib/backend/runner.ml`）

`bin/bench.ml` は薄い CLI エントリ（`bin/main.ml` と同じ `bin/` 配下）。実体は `lambda_S_dti` ライブラリ内の `lib/bench/`:

| モジュール | 役割 |
|---|---|
| `bench_config` | ベンチ対象リスト・既定反復回数・`sample_path`/`input_path` |
| `mutate` | mutant 生成（`analyze` / `mutate_all`） |
| `bench_target` | `mode` 型・`full_mode_name`・`parse_and_mutate`・ターゲット展開・対象ごとの制限（未対応モード除外） |
| `bench_builder` | `job list`（out_path + clang コマンド）から Makefile を生成し `make -j<N> -k --output-sync=target` で並列コンパイル。`-j` 既定値は `nproc - 1` |
| `bench_compiler` | 対象ごとの mutant 生成・C ソース生成・並列コンパイルジョブの列挙・オーケストレーション（`compile_dynamize` / `compile_static` / `compile_dynamize_grift` / `compile_static_grift`） |
| `bench_runner` | コンパイル済みターゲットの直列実行・計測（`run_batch` / `run_grift_batch`） |
| `bench_grift` | grift 側 lattice ベンチ（`.grift` を S 式として mutate → `grift` で compile/run）。旧 `benchC/run_grift.py`（Python）の OCaml 移植 |
| `bench_output` | mutant 1件の JSON 構築と jsonl/json 書き込み |
| `bench_progress` | 進捗バー |
| `bench_json` | 極小 JSON ビルダ |

単一プログラムのビルド・実行（`-c` モード、並列化不要）は `lib/backend/runner.ml`（`Runner.build_run`）が担う。`lib/backend/builder.ml` はどちらからも使われる「clang コマンド文字列を組み立てるだけ」の共通部分（`build_clang_cmd` / `unique_base`）。

### 入出力

- ソース: `samples/src_gradti/untyped/{original,grift_benchmark}/<name>.ml`。
- driver 入力: `samples/input/<name>.txt`（`--static` は `<name>_fs.txt`）。
- grift 比較用ソース: `samples/src_grift/{original,grift_benchmark}/<name>.grift`。
  `--grift` は `grift`（racket 実装、`GRIFT` 環境変数でパス上書き可）を要する。
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

### 実行

```bash
dune exec ./bin/bench.exe -- --all -i 500        # 既定対象を全モードで
dune exec ./bin/bench.exe -- --dynamize fib tak  # 対象を指定して dynamize のみ
make benchmark                                   # = dune exec ./bin/bench.exe（引数なし）
make plot                                        # scripts/plot_all.py で可視化
```

**注意**: `--dynamize` / `--static` / `--grift` / `--all` のいずれも指定しないと何も
実行されない（`make benchmark` に引数を渡すか `--all` を付ける）。

| オプション | 意味 |
|---|---|
| `--dynamize` | mutant 群をベンチ（STATIC mode は除外） |
| `--static` | 完全静的版（`<name>_fs`、先頭 mutant のみ）をベンチ |
| `--grift` | grift 比較を実行（`bench_grift`、要 `grift` バイナリ） |
| `--all` | `--dynamize --static --grift` |
| `-i N` | 反復回数（既定 `Bench_config.default_itr` = 500） |
| `--jobs N` | 並列コンパイルの最大ジョブ数（既定 `nproc - 1`） |
| `--eager` / `--lazy` | 評価戦略を固定（無指定で両方） |
| `--hash` / `--no-hash` | hash-consing を固定（無指定で両方） |
| `--guarded` / `--monotonic` | reference/array の意味論を固定（無指定で両方） |
| `--out json\|jsonl` | 出力形式（既定 `jsonl`） |
| `--list` | ベンチ対象名を表示して終了 |
| 位置引数 | ベンチ対象名（無指定で `Bench_config.all_targets`） |

---

## 言語構文

構文一覧は [README.md](../README.md) の Syntax セクションを参照。