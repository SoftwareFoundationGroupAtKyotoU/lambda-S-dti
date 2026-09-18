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
| `-h` | hash-consing / compose のメモ化を有効化（`-c` 専用） |
| `--static` | 完全に静的な（`?` を含まない）プログラムのみを評価/コンパイル。指定時は内部的に `alt=false, intoB=true, eager=true, monotonic=false, hash=false` に固定される |

`-a` と `-b` は同時指定不可。`--monotonic`（デフォルト）と `-b` も同時指定不可。インタプリタモード（`-c` なし）では `--static`/`-h` は未実装。

これらの組み合わせ（`eager` × `monotonic` × `intoB` など）はインタプリタの評価戦略を切り替えるフラグで、`test/test_interpreter.ml` で網羅テスト中（[todo.md](todo.md) 参照）。

## テスト

```bash
dune runtest                  # OUnit2 ユニットテスト（test/ 以下）
bash compile_test/dotests.sh  # コンパイルテスト一括実行（`-c`/`-c -a`/`-c -b --non_monotonic`/`-c --static` 全パターン）
```

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

### モジュール構成（`bench/`）

`bench.ml` は薄い CLI エントリ。実体は `bench_lib` ライブラリ:

| モジュール | 役割 |
|---|---|
| `bench_config` | ベンチ対象リスト・既定反復回数・`sample_path`/`input_path` |
| `mutate` | mutant 生成（`analyze` / `mutate_all`） |
| `bench_target` | `mode` 型・`full_mode_name`・`parse_and_mutate`・ターゲット展開 |
| `bench_runner` | 1ターゲットの実行、`run_dynamize` / `run_static` / `run_grift` |
| `bench_grift` | grift 側 lattice ベンチ（`.grift` を S 式として mutate → `grift` で compile/run）。旧 `benchC/run_grift.py` の OCaml 移植 |
| `bench_output` | mutant 1件の JSON 構築と jsonl/json 書き込み |
| `bench_progress` | 進捗バー |
| `bench_json` | 極小 JSON ビルダ |

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
  ドライバ（`Builder.build_run_bench`、`benchC/bench_json.c`）が後から書き戻す。

### 実行

```bash
dune exec ./bench/bench.exe -- --all -i 500        # 既定対象を全モードで
dune exec ./bench/bench.exe -- --dynamize fib tak  # 対象を指定して dynamize のみ
make benchmark                                     # = dune exec ./bench/bench.exe（引数なし）
make plot                                          # scripts/plot_all.py で可視化
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
| `--eager` / `--lazy` | 評価戦略を固定（無指定で両方） |
| `--hash` / `--no-hash` | hash-consing を固定（無指定で両方） |
| `--out json\|jsonl` | 出力形式（既定 `jsonl`） |
| `--list` | ベンチ対象名を表示して終了 |
| 位置引数 | ベンチ対象名（無指定で `Bench_config.all_targets`） |

---

## 言語構文

構文一覧は [README.md](../README.md) の Syntax セクションを参照。