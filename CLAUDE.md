# lambda-S-dti — CLAUDE.md

gradual typing + Hindley-Milner 型推論コンパイラ（ITGL → CC → k-正規化 → クロージャ変換 → C）の実装リポジトリ。
Space-efficient coercion による動的型推論（DTI）を特徴とする。

このファイルはアーキテクチャと現状の要約のみを扱う。用途別の詳細は以下を参照:

- **[docs/howto.md](docs/howto.md)** — ビルド・実行・テストの手順、CLI オプション
- **[docs/history.md](docs/history.md)** — これまでの実装の変遷
- **[docs/todo.md](docs/todo.md)** — 現在の残作業
- [README.md](README.md) — 言語仕様の基本構文リファレンス（外部向け）
- [memo.md](memo.md) — 著者のベンチマーク分析用の生の研究ノート

---

## アーキテクチャ概観

```
ソースプログラム (.ldti) (.ml)
    │
    ▼
[フロントエンド]  lib/frontend/lexer.mll, parser.mly
    │ ITGL AST (Syntax.ITGL.exp)
    ▼
[型推論]          lib/typing/typing.ml  (ITGL モジュール)
    │ 型注釈付き ITGL AST
    ▼
[キャスト挿入翻訳] lib/backend/translate.ml  (ITGL → CC)
    │ CC AST (Syntax.CC.exp)
    ├─▶ [インタプリタ]   lib/interpreter/eval.ml
    │
    ▼
[k-正規化]        lib/backend/kNormal.ml   (CC → KNorm)
    ▼
[クロージャ変換]   lib/backend/closure.ml  (KNorm → Cls)
    ▼
[C コード生成]    lib/backend/toC.ml      (Cls → C)
    ▼
[C コンパイル]    lib/backend/runner.ml   (clang 呼び出し。コマンド組み立ては builder.ml)
```

パイプライン全体は `lib/pipeline.ml` が統括。REPL / ファイル実行は `bin/main.ml`。

---

## 言語仕様のポイント

- **ITGL** (Implicitly-Typed Gradual Language): HM 型推論 + 型の一致性制約 (`~`) による Gradual Typing
- **CC** (Blame Calculus with DTI): Coercion を明示的に持つ中間言語。
- **Coercion**: `CId`, `CSeq`, `CInj`, `CProj`, `CFun`, `CList`, `CTuple`, `CRef of coercion * coercion`, `CMRef of ty * ty`, `CArray of coercion * coercion`, `CMArray of ty * ty`, `CTvInj`, `CTvProj`, `CTvProjInj`, `CFail`
  - 型変数は `CTvInj` / `CTvProj` / `CTvProjInj` として実体化
  - `CRef (c_r, c_w)` : `(u1 ref → u2 ref)` — `c_r : u2→u1`（読み出し逆変換）, `c_w : u1→u2`（書き込み変換）
  - `CMRef (u1, u2)` : monotonic モード（`config.monotonic = true`）で使用。型変数の一方向インスタンス化のみ許す
  - `CArray`/`CMArray` は `CRef`/`CMRef` と対称な設計（配列版）
- **Tag**: `I | B | U | Fn | Li | Tp n | Rf | Ar` — ground type 識別子
- **DTI (Dynamic Type Inference)**: `compose` 関数内で `CTvInj ; CProj(tag)` が出会った時に型変数を具体化する
- **Space-efficient**: Coercion の合成 (`compose`) により冗長な cast を削減
- **for/while**: 他の多くの構文糖（match の一部等）と異なり `fun`/`let rec` への脱糖ではなく、`ForExp`/`WhileExp`（ITGL/CC）→ `For`/`While`（KNorm/Cls）という専用 AST ノードを持ち、C バックエンドはネイティブの `for`/`while` 文（`SFor`/`SWhile`）を直接出力する

---

## AST 定義 (`lib/syntax.ml`)

```
Syntax.ITGL.exp  — 表面言語 AST
Syntax.CC.exp    — CC 中間言語 AST（coercion 明示）
Syntax.CC.value  — インタプリタの値
Syntax.KNorm.exp — k-正規化後 AST
Syntax.Cls.exp   — クロージャ変換後 AST
```

型関連:
- `ty` : TyDyn | TyVar | TyInt | TyBool | TyUnit | TyFun | TyList | TyTuple | TyRef | TyArray
- `tysc` : TyScheme (tyvar list * ty) — let 多相スキーム
- `coercion` : 上記参照
- `CC.value` : `RefV of (value * ty) ref`、`ArrayV of (value array * ty) ref` — 現在の型を自分で保持するセル/配列。lazy な値ラッパーが2系統ある:
  - `CoerceV of value * coercion` — coercion 経由（`CAppExp`/`coerce`）の遅延キャスト。`CFun`/`CList`/`CTuple`/`CRef`/`CArray` を deep coercion として1つの `CoerceV` にまとめ、`coerce` 自身が `compose` で多重ラップを畳み込む
  - `CastFunV`/`CastListV`/`CastTupleV`/`CastRefV`/`CastArrayV`（各 `value * (分解済みの型) * ... * (range * polarity)`）— 直接キャスト（`-b`/`CastExp`/`cast`）経由の遅延キャスト。`coercion` を経由しない分、多重ラップ `CastXxxV<CastXxxV<...>>` はそのまま許容し、`match_mf`/`eval_app_valM`/`DerefExp`/`SubstExp` などの消去位置で「destructure するたびに1層ずつ剥がす」再帰的 force で解決する

---

## 主要ファイルと役割

| ファイル | 役割 |
|---|---|
| `lib/syntax.ml` | 全 AST 定義・共有型（ty, coercion, tag 等） |
| `lib/config.ml` | 実行時フラグ（`eager`/`monotonic`/`alt`/`intoB`/`static`/`hash` 等）の定義と妥当性検査 |
| `lib/typing/typing.ml` | ITGL 型推論（unify）+ CC 型検査 |
| `lib/backend/translate.ml` | キャスト挿入翻訳（ITGL → CC）+ `make_s_coercion` |
| `lib/interpreter/eval.ml` | CC インタプリタ本体（`compose`/coercion 演算は `lib/utils/coercion.ml` に分離） |
| `lib/utils/coercion.ml` | `compose`・`normalize_coercion`・`is_d` など coercion 演算 |
| `lib/utils/unify.ml`, `type_utils.ml` | 型の unify・meet などの補助演算 |
| `lib/utils/modify/`（`fresh_tv.ml`/`normalize.ml`/`subst.ml`） | AST を書き換える系の関数群（型変数リフレッシュ・正規化・代入） |
| `lib/utils/var/`（`fv.ml`/`ftv.ml`/`tv.ml`） | 自由変数・自由型変数・型変数の収集 |
| `lib/utils/pp.ml` | 全 AST の pretty-printer |
| `lib/utils/resources.ml` | project root / libC / result_C / result の絶対パス解決 |
| `lib/backend/kNormal.ml` | k-正規化（CC → KNorm）|
| `lib/backend/closure.ml` | クロージャ変換（KNorm → Cls）|
| `lib/backend/static_manage.ml` | `toC.ml` 向けの静的管理（ty/range/coercion のシングルトン登録、capp ショートサーキット用の `fast_inj`/`fast_proj`/`fast_proj_tp`） |
| `lib/backend/toC.ml` | C コード生成（Cls → C）。monotonic ref/array の deref/subst/get/put 向けに、静的な型から coercion 生成 C コードをコンパイル時に組み立てる `make_s_coercion_call` も持つ |
| `lib/backend/builder.ml` | clang コマンド文字列の組み立て（`build_clang_cmd`）・出力の一意な命名（`unique_base`）。`Resources.*` で絶対パスを取得。実行自体は `runner.ml`（単一プログラム）/ `lib/bench/bench_builder.ml`+`bench_compiler.ml`（ベンチ、並列コンパイル）が担う |
| `lib/backend/runner.ml` | 単一プログラムのビルド・実行（`-c` モード、`Runner.build_run`） |
| `lib/pipeline.ml`（+ `pipeline.mli`） | パイプライン全体の統括。`bin/main.ml`/`bin/bench.ml`/テストが共通で使う公開インターフェースを `.mli` で明示 |
| `bin/main.ml` | REPL / ファイル実行エントリポイント |
| `libC/` | C ランタイム。`capp.c`/`crc.c`/`ty.c` が coercion 適用の中核、`ref.c`/`arr.c`/`lst.c`/`tpl.c` が各型の実装 |
| `test/testcases.ml` | インタプリタテストケース本体（`test_interpreter.ml` から10通りの config で実行） |
| `test/test_typing.ml` | 型推論テスト（OUnit2）|
| `test/test_mutate.ml` / `test/test_grift.ml` | `lib/bench/mutate.ml`（出現順スロット付番・全 mutant のインタプリタ差分カバレッジ）と `lib/bench/bench_grift.ml`（S式 round-trip・スロット数が ML 側と一致）のユニットテスト |
| `test/check_mutants.ml` | ベンチと同じ軸別アブレーション（untypedALHMT 基準 + id_opt/eagerness/hash/monotonic/tvs_opt/typed を1つずつ反転、× dynamize/static）の各ターゲットで全 mutant を実際にコンパイル・実行し、標準出力が正解値と一致するかを見る end-to-end 正当性テスト。`compile_test/mutation_test.sh` から呼ぶ |
| `bin/bench.ml` + `lib/bench/` | mutation ベンチマーク。`lib/bench/`（`bench_config`/`bench_target`/`bench_builder`/`bench_compiler`/`bench_runner`/`bench_grift`/`bench_output`/`bench_progress`/`bench_json`/`mutate`）＋ 薄い `bin/bench.ml`。コンパイル専用。コンパイル（`bench_builder`/`bench_compiler`、並列）と計測（`bench_runner`、直列）を分離。mutation スロットはソース出現順に番号付けし、ML 側（`mutate`）と grift 側（`bench_grift`）で同一の `mutant_index` を共有。詳細は [docs/howto.md](docs/howto.md) |

正確なファイル一覧は `find lib libC -name "*.ml" -o -name "*.c" -o -name "*.h"` で随時確認すること（このリポジトリはファイル配置がしばしば変わるため、本表は目安）。

---

## クイックリファレンス

```bash
dune build && dune runtest          # ビルド + ユニットテスト
bash compile_test/dotests.sh        # コンパイルテスト一括実行
lSdti file.ldti [-c] [-a|-b] [--non_monotonic] [--static]
```

詳しい手順・CLI オプションの意味・言語構文の追加分は **[docs/howto.md](docs/howto.md)** を参照。
