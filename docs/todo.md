# todo — 残作業

[CLAUDE.md](../CLAUDE.md) から参照される用途別ドキュメントの一つ。「次に何をやるか」をここに集約する。
経緯は [history.md](history.md)、使い方は [howto.md](howto.md) を参照。

新しく着手する前に、まず `git log` と `dune runtest`/`compile_test/dotests.sh` を実行して以下がまだ有効か確認すること（実装は git log の方が正しい）。
このリストは `grep -rn "TODO\|FIXME\|yet"` で拾えるものを中心に棚卸ししたもの（初出 2026-08-08、行番号は 2026-09-19 時点のものに更新済み）。

---

## stdlib の CUnimplementedを消す

## 「Boxed」的な汎用タグの導入

個々の新しい型ごとに ground tag を1つずつ消費するのをやめ、「boxed／拡張型」を表す **共通の1つの ground tag** を用意し、その中身（ヒープ確保したオブジェクトの先頭）に実際の型を示す小さな種別フィールドを持たせる2段構成にする。こうすれば、3bit の ground tag 空間を増やさずに任意個の「低頻度・後発の型」を追加できるようになる（float 含め今後増える型はすべてこの Boxed タグ配下に统合する運用も考えられる）

## NaN Tagging による再実装の検討

現在の「ポインタ/整数の下位ビットを盗んでタグ化する」方式を、IEEE754 の double が持つ NaN のペイロードビット（quiet NaN で約51bit）を使ってタグと小さな payload を埋め込む「NaN タギング」方式に置き換えることを、より抜本的な将来の再設計として検討する。JS エンジン（V8 の Smi/HeapObject、JavaScriptCore の NaN-boxing 等）で使われる手法で、ポインタか即値かを下位ビットで判別する現行方式より柔軟に型を詰め込める可能性がある。ただし `value` の表現（`libC/types.h:42` の `typedef intptr_t value;`）や `tag_value`/`untag_value`/`cast`/`coerce` 全体に及ぶ大規模な再設計になるため、実際に着手するかどうかは別途判断する

## blame ラベルの伝播が未実装

monotonic reference/array の deref・subst（`GetExp`/`PutExp`/`DerefExp`/`SubstExp`）で `make_s_coercion` を呼ぶ際、実際の blame range/polarity ではなく `Utils.Error.dummy_range, Pos` を仮置きしている。`compose` が `CMRef`/`CMArray` の unify に失敗して `CFail` を生成する箇所も同様に dummy range を使っている。C ランタイム側の `make_s_coercion`（`libC/crc.c:883`）にも同じ制約がコメントで明記されている。

- `lib/utils/coercion.ml:97` — `compose` 冒頭の `(* TODO: blame *)`
- `lib/utils/coercion.ml:312,325` — `CMRef`/`CMArray` の unify 失敗時に生成する `CFail` が dummy range 固定
- `lib/interpreter/eval.ml:222,242,276,301,620,624,630,634` — `DerefExp`/`SubstExp`/`GetExp`/`PutExp` の monotonic 経路
- `libC/crc.c:883` — `make_s_coercion`（C 版）が同じ理由で blame label 未対応とコメントされている

正しい blame range を持たせるには、これらの呼び出し元まで元の cast 式の range を伝播させる必要がある（未調査）。

なお `lib/backend/toC.ml` の `monotonic_dummy_range`（deref/subst/get/put 向けの効率的な coercion 生成パス、[history.md](history.md) 参照）は名前が似ているが別物: こちらは「`TyDyn` との合流点を判定するための、コンパイル時にのみ使う実体のないダミー range」であり、上記の「実行時 blame に本来必要な range が来ていない」という問題とは無関係。

## `--static`/`--hash`/`--tvs_opt` の未対応の組み合わせ

- `lib/config.ml:33,35,37,39` — `--hash`/`--static`/tvs 最適化はコンパイルモード専用で、インタプリタ実行時に指定すると `NotImplemented` で `failwith` する
- `lib/backend/static_manage.ml:150` — `--static` モードで `TyCoercion` 型が来ると未対応（`Static_manage_bug "yet"`）
- `lib/backend/static_manage.ml:268` — `--static` モードで `CFail` coercion が来ると未対応（`Static_manage_bug "yet"`）

## CFail / 想定外の coercion・型が toC まで到達すると不親切なエラーになる

`lib/typing/typing.ml:345`（`type_of_coercion (CFail _) = assert false`）と同様の問題が `toC.ml` にも複数箇所ある。いずれも「通常の経路には現れない想定」だが、意図しない経路で来た場合にデバッグしづらいエラーメッセージになる。

- `lib/backend/toC.ml:71` — `toC_tycontent` が未知の `ty` パターンで `ToC_bug "toC_content yet"`
- `lib/backend/toC.ml:225` — `toC_crc` が `CFail` で `ToC_bug "toC_crc yet"`
- `lib/backend/toC.ml:354` — `set_ty` が未知の `ty` パターンで `ToC_bug "set_ty yet"`

## monotonic ref/array coercion の `has_tv` が未設定

`libC/crc.c:325`（`new_mref`）・`crc.c:345`（`new_marray`）で `has_tv` フィールドがコメントアウトされたまま（`/*.has_tv = TODO yet, */`）になっており、実質 0 固定。`CMRef`/`CMArray` の runtime crc が型変数を含んでいても `has_tv` に反映されない。non-monotonic 版（`new_ref`/`new_array`）は `c1->has_tv | c2->has_tv` を正しく設定しているのと対称性が崩れている。影響範囲は未調査。

## bench のインタプリタ計測（廃止済み・復活は要検討）

`f2a9c0a`「refactor bench」で bench はコンパイル専用になり、インタプリタの時間/メモリ
計測（旧 `mem_json` の `Failure "yet"`、旧 `Text` out_mode）と core_bench 基盤は削除した。
mutation 後プログラムがインタプリタで評価まで通るかの回帰は `test/test_mutate.ml` の
差分カバレッジテストでカバーしている。

インタプリタ計測を復活させる場合は (a) サンプルが stdin 入力を要求する形式に変わった
ことへの対応（`samples/input/<name>.txt` を評価時に流す）、(b) 計測基盤の再導入が必要。
旧実装は `f2a9c0a` 以前の git 履歴（`Translate.CC.translate` / `translate_alt` →
`Eval.CC.eval_program` を `measure_mem_to_json` で包む形）を参照。

## その他の小さな TODO（旧リストから継続）

- **`Cls.Cast` 周りの base_inj/base_proj シングルトン化**（旧 TODO）は、ショートサーキット最適化（インライン展開でディスパッチを消す方式）によって実質的に置き換えられた。まだ性能が問題になる場合のみ再検討する。
- `lib/frontend/lexer.mll:113` — コメントが閉じられないまま EOF に達した場合、`Format.eprintf` で警告を出すのみで例外を送出していない。
- `lib/utils/utils.ml:56` — `Utils.Lexing` モジュールの存在意義が不明なコードに `(* TODO: why does it exist? *)` が付いたまま。
- `lib/utils/pp.ml:85` — `gt_binop`（演算子の pretty-print 用の優先順位比較）に `(* TODO: replace to level *)`。優先順位を表す `level` のようなものに置き換えたいという意図と思われるが未着手。
- `bin/main.ml:28` — ファイルモード実行時、プログラムが正しく書けていなくてもコンパイルが通ってしまうことがある（例: `bad.ml`）。原因未調査。

## テストの TODO（コメントアウトされたまま復活していないケース）

以下のテストファイルに、期待値の記述が難しい／未対応機能のためコメントアウトされたままの `(* TODO: ... *)` ケースが残っている。個々の内容は各ファイルを参照。

- `test/test_pp.ml:145,165,168,171,172`
- `test/test_typing.ml:165`
- `test/test_translate.ml:27,40`

---

## 完了済み

過去に完了した TODO は随時この節から削除し、詳細は [history.md](history.md) に記録する（現時点でこの節は空）。
