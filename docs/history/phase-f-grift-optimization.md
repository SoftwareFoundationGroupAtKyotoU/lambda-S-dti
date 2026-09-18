# Phase F — grift比較ベンチマーク・静的最適化（2026-02-03〜2026-03-16）

[docs/history.md](../history.md) の「プレヒストリ」から参照。一つ新しい話題は [Phase G](phase-g-pipeline-tuple.md) へ、一つ古い話題は [Phase E](phase-e-rename-ci.md) へ。

他の gradual typing 処理系 **grift** との性能比較ベンチマーク基盤を整備しつつ、static/atomic な inject/project のインライン化・hash-consing・compose のメモ化など、C バックエンドの性能最適化を進めた、この期間で最も commit 数の多いフェーズ。マージのみの commit は省略。

## grift 比較ベンチマーク基盤

- **82f92f2** (2026-03-09) grift の `map_mono` をカリー化
- **15b8ff6** (2026-03-09) grift コンパイルを並列化
- **cc543a3** (2026-02-24) grift と lSdti の計測順序を対応させる
- **cd58070** (2026-02-24) grift が C を出力できるように、cast 数と最長チェーン長も出力
- **9183b88** (2026-03-01) grift を list に対応
- **78414b0** (2026-03-03) ml と grift で dynamize の総数を合わせる
- **c37d5eb** (2026-02-28) `GRIFTC` に改名、value を改造（途中）
- **664e51c** (2026-02-11) grift を扱えるように、stdlib 用に tyenv を変更、gcc 失敗時にエラー表示
- **b14e8fb** (2026-02-11) grift の計測を行う Python コードを追加
- **cfb6e5a** (2026-02-11) grift 用の Dockerfile を作成
- **9f451df** (2026-02-11) `grift_builder` で grift をビルド
- **846896a** (2026-02-11) grift サンプルを追加
- **dc6d775** (2026-02-11) samples と `run_grift` を変更
- **1d82a5d** (2026-02-13) dynamize の順番をそろえる（対応途中）
- **dbe2106** (2026-02-13) static で syntacticity を同一視

## ベンチマーク・計測基盤

- **2490c59** (2026-03-16) plot の見栄えを修正、テキスト/テーブルの ON/OFF 切り替え
- **0825c90** (2026-03-09) plot のログ出力を充実
- **3aa17c1** (2026-03-09) debug モードで clang コマンドを出力
- **bdf343b** (2026-03-09) `incsum` を追加
- **2e69c8d** (2026-03-09) ログを読み込まないよう `.dockerignore` を修正
- **2ed0ebd** (2026-03-06) scatter/metric を 0 始まりに、色を固定、relative を対数スケールに
- **2dcc014** (2026-02-26) C backend も計測対象に
- **f51575d** (2026-02-19) bench を Docker 内で実行
- **c353693** (2026-02-05) STATIC との時間比較を出力
- **dc2e453** (2026-02-06) 複数ケースの比較に対応
- **71fe4bf** (2026-02-06) sample を移動
- **7c6fae6** (2026-02-11) sample の input を追加
- **a0ec7e6** (2026-02-11) samples に値を出力させる、`loop_mono` を追加
- **5b90fc6** (2026-02-11) 静的メトリクスの出力に対応
- **d864d91** (2026-02-03) static benchmark に対応
- **9f4c47c** (2026-02-03) `samples/` を追加
- **8399534** (2026-02-03) occur check coercion を追加、bench が引数を取れるように

## C バックエンドの最適化

- **1fa2be3** (2026-03-09) `has_tv` を持たせ、HASH に TV 関連の coercion を含めないように
- **4da7631** (2026-03-07) cast カウントを inject/project にも適用
- **76d7430** (2026-03-07) `ty_find` の抜けを修正
- **845a6aa** (2026-03-06) 不要なクロージャを生成しないように、値でない `LetExp` の translate を変更
- **415e068** (2026-03-05) fun coercion のバグを修正
- **7363dc6** (2026-03-05) `toC`/`pipeline` を統合
- **57aa77d** (2026-03-05) hash-consing と compose のメモ化を追加
- **ca26ade** (2026-03-04) GC の初期設定を実行
- **d539fcb** (2026-03-04) list の変更に追従
- **fa2f76c** (2026-03-04) list の wrap を、CAST でない場合はタグ付きポインタに変更
- **b4a7399** (2026-03-01) dyn 周りを整理
- **f804463** (2026-02-28) value の改造を完了
- **fe17b8e** (2026-02-28) app の最適化を正しく実装
- **889ca1d** (2026-02-26) fun の構造を改変
- **b93d83c** (2026-02-25) fun 関連の `GC_MALLOC` 回数を削減
- **fde44e7** (2026-02-23) `INTinj` 等がポインタ非等価のとき coerce できない問題を修正
- **9bb5964** (2026-02-23) `non_atom` の `id_crc` のバグを修正
- **310308b** (2026-02-21) static で atomic な inject/project を `coerce` 呼び出しなしでインライン化
- **e38669a** (2026-02-16) `Caml.` を削除
- **3e1c597** (2026-02-16) dyn 最適化
- **202ccb6** (2026-02-06) unity でテスト
- **c5eb89d** (2026-02-06) compose のテストを追加
- **460d3f3** (2026-02-11) tvs の無駄な `MALLOC` を除去
- **7746d2f** (2026-02-11) パターンマッチの warning 抑制、`blame`/`did_not_match` に noreturn 属性、`read_int` を `stdlib.c` に追加
- **ab1c66d** (2026-02-11) OCaml を 4.14.1 以上に制限
