# Phase G — 論文実験・pipeline統合・タプル対応（2026-04-01〜2026-05-21）

[docs/history.md](../history.md) の「プレヒストリ」から参照。一つ新しい話題は [Phase H](phase-h-ref-array-bench-refactor.md) へ、一つ古い話題は [Phase F](phase-f-grift-optimization.md) へ。

論文用の実験データ収集（church_compare 等）と並行して、`LS1` を `CC` に統合する・`pipeline.ml` に処理をまとめる・`config` を整理するといった内部構造の整理が進んだ時期。末尾でタプル対応がインタプリタ・コンパイラ双方に入る。

- **d3d6db9** (2026-05-21) `app.c` の `two` を `fun` に変更
- **ecacde3** (2026-05-17) ファイル整理
- **c11ef6c** (2026-04-18) タプルをコンパイラに実装
- **7bb149a** (2026-04-13) タプルをインタプリタに実装
- **13fa9b9** (2026-04-08) B（`intoB`）用の eager テストを追加
- **25f4c60** (2026-04-08) list や他の binop のテストを追加、config をリファクタ
- **798e3bd** (2026-04-08) pipeline を改訂し、main/bench/test で共通利用するように
- **7987f36** (2026-04-05) eval テストを圧縮、config が kNorm 引数を取るように
- **ec16619** (2026-04-04) LS1 を CC に統合
- **f71d2f2** (2026-04-03) ビルド処理を `builder.ml` へ移動
- **1039e47** (2026-04-03) bench のコンパイル処理を pipeline へ統合
- **849ddf5** (2026-04-02) `fresh_tv` を pipeline から分離
- **92bb290** (2026-04-02) issue 1, 2 用のテストファイルを追加
- **c5c7fa2** (2026-04-02) `church_4` テストを追加
- **49e417d** (2026-04-02) プロファイリングを強化
- **fb85a0f** (2026-04-01) 論文用実験（`church_compare` 追加など）
