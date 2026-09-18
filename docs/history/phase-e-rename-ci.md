# Phase E — lambda-S-dtiへの命名統一・CI整備・fully-staticコンパイラ（2026-01-02〜2026-01-23）

[docs/history.md](../history.md) の「プレヒストリ」から参照。一つ新しい話題は [Phase F](phase-f-grift-optimization.md) へ、一つ古い話題は [Phase D](phase-d-cbackend-bootstrap.md) へ。

このフェーズの `605f54a` で、プロジェクト名が現在の **lambda-S-dti** に統一された。CI（GitHub Actions）の整備もこの時期に行われている。

- **30e8a83** (2026-01-23) `.opam` を再生成
- **7ea5a38** (2026-01-23) CI が Boehm GC と cJSON をインストールするように
- **32dd407** (2026-01-23) `gc.h` を CI で使えるように
- **98013b3** (2026-01-23) `dotests.sh` を CI に追加、compile_test を追加、closure が長時間かかる問題を修正
- **d6507c5** (2026-01-21) opam の depends を更新
- **605f54a** (2026-01-21) プロジェクト名を **lambda-S-dti** に統一
- **9551b8e** (2026-01-21) CI を簡略化
- **d492bf6** (2026-01-21) README/CITATION/LICENSE を整備
- **a87ea5b** (2026-01-21) bench でメモリ使用量を計測できるように、crc の構造体を変更、occur check・dummy blame label の問題を解消、fully-static 決め打ちコンパイラを追加
- **932c1ae** (2026-01-14) C バックエンドを再度大幅に変更
- **d5d6799** (2026-01-07) pretty-printer を改良
- **695a99f** (2026-01-04) `hd`/`tl` の実装を変更
- **59a79bf** (2026-01-02) main と bench のコードを整理
