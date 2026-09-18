# Phase C — K正規化体系の修正（2025-05-07〜2025-06-26）

[docs/history.md](../history.md) の「プレヒストリ」から参照。一つ新しい話題は [Phase D](phase-d-cbackend-bootstrap.md) へ、一つ古い話題は [Phase B](phase-b-gc-polymorphism.md) へ。

Phase B で「lambdaS1DTI のインタプリタ完成」を迎えた直後、K 正規化の体系にバグが見つかり、その修正に充てられた短い期間。

- **3a71e62** (2025-06-26) alternative の k 正規化まで対応
- **ea2b109** (2025-06-25) 変数 id をなるべく作らない変換を導入
- **0db3aa0** (2025-06-06) 体系の修正完了
- **d0f79c2** (2025-05-31) ファイルチェック
- **c95974c** (2025-05-07) K 正規化が完成、体系にバグを発見
