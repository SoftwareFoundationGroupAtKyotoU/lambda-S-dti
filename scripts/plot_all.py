# plot_all.py
import os
from benchviz import (
    latest_date_dir, check_pair_exists, TARGET_PAIRS
)

from plot_herman import plot_herman
from plot_relative import plot_relative, plot_static_summary
from plot_scattered import plot_scattered
from plot_metric import plot_metric
from plot_compare import plot_compare  # ★ plot_compare をインポート追加

EXTRA_METRICS = ["cast", "inference", "mem", "longest"]

def run_plots(base, comp, static, date_dir):
    print(f"\n[DEBUG] ---> run_plots 開始: base={base}, comp={comp}, static={static}")
    
    if not check_pair_exists(date_dir, base, comp, static):
        print(f"[DEBUG] スキップ: {date_dir} に {base} または {comp} のログがありません。")
        return

    # ==========================================
    # ★ Static の場合は専用の統合プロットのみを実行する
    # ==========================================
    if static:
        print(f"[DEBUG] Staticモード: 統合Relativeプロットのみ実行します")
        if isinstance(comp, list):
            plot_static_summary(base, comp)
            # 個別も欲しい場合は以下を活かす（不要ならコメントアウトでOKです）
            for c in comp:
                plot_static_summary(base, c)
        else:
            plot_static_summary(base, comp)
        print(f"[DEBUG] <--- run_plots 完了: base={base}, comp={comp} (Static)")
        return

    # ==========================================
    # 以下は通常（Dynamic/Mutant）の処理
    # ==========================================
    print(f"[DEBUG] ログを確認しました。プロット処理に入ります...")

    if isinstance(comp, list):
        print(f"[DEBUG] 複数比較 (リスト) モード: {comp}")
        plot_herman(base, comp, static)
        plot_relative(base, comp, static)
        plot_scattered(base, comp, static)
        for m in EXTRA_METRICS:
            plot_metric(base, comp, static, m)

        for c in comp:
            print(f"[DEBUG] 個別プロット実行中: {c}")
            plot_herman(base, c, static)
            plot_relative(base, c, static)
            plot_scattered(base, c, static)
            for m in EXTRA_METRICS:
                plot_metric(base, c, static, m)

    else:
        print(f"[DEBUG] 単体比較モード: {comp}")
        plot_herman(base, comp, static)
        plot_relative(base, comp, static)
        plot_scattered(base, comp, static)
        for m in EXTRA_METRICS:
            plot_metric(base, comp, static, m)

    print(f"[DEBUG] <--- run_plots 完了: base={base}, comp={comp}")

def main():
    cwd = os.getcwd()
    try:
        latest_ts, date_dir = latest_date_dir("logs")
    except Exception as e:
        print(f"[DEBUG] ログディレクトリの取得に失敗しました: {e}")
        return

    print("\n=== Processing Non-Static Logs ===")
    for base, comp in TARGET_PAIRS:
        run_plots(base, comp, False, date_dir)

    print("\n=== Processing Static Logs ===")
    for base, comp in TARGET_PAIRS:
        run_plots(base, comp, True, date_dir)
        
    # ==========================================
    # ★ 追加: Mono vs Poly の Compare プロット処理
    # ==========================================
    print("\n=== Processing Compare Logs (Mono vs Poly) ===")
    # TARGET_PAIRS から使用されているすべてのモードを抽出 (重複排除)
    all_modes = set()
    for base, comp in TARGET_PAIRS:
        all_modes.add(base)
        if isinstance(comp, list):
            all_modes.update(comp)
        else:
            all_modes.add(comp)
            
    # 各モードに対して compare プロットを実行
    for mode in all_modes:
        print(f"\n[DEBUG] Compareプロット実行中: mode={mode}")
        # plot_compare 側で該当ログがなければ自動でスキップされるので安全です
        plot_compare(mode, static=False)
        plot_compare(mode, static=True)

    print("\n[DEBUG] スクリプトの実行が最後まで完了しました。")

if __name__ == "__main__":
    main()