import os
from benchviz import (
    latest_date_dir, check_pair_exists, TARGET_PAIRS
)

from plot_herman import plot_herman
from plot_relative import plot_relative
from plot_scattered import plot_scattered
from plot_metric import plot_metric

EXTRA_METRICS = ["cast", "inference", "mem", "longest"]

def run_plots(base, comp, static, date_dir):
    print(f"\n[DEBUG] ---> run_plots 開始: base={base}, comp={comp}, static={static}")
    
    if not check_pair_exists(date_dir, base, comp, static):
        print(f"[DEBUG] スキップ: {date_dir} に {base} または {comp} のログがありません。")
        return

    print(f"[DEBUG] ログを確認しました。プロット処理に入ります...")

    if isinstance(comp, list):
        print(f"[DEBUG] 複数比較 (リスト) モード: {comp}")
        plot_herman(base, comp, static)
        plot_relative(base, comp, static)
        plot_scattered(base, comp, static)
        for m in EXTRA_METRICS:
            print(f"[DEBUG] plot_metric 実行中 (メトリクス: {m}, 全体)")
            plot_metric(base, comp, static, m)

        for c in comp:
            print(f"[DEBUG] 個別プロット実行中: {c}")
            plot_herman(base, c, static)
            plot_relative(base, c, static)
            plot_scattered(base, c, static)
            for m in EXTRA_METRICS:
                print(f"[DEBUG] plot_metric 実行中 (メトリクス: {m}, 個別: {c})")
                plot_metric(base, c, static, m)

    else:
        print(f"[DEBUG] 単体比較モード: {comp}")
        plot_herman(base, comp, static)
        plot_relative(base, comp, static)
        plot_scattered(base, comp, static)
        for m in EXTRA_METRICS:
            print(f"[DEBUG] plot_metric 実行中 (メトリクス: {m})")
            plot_metric(base, comp, static, m)

    print(f"[DEBUG] <--- run_plots 完了: base={base}, comp={comp}")

def main():
    cwd = os.getcwd()
    print(f"[DEBUG] カレントディレクトリ (CWD): {cwd}")
    print(f"[DEBUG] 'logs' フォルダの絶対パス: {os.path.abspath('logs')}")
    
    try:
        latest_ts, date_dir = latest_date_dir("logs")
        print(f"[DEBUG] 対象ログディレクトリ: {date_dir} (絶対パス: {os.path.abspath(date_dir)})")
    except Exception as e:
        print(f"[DEBUG] ログディレクトリの取得に失敗しました: {e}")
        return

    print(f"[DEBUG] TARGET_PAIRS: {TARGET_PAIRS}")

    print("\n=== Processing Non-Static Logs ===")
    for base, comp in TARGET_PAIRS:
        run_plots(base, comp, False, date_dir)

    print("\n=== Processing Static Logs ===")
    for base, comp in TARGET_PAIRS:
        run_plots(base, comp, True, date_dir)
        
    print("\n[DEBUG] スクリプトの実行が最後まで完了しました。")

if __name__ == "__main__":
    main()