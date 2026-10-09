# plot_all.py
import os
from benchviz import (
    latest_date_dir, check_pair_exists, TARGET_PAIRS, STATIC_SUMMARY_GROUPS
)

def prune_empty_dirs(root: str) -> None:
    """root 以下で、生成物が1つも入らなかった空ディレクトリを消す。
    プロッタが ensure_dir だけして 1 枚も描かなかったときの「空フォルダ」対策。"""
    if not os.path.isdir(root):
        return
    for cur, dirs, files in os.walk(root, topdown=False):
        if cur == root:
            continue
        if not os.listdir(cur):          # 空になったら（子を消した後も含む）
            try:
                os.rmdir(cur)
                print(f"[plot_all] removed empty dir: {cur}")
            except OSError:
                pass

from plot_relative import plot_relative, plot_static_summary
from plot_scattered import plot_scattered
from plot_metric import plot_metric
from plot_stacked_time import run as run_plot_stacked_time  # 累積性能グラフ

EXTRA_METRICS = ["cast", "inference", "mem", "longest"]

def run_static_summaries(base, comps, date_dir):
    """static summary: comps 全体の図と、comp ごとの図を出す。
    ログの無い comp は除いて描く（全体図は残った comp だけで描く）。"""
    present = [c for c in comps if check_pair_exists(date_dir, base, c, True)]
    for c in comps:
        if c not in present:
            print(f"[DEBUG] スキップ: {date_dir} に {base} または {c} の static ログがありません。")
    if not present:
        return
    if len(present) > 1:
        plot_static_summary(base, present)
    for c in present:
        plot_static_summary(base, c)

def plot_one(base, comp):
    """1 つの (base, comp) について relative / scattered / metrics を描く（comp はリストでもよい）"""
    plot_relative(base, comp, False)
    plot_scattered(base, comp, False)
    for m in EXTRA_METRICS:
        plot_metric(base, comp, False, m)

def run_plots(base, comps, date_dir):
    """comps 全部をまとめた図と、comp 1つずつの図を出す（mutant の計測ログ）。
    累積性能グラフ（cumulative）は plot_stacked_time が同じ組み合わせで別に描く。"""
    print(f"\n[DEBUG] ---> run_plots 開始: base={base}, comps={comps}")
    present = [c for c in comps if check_pair_exists(date_dir, base, c, False)]
    for c in comps:
        if c not in present:
            print(f"[DEBUG] スキップ: {date_dir} に {base} または {c} のログがありません。")
    if len(present) > 1:
        plot_one(base, present)
    for c in present:
        plot_one(base, c)
    print(f"[DEBUG] <--- run_plots 完了: base={base}, comps={comps}")

def main():
    try:
        latest_ts, date_dir = latest_date_dir("logs")
    except Exception as e:
        print(f"[DEBUG] ログディレクトリの取得に失敗しました: {e}")
        return

    print("\n=== Processing Non-Static Logs ===")
    for base, comps in TARGET_PAIRS:
        run_plots(base, comps, date_dir)

    print("\n=== Processing Cumulative Plots ===")
    run_plot_stacked_time(date_dir, pairs=TARGET_PAIRS)

    print("\n=== Processing Static Logs ===")
    for base, comps in STATIC_SUMMARY_GROUPS:
        run_static_summaries(base, comps, date_dir)

    # 生成物ゼロで作られてしまった空フォルダを掃除
    prune_empty_dirs(date_dir)

    print("\n[DEBUG] スクリプトの実行が最後まで完了しました。")

if __name__ == "__main__":
    main()
