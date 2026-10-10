# plot_paper.py
#
# 論文（lsdti-compiler-paper）の評価節で使う 30 枚の図を、論文用のラベル・スタイルで描く。
# データの読み込み・フィルタ・baseline は plot_stacked_time（累積グラフ）と
# plot_relative（相対グラフ, zigzag 版）とまったく同じ関数を使い、変えるのは
# ラベル・スタイルと、相対グラフの x 軸の目盛り（k/N のビン境界）だけ。
#
#   figures/rq1_church_cumulative.png          累積: typed vs. untyped（church）
#   figures/rq2_{ray,church}_relative.png      相対: 3 ablation / untyped
#   figures/supp/rq1_<bench>.png               累積: typed vs. untyped
#   figures/supp/rq2_<bench>.png               累積: untyped + 3 ablation
#   figures/supp/rq3_<bench>.png               累積: typed vs. Grift
#
# 使い方（リポジトリ直下で）:
#   BENCH_LOG_DIR=20261008-20:15:54 uv run python scripts/plot_paper.py --paper-root ~/lsdti-compiler-paper
# 既存の PNG は上書き前に <paper-root>/figures/old-<今日の日付>/ へ同じ相対パスで退避する。

import argparse
import datetime
import json
import os
import re
import shutil
from typing import Dict, List

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, NullFormatter, NullLocator

from benchviz import (
    get_config, get_plot_style, ingest_latest_as_map, latest_date_dir, ratio_with_delta_ci,
)
from plot_relative import apply_smart_log2_scale
from plot_stacked_time import (
    ACCEPTABLE_FRACTION, DEFAULT_M, DEFAULT_N, _OVERHEAD_TICKS, collect, overheads,
)

LABEL = {
    "typedALHMT":   "Gradti (typed)",
    "untypedALHMT": "Gradti",
    "untypedSLHMT": "w/o dual-entry closures",
    "untypedALhMT": "w/o hash consing",
    "untypedALHMt": "w/o type-parameter pruning",
    "GRIFTCM":      "Grift",
}
# 相対グラフの凡例（1行3列）に長いラベルが収まらないときの短縮形
SHORT_LABEL = {
    "untypedSLHMT": "w/o dual entry",
    "untypedALhMT": "w/o hash consing",
    "untypedALHMt": "w/o pruning",
}
BENCH = {"church-1048576": "church"}   # それ以外のベンチは名前そのまま
# 論文のファイル名 → ログのベンチ名（ログ側は歴史的に "blacksholes" と綴っている）
LOG_BENCH = {"blackscholes": "blacksholes", "church": "church-1048576"}

ABLATIONS = ["untypedSLHMT", "untypedALhMT", "untypedALHMt"]
RQ12_BENCHES = ["array", "blackscholes", "fft", "n_body", "quicksort", "ray", "tak", "church", "loop", "fsm"]
RQ3_BENCHES = ["array", "blackscholes", "fft", "n_body", "quicksort", "ray", "tak"]

CUMULATIVE_SIZE = (2.6, 1.9)
RELATIVE_SIZE = (2.2, 1.7)
GUIDE = dict(color="0.6", lw=0.8, ls=":", zorder=1)

plt.rcParams.update({"font.size": 8, "legend.fontsize": 7, "axes.labelsize": 8,
                     "xtick.labelsize": 7, "ytick.labelsize": 7})


def save(fig, path: str, backup_root: str, paper_root: str) -> None:
    if os.path.exists(path):
        bak = os.path.join(backup_root, os.path.relpath(path, os.path.join(paper_root, "figures")))
        if not os.path.exists(bak):
            os.makedirs(os.path.dirname(bak), exist_ok=True)
            shutil.copy2(path, bak)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    for p in (path, os.path.splitext(path)[0] + ".pdf"):
        fig.savefig(p, dpi=300, bbox_inches="tight", pad_inches=0.02)
    plt.close(fig)
    print(f"[plot_paper] wrote {path}")


# =========================
# 累積グラフ（plot_stacked_time.plot_benchmark と同じ曲線）
# =========================

def plot_cumulative(data, bench: str, base: str, modes: List[str], path: str, **save_args) -> None:
    series_by_mode = data[LOG_BENCH.get(bench, bench)]
    baseline = series_by_mode[base].endpoint("static")   # 基準モードの最も静的な mutant
    curves = [(mode, overheads(series_by_mode[mode], baseline)) for mode in modes]
    n, m = DEFAULT_N, DEFAULT_M

    all_ovh = np.concatenate([o for _, o in curves])
    lower = min(float(all_ovh.min()), 1.0) / 1.15
    upper = max(float(all_ovh.max()), m) * 1.15

    fig, ax = plt.subplots(figsize=CUMULATIVE_SIZE, layout="constrained")
    for i, (mode, ovh) in enumerate(curves):
        xs = np.concatenate(([lower], ovh, [upper]))
        ys = np.concatenate(([0.0], np.arange(1, len(ovh) + 1) / len(ovh) * 100.0, [100.0]))
        ys[-1] = ys[-2]
        ax.step(xs, ys, where="post", color=get_plot_style(mode, i)["color"], linewidth=1.2,
                label=LABEL[mode], zorder=2)

    for x in (1.0, n, m):
        ax.axvline(x, **GUIDE)
    ax.axhline(ACCEPTABLE_FRACTION, **GUIDE)

    ax.set_xscale("log")
    ax.set_xlim(lower, upper)
    ticks = [t for t in _OVERHEAD_TICKS if lower <= t <= upper]
    ax.xaxis.set_major_locator(FixedLocator(ticks))
    ax.xaxis.set_minor_locator(NullLocator())
    ax.set_xticklabels([f"{t:g}x" for t in ticks])
    ax.set_ylim(0, 100)
    ax.set_yticks([0, 20, 40, 60, 80, 100])

    # 1 行では 2.6 in に収まらないので 2 行に折る
    ax.set_xlabel(f"Slowdown relative to the fully static\n{LABEL[base]} (log scale)")
    ax.set_ylabel("% of configurations")
    place_legend(fig, ax, [(np.concatenate(([lower], o)), np.arange(len(o) + 1) / len(o) * 100.0)
                           for _, o in curves])
    save(fig, path, **save_args)


def place_legend(fig, ax, lines) -> None:
    """凡例は右下に置くが、そこで曲線を隠してしまうときは左上と比べて、隠す点の少ない方に置く。
    lines: 各曲線の階段の (xs, ys)。"""
    def covered(legend) -> int:
        fig.canvas.draw()
        box = legend.get_window_extent()
        hits = 0
        for xs, ys in lines:
            # 階段を x 方向に細かく標本化（水平部分）し、各段の縦の線分も標本化する
            lo, hi = ax.get_xlim()
            gx = np.geomspace(lo, hi, 2000)
            gy = ys[np.clip(np.searchsorted(xs, gx, side="right") - 1, 0, len(ys) - 1)]
            vx = np.repeat(xs[1:], 10)
            vy = np.concatenate([np.linspace(a, b, 10) for a, b in zip(ys[:-1], ys[1:])])
            disp = ax.transData.transform(np.column_stack((np.concatenate((gx, vx)), np.concatenate((gy, vy)))))
            hits += int(np.sum((disp[:, 0] >= box.x0) & (disp[:, 0] <= box.x1)
                               & (disp[:, 1] >= box.y0) & (disp[:, 1] <= box.y1)))
        return hits
    best = None
    for loc in ("lower right", "upper left"):
        legend = ax.legend(loc=loc, ncol=1, frameon=True, fancybox=False, framealpha=0.85,
                           edgecolor="0.85", borderpad=0.3, borderaxespad=0.3,
                           handlelength=1.5, labelspacing=0.25)
        n = covered(legend)
        if best is None or n < best[1]:
            best = (loc, n)
        if n == 0:
            break
    ax.legend(loc=best[0], ncol=1, frameon=True, fancybox=False, framealpha=0.85,
              edgecolor="0.85", borderpad=0.3, borderaxespad=0.3, handlelength=1.5, labelspacing=0.25)


# =========================
# 相対グラフ（plot_relative の zigzag 版と同じ点）
# =========================

def dynamized_counts(date_dir: str, mode: str, log_bench: str) -> Dict[int, int]:
    """mutant_index -> k（Dyn 化した注釈の数）。ログに k は無いので、after_mutate の `?` の数から
    最も静的な mutant（mutant_index 1）の分を引いて求める。最大値が N（Dyn 化しうる注釈の数）。"""
    counts = {}
    with open(os.path.join(date_dir, f"{mode}_{log_bench}.jsonl"), encoding="utf-8") as f:
        for line in f:
            if line.strip():
                rec = json.loads(line)
                counts[int(rec["mutant_index"])] = len(re.findall(r"\?", rec["after_mutate"]))
    return {i: q - counts[1] for i, q in counts.items()}


def plot_relative(bench: str, base: str, comps: List[str], date_dir: str, path: str,
                  short_labels: bool, **save_args) -> None:
    log_bench = LOG_BENCH.get(bench, bench)
    cfg = get_config(base, comps, False)
    _, _, data = ingest_latest_as_map(base, comps, cfg)
    n_map = data[log_bench]

    fig, ax = plt.subplots(figsize=RELATIVE_SIZE, layout="constrained")
    for i, c in enumerate(comps):
        ns, ratios, cis = [], [], []
        for n in sorted(n_map.keys()):
            r = ratio_with_delta_ci(n_map[n][f"{base}_times"], n_map[n][f"{c}_times"])
            if r and np.isfinite(r[0]):
                ns.append(n); ratios.append(r[0]); cis.append(r[1])
        style = get_plot_style(c, i)
        label = (SHORT_LABEL if short_labels else LABEL)[c]
        ax.errorbar(ns, ratios, yerr=cis, fmt=style["marker"], color=style["color"],
                    markersize=2.5, alpha=0.75, elinewidth=0.6, capsize=1, label=label, zorder=2)

    ax.axhline(1, color="0.3", ls="--", lw=0.8, zorder=3)

    # x: mutant_index（k の昇順に並んでいる）を等間隔に置き、k/N のビン境界に縦線と目盛り
    k = dynamized_counts(date_dir, base, log_bench)
    idx = sorted(n_map.keys())
    big_n = max(k.values())
    assert all(k[a] <= k[b] for a, b in zip(idx, idx[1:])), "mutant_index is not ordered by k"
    def boundary(num: int) -> float:   # 3k < num·N を満たす最後の点と次の点の間
        last = max(i for i in idx if 3 * k[i] < num * big_n)
        return last + 0.5
    b1, b2 = boundary(1), boundary(2)
    for x in (b1, b2):
        ax.axvline(x, **GUIDE)
    ax.set_xlim(idx[0] - 0.5, idx[-1] + 0.5)
    ax.xaxis.set_major_locator(FixedLocator([idx[0], b1, b2, idx[-1]]))
    ax.xaxis.set_minor_locator(NullLocator())
    ax.set_xticklabels(["0", "1/3", "2/3", "1"])
    print(f"[plot_paper] {bench}: N={big_n}, bins k/N<1/3: {int(b1 - idx[0] + 0.5)}, "
          f"<2/3: {int(b2 - b1)}, >=2/3: {int(idx[-1] - b2 + 0.5)} configurations")

    apply_smart_log2_scale(ax)
    ax.yaxis.set_minor_formatter(NullFormatter())

    ax.set_xlabel("Degree of dynamization k/N")
    ax.set_ylabel(f"Slowdown relative to {LABEL[base]}")
    # 7 pt では短縮ラベルでも 3 列 1 行が 2.2 in に収まらない（約 2.4 in）ので 2 列にする
    ax.legend(ncol=2, loc="lower center", bbox_to_anchor=(0.5, 1.0), frameon=False,
              borderaxespad=0.2, handlelength=1.0, handletextpad=0.3, columnspacing=0.8,
              labelspacing=0.2)
    save(fig, path, **save_args)


def main() -> None:
    parser = argparse.ArgumentParser(description="Paper figures for the evaluation section.")
    parser.add_argument("--paper-root", default=os.path.expanduser("~/lsdti-compiler-paper"))
    parser.add_argument("--log-dir", help="log directory (default: latest under logs/, or $BENCH_LOG_DIR)")
    parser.add_argument("--long-relative-labels", action="store_true",
                        help="use the full ablation labels in the relative plots")
    args = parser.parse_args()

    if args.log_dir:
        os.environ["BENCH_LOG_DIR"] = os.path.basename(os.path.normpath(args.log_dir))
    date_dir = latest_date_dir("logs")[1]
    print(f"[plot_paper] using {date_dir}")

    fig_dir = os.path.join(args.paper_root, "figures")
    save_args = dict(paper_root=args.paper_root,
                     backup_root=os.path.join(fig_dir, f"old-{datetime.date.today():%Y-%m-%d}"))

    data = collect(date_dir)
    for bench in RQ12_BENCHES:
        plot_cumulative(data, bench, "typedALHMT", ["typedALHMT", "untypedALHMT"],
                        os.path.join(fig_dir, "supp", f"rq1_{bench}.png"), **save_args)
        plot_cumulative(data, bench, "untypedALHMT", ["untypedALHMT"] + ABLATIONS,
                        os.path.join(fig_dir, "supp", f"rq2_{bench}.png"), **save_args)
    for bench in RQ3_BENCHES:
        plot_cumulative(data, bench, "typedALHMT", ["typedALHMT", "GRIFTCM"],
                        os.path.join(fig_dir, "supp", f"rq3_{bench}.png"), **save_args)
    plot_cumulative(data, "church", "typedALHMT", ["typedALHMT", "untypedALHMT"],
                    os.path.join(fig_dir, "rq1_church_cumulative.png"), **save_args)
    for bench in ("ray", "church"):
        plot_relative(bench, "untypedALHMT", ABLATIONS, date_dir,
                      os.path.join(fig_dir, f"rq2_{bench}_relative.png"),
                      short_labels=not args.long_relative_labels, **save_args)


if __name__ == "__main__":
    main()
