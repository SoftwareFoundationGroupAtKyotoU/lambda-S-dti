# plot_stacked_time.py
#
# 累積性能グラフ（cumulative performance plot）を描く。手法は次の2論文に従う:
#
#   - Takikawa et al., "Is Sound Gradual Typing Dead?" (POPL'16) Fig. 4/5
#   - Kuhlenschmidt et al., "Toward Efficient Gradual Typing for Structural
#     Types via Coercions" (PLDI'19) Fig. 8
#
# 各 configuration（= mutant）の overhead を
#     overhead = mean(times_sec of the mutant) / baseline
# とし、x 軸に overhead、y 軸に「overhead が x 以下の configuration の割合」をとる
# 階段関数をモードごとに1本ずつ描く。左上に急峻に立ち上がる線ほど良い。
#
# モードを2つのグループに分け、グループごとに図と表を作る（GROUPS）。
#   - typed_vs_grift: typedALHMT を基準に、Grift（GRIFT*）と untypedALHMT を比べる
#   - ablation      : untypedALHMT を基準に、軸を1つ反転した untyped* 構成を比べる
# baseline は既定で「グループの基準モードの最も静的な mutant（mutant_index 1、Dyn 化
# スロットなし）」の実行時間。グループ内の全モードで共通の baseline を使うので、線同士を
# 直接比較できる。最大の mutant_index は最も動的な mutant（全スロット Dyn 化）である
# （lib/bench/mutate.ml の all_subsets_by_length / sample_subsets_by_length）。
#
# y 軸は件数ではなく割合（%）にしてある。Takikawa も「全グラフが同じ高さになるよう
# 件数をスケールした」と書いており、typed ソースと untyped ソースのようにモード間で
# mutant 数が異なる場合でも線を重ねて比較できるようにするため。件数は凡例と
# summary.md に出す。
#
# 補助線は Takikawa に揃えて N=3（deliverable の上限, 緑）、M=10（usable の上限, 黄）、
# y=60%（赤破線）。Takikawa の表に相当する統計（static/dynamic 比, 最大・平均 overhead,
# N-deliverable, N/M-usable）は summary.md に書き出す。L-step N/M-usable は
# 性能格子の全列挙が前提なので、mutant をサンプリングしている本リポジトリでは扱わない。
#
# 静的実行（*_fs）のログは各モード1 mutant しかないため累積グラフにならず、対象外。
# 各 mutant の実行時間は benchviz.mean_time（times_sec の平均）で、他のスクリプトと同じ定義。

import argparse
import os
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, NullLocator

from benchviz import (
    latest_date_dir, ensure_dir, save_fig, setup_plot_style, get_plot_style, format_comp_label,
    parse_log_filename, iter_log_records, mean_time,
)

DEFAULT_BASELINE_POINT = "static"   # "static"（mutant 1）| "dynamic"（最大の mutant_index）
DEFAULT_N = 3.0
DEFAULT_M = 10.0
ACCEPTABLE_FRACTION = 60.0          # Takikawa の赤破線（%）
OUTDIR = "cumulative"


@dataclass
class Group:
    name: str
    title: str
    baseline_mode: str

    def includes(self, mode: str) -> bool:
        if self.name == "typed_vs_grift":
            return mode in (self.baseline_mode, "untypedALHMT") or mode.startswith("GRIFT")
        return mode.startswith("untyped") and "STATIC" not in mode

    def order(self, mode: str) -> Tuple[int, str]:
        """基準モードを先頭に、残りは名前順。"""
        return (0 if mode == self.baseline_mode else 1, mode)


GROUPS = [
    Group("typed_vs_grift", "typed vs. Grift / untyped", "typedALHMT"),
    Group("ablation", "untyped vs. ablations", "untypedALHMT"),
]

_OVERHEAD_TICKS = [0.1, 0.2, 0.25, 0.5, 1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000]


@dataclass
class ModeSeries:
    mode: str
    means: Dict[int, float]  # mutant_index -> mean(times_sec)。未計測の mutant は含まない
    max_index: int           # ログに出てきた最大の mutant_index（= 最も動的な mutant）

    @property
    def total(self) -> int:
        return self.max_index

    def endpoint(self, point: str) -> Optional[float]:
        index = 1 if point == "static" else self.max_index
        return self.means.get(index)


# =========================
# ログ読み込み
# =========================

def collect(date_dir: str) -> Dict[str, Dict[str, ModeSeries]]:
    """benchmark -> mode -> series（静的実行ログと計測値のないログは除く）。
    ファイル名の分解・レコード読み込み・実行時間の定義（mean_time）は benchviz と共通。"""
    data: Dict[str, Dict[str, ModeSeries]] = {}
    for fname in sorted(os.listdir(date_dir)):
        parsed = parse_log_filename(fname)
        if parsed is None:
            continue
        mode, bench, is_static = parsed
        if is_static:
            continue
        means: Dict[int, float] = {}
        max_index = 0
        for rec in iter_log_records(os.path.join(date_dir, fname)):
            index = int(rec["mutant_index"])
            max_index = max(max_index, index)
            mean = mean_time(rec.get("times_sec"))
            if mean is not None:
                means[index] = mean
        if not means:
            # times_sec が空（コンパイルのみ）か全部 0（タイマ分解能未満）で overhead 比が定義できない
            print(f"[plot_stacked_time] skip {fname}: no mutant has a positive mean time")
            continue
        data.setdefault(bench, {})[mode] = ModeSeries(mode, means, max_index)
    return data


# =========================
# 指標
# =========================

def overheads(series: ModeSeries, baseline: float) -> np.ndarray:
    return np.sort(np.asarray(list(series.means.values()), dtype=float) / baseline)


def summarize(series: ModeSeries, baseline: float, n: float, m: float) -> Dict[str, Any]:
    """Takikawa Fig. 4/5 の表に相当する統計。平均 overhead は Takikawa に従い
    最も静的 / 最も動的な mutant の両端を除いて計算する（端点しかなければ全体）。"""
    ovh = overheads(series, baseline)
    static, dynamic = series.endpoint("static"), series.endpoint("dynamic")
    inner = [t / baseline for i, t in series.means.items() if i not in (1, series.max_index)]
    count = len(ovh)
    deliverable = int(np.sum(ovh <= n))
    usable = int(np.sum((ovh > n) & (ovh <= m)))
    return {
        "measured": count,
        "total": series.total,
        "static_dynamic_ratio": static / dynamic if static and dynamic else None,
        "max_overhead": float(ovh.max()),
        "mean_overhead": float(np.mean(inner)) if inner else float(ovh.mean()),
        "deliverable": deliverable,
        "usable": usable,
    }




# =========================
# 描画
# =========================

def plot_benchmark(bench: str, title: str, curves: List[Tuple[str, np.ndarray, int]],
                   baseline_label: str, n: float, m: float, out_dir: str) -> None:
    """curves: (mode, 昇順 overhead, その mode の総 mutant 数)"""
    all_ovh = np.concatenate([o for _, o, _ in curves])
    lower = min(float(all_ovh.min()), 1.0) / 1.15
    upper = max(float(all_ovh.max()), m) * 1.15

    fig, ax = plt.subplots(figsize=(8.0, 4.8))
    for i, (mode, ovh, total) in enumerate(curves):
        style = get_plot_style(mode, i)
        xs = np.concatenate(([lower], ovh, [upper]))
        ys = np.concatenate(([0.0], np.arange(1, len(ovh) + 1) / len(ovh) * 100.0, [100.0]))
        ys[-1] = ys[-2]
        missing = f", {total - len(ovh)} unmeasured" if len(ovh) < total else ""
        ax.step(xs, ys, where="post", color=style["color"], linewidth=1.8,
                label=f"{format_comp_label(mode)} (n={len(ovh)}{missing})")

    ax.axvline(1.0, color="black", linewidth=0.8, zorder=0)
    ax.axvline(n, color="#2ca02c", linewidth=1.2, zorder=1.5, label=f"N = {n:g}x")
    ax.axvline(m, color="#e6b800", linewidth=1.2, zorder=1.5, label=f"M = {m:g}x")
    ax.axhline(ACCEPTABLE_FRACTION, color="#d62728", linestyle="--", linewidth=1.0,
               zorder=1.5, label=f"{ACCEPTABLE_FRACTION:g}% of configurations")

    ax.set_xscale("log")
    ax.set_xlim(lower, upper)
    ticks = [t for t in _OVERHEAD_TICKS if lower <= t <= upper]
    ax.xaxis.set_major_locator(FixedLocator(ticks))
    ax.xaxis.set_minor_locator(NullLocator())
    ax.set_xticklabels([f"{t:g}x" for t in ticks])
    ax.set_ylim(0, 100)
    ax.set_yticks([0, 20, 40, 60, 80, 100])
    ax.grid(True, axis="x", which="major", color="#dddddd", linewidth=0.6)
    ax.set_axisbelow(True)

    ax.set_xlabel(f"Overhead relative to {baseline_label} (log scale)")
    ax.set_ylabel("% of configurations with overhead ≤ x")
    ax.set_title(f"{bench}: cumulative performance ({title})")
    ax.legend(loc="lower right", fontsize=8, frameon=True)

    ensure_dir(out_dir)
    save_fig(fig, os.path.join(out_dir, f"{bench}_cumulative.png"))


def _fmt(value: Optional[float]) -> str:
    return "-" if value is None else f"{value:.2f}x"


def write_summary(md, title: str, rows: List[Tuple[str, str, Dict[str, Any]]],
                  baseline_label: str, n: float, m: float) -> None:
    md.write(f"## {title}\n\n")
    md.write(f"- Baseline: {baseline_label}\n\n")
    md.write(f"| benchmark | mode | configs (measured/total) | static/dynamic ratio "
             f"| max overhead | mean overhead | {n:g}-deliverable | {n:g}/{m:g}-usable |\n")
    md.write("|---|---|---:|---:|---:|---:|---:|---:|\n")
    for bench, mode, s in rows:
        k = s["measured"]
        md.write(f"| {bench} | {mode} | {k}/{s['total']} | {_fmt(s['static_dynamic_ratio'])} "
                 f"| {_fmt(s['max_overhead'])} | {_fmt(s['mean_overhead'])} "
                 f"| {s['deliverable']} ({s['deliverable'] / k:.0%}) "
                 f"| {s['usable']} ({s['usable'] / k:.0%}) |\n")
    md.write("\n")


# =========================
# エントリポイント
# =========================

def run_group(data: Dict[str, Dict[str, ModeSeries]], group: Group, point: str,
              n: float, m: float, out_dir: str) -> Tuple[List[Tuple[str, str, Dict[str, Any]]], int]:
    """1 グループ分の図を描き、表の行を返す。基準モードのないベンチは飛ばす。"""
    rows: List[Tuple[str, str, Dict[str, Any]]] = []
    written = 0
    for bench, series_by_mode in sorted(data.items()):
        base_series = series_by_mode.get(group.baseline_mode)
        base = base_series.endpoint(point) if base_series else None
        if base is None:
            print(f"[plot_stacked_time] skip {group.name}/{bench}: baseline "
                  f"({group.baseline_mode}, most {point} mutant) not measured")
            continue
        curves = []
        for mode in sorted((md for md in series_by_mode if group.includes(md)), key=group.order):
            series = series_by_mode[mode]
            curves.append((mode, overheads(series, base), series.total))
            rows.append((bench, mode, summarize(series, base, n, m)))
        plot_benchmark(bench, group.title, curves, baseline_label(group, point), n, m,
                       os.path.join(out_dir, group.name))
        written += 1
    return rows, written


def baseline_label(group: Group, point: str) -> str:
    return f"{format_comp_label(group.baseline_mode)} most {point} mutant"


def run(date_dir: str, point: str = DEFAULT_BASELINE_POINT,
        n: float = DEFAULT_N, m: float = DEFAULT_M) -> int:
    data = collect(date_dir)
    if not data:
        print(f"[plot_stacked_time] no timed (non-static) logs in {date_dir}")
        return 0

    out_dir = os.path.join(date_dir, OUTDIR)
    ensure_dir(out_dir)
    written = 0
    with open(os.path.join(out_dir, "summary.md"), "w", encoding="utf-8") as md:
        md.write("# Cumulative performance summary\n\n")
        md.write(f"- N = {n:g}x (deliverable), M = {m:g}x (usable)\n")
        md.write("- overhead = mean(times_sec) of the mutant / baseline\n")
        md.write("- static/dynamic ratio: most static (mutant 1) / most dynamic mutant of the same mode\n")
        md.write("- mean overhead excludes the most static and most dynamic mutants\n\n")
        for group in GROUPS:
            rows, w = run_group(data, group, point, n, m, out_dir)
            written += w
            if rows:
                write_summary(md, group.title, rows, baseline_label(group, point), n, m)
    print(f"[plot_stacked_time] wrote {written} cumulative plots and summary.md to {out_dir}")
    return written


def main() -> None:
    parser = argparse.ArgumentParser(description="Cumulative performance plots "
                                     "(Takikawa et al. POPL'16 / Kuhlenschmidt et al. PLDI'19).")
    parser.add_argument("--log-dir", help="log directory (default: latest under logs/, or $BENCH_LOG_DIR)")
    parser.add_argument("--baseline-point", choices=("static", "dynamic"), default=DEFAULT_BASELINE_POINT,
                        help="most static (mutant 1, default) or most dynamic (last mutant) "
                             "configuration of each group's baseline mode")
    parser.add_argument("-N", type=float, default=DEFAULT_N, help="deliverable slowdown bound")
    parser.add_argument("-M", type=float, default=DEFAULT_M, help="usable slowdown bound")
    args = parser.parse_args()

    setup_plot_style()
    date_dir = args.log_dir or latest_date_dir("logs")[1]
    print(f"[plot_stacked_time] using {date_dir}")
    run(date_dir, args.baseline_point, args.N, args.M)


if __name__ == "__main__":
    main()

