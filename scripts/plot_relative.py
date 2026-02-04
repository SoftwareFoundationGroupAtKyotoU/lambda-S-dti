import os
import math
import numpy as np
import matplotlib.pyplot as plt

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
    ratio_with_delta_ci, integer_xticks, save_fig,
)

def _binomial_boundaries_between(n_total: int):
    """
    n_total が 2^n と仮定し、"区切りの縦線" を入れる位置を返す。
    例) n=3, 累積 = [1,4,7,8] -> 線は [1.5, 4.5, 7.5]
    """
    if n_total <= 0:
        return []
    n = round(math.log2(n_total))
    if (1 << n) != n_total:
        n = int(math.log2(max(1, n_total)))
    cum = 0
    mids = []
    for k in range(n + 1):
        cum += math.comb(n, k)
        if cum < (1 << n):        # 最後(2^n)は除外
            mids.append(cum + 0.5)
    return mids

def plot_relative(base: str, comp: str, static: bool):
    fs = ""
    if static:
        fs = "_fs"
    cfg = load_config(base, comp, static)
    latest, date_dir, data = ingest_latest_as_map(base, comp, cfg)
    rcfg = cfg["relative"]

    out_dir = os.path.join(date_dir, rcfg["outdir"])
    ensure_dir(out_dir)

    for bench, n_map in data.items():
        ns, ratios, cis = [], [], []
        for n in sorted(n_map.keys()):
            slot = n_map[n]
            r = ratio_with_delta_ci(slot[f"{base}_times"], slot[f"{comp}_times"])
            if r is None:
                continue
            ratio, ci, *_ = r
            if not np.isfinite(ratio):
                continue
            ns.append(n); ratios.append(ratio); cis.append(ci)

        if not ns:
            continue

        # === zigzag版（区切り線は半端位置に） ===
        n_total = len(n_map)  # 2^n が保証されている
        midlines = _binomial_boundaries_between(n_total)

        fig, ax = plt.subplots(figsize=(8, 6))
        ax.errorbar(ns, ratios, yerr=cis, fmt='d', capsize=5, markersize=3,
                    label=f'{comp}/{base} Ratio (95% CI)')
        ax.axhline(1, color='gray', linestyle='--', label=f'{base} = 1 Baseline')

        # 目盛はデータ点のみ(整数)、描画範囲は [0.5, 2^n+0.5]
        integer_xticks(ax, ns)
        ax.set_xlim(0.5, n_total + 0.5)

        # 区切りの縦線（最後の 2^n+0.5 は描かない）
        for x in midlines:
            ax.axvline(x=x, color='lightgray', linestyle=':', linewidth=0.9, zorder=0)

        ax.set_xlabel(rcfg["xlabel"]); ax.set_ylabel(rcfg["ylabel"])
        ax.set_title(f'{rcfg["title_prefix"]}: {bench} ({comp} relative to {base})')
        ax.grid(True, axis='y', linestyle='--', alpha=0.35); ax.legend()
        save_fig(fig, os.path.join(out_dir, f'plot_{bench}_{base}-{comp}_relative_zigzag{fs}.png'))

        # 2) 比の昇順並べ替え
        bundle = sorted(zip(ns, ratios, cis), key=lambda x: x[1])
        xs = list(range(1, len(bundle) + 1))
        ys = [b[1] for b in bundle]; ycis = [b[2] for b in bundle]

        fig, ax = plt.subplots(figsize=(11, 6))
        ax.errorbar(xs, ys, yerr=ycis, fmt='d', capsize=3, markersize=2, rasterized=True,
                    label=f'{comp}/{base} Ratio (95% CI)')
        ax.axhline(1, color='gray', linestyle='--', label=f'{base} = 1 Baseline')
        integer_xticks(ax, xs)
        ax.set_xlabel(rcfg["xlabel"] + " (filtered & sorted)")
        ax.set_ylabel(rcfg["ylabel"])
        ax.set_title(f'{rcfg["title_prefix"]} (filtered & sorted): {bench}')
        ax.legend(); ax.grid(True, axis='y', alpha=0.3)
        save_fig(fig, os.path.join(out_dir, f'plot_{bench}_{base}-{comp}_relative_sorted{fs}.png'))

    print(f"Saved relative plots under: {out_dir}")
    print(f"Done: {comp} vs {base}")