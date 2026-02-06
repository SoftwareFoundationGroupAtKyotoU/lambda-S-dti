import os
import math
import numpy as np
import matplotlib.pyplot as plt
from typing import List, Dict, Any, Union

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

def plot_relative(base: str, comp: Union[str, List[str]], static: bool):
    if static:
        fs = "_fs"
    else :
        fs = ""

    # comp がリストの場合は "|" で結合して正規表現を作る
    if isinstance(comp, list):
        # ["ALC", "SLC"] -> "ALC|SLC"
        comp_pattern = "|".join(comp)
        # ラベル等が長くなりすぎないように調整（必要であれば）
        comp_label = "|".join(comp) 
        comps = comp
        is_multi = True
    else:
        comp_pattern = comp
        comp_label = comp
        comps = [comp]
        is_multi = False
    if not comps:
        return
    
    cfg = load_config(base, comps, static)
    latest, date_dir, data = ingest_latest_as_map(base, comps, cfg)
    rcfg = cfg["relative"]

    out_dir = os.path.join(date_dir, rcfg["outdir"])
    ensure_dir(out_dir)

    markers = ['d', 'o', '^', 's', 'v', 'X', 'P', '*']

    for bench, n_map in data.items():
        valid_data = {}
        for c in comps:
            ns, ratios, cis = [], [], []
            for n in sorted(n_map.keys()):
                slot = n_map[n]
                r = ratio_with_delta_ci(slot[f"{base}_times"], slot[f"{c}_times"])
                if r is None:
                    continue
                ratio, ci, *_ = r
                if not np.isfinite(ratio):
                    continue
                ns.append(n); ratios.append(ratio); cis.append(ci)

            if ns:
                valid_data[c] = {'ns': ns, 'ratios': ratios, 'cis': cis}

        if not valid_data:
            continue

        # === zigzag版（区切り線は半端位置に） ===
        n_total = len(n_map)  # 2^n が保証されている
        midlines = _binomial_boundaries_between(n_total)
        all_ticks = set()
        for d in valid_data.values():
            all_ticks.update(d['ns'])

        fig, ax = plt.subplots(figsize=(8, 6))
        ax.axhline(1, color='gray', linestyle='--', label=f'{base} = 1 Baseline')

        for i, c in enumerate(comps):
            if c not in valid_data:
                continue
            d = valid_data[c]
            marker = markers[i % len(markers)]

            ax.errorbar(d['ns'], d['ratios'], yerr=d['cis'], fmt=marker, capsize=5, markersize=3,
                    label=f'{c}/{base} Ratio (95% CI)')
        
        # 目盛はデータ点のみ(整数)、描画範囲は [0.5, 2^n+0.5]
        if all_ticks:
            integer_xticks(ax, list(all_ticks))
        ax.set_xlim(0.5, n_total + 0.5)

        # 区切りの縦線（最後の 2^n+0.5 は描かない）
        for x in midlines:
            ax.axvline(x=x, color='lightgray', linestyle=':', linewidth=0.9, zorder=0)

        ax.set_xlabel(rcfg["xlabel"]); ax.set_ylabel(rcfg["ylabel"])
        ax.set_title(f'{rcfg["title_prefix"]}: {bench} ({comp_label} relative to {base})')
        ax.grid(True, axis='y', linestyle='--', alpha=0.35); ax.legend()
        save_fig(fig, os.path.join(out_dir, f'plot_{bench}_{base}-{comp_label}_relative_zigzag{fs}.png'))

        # 2) 比の昇順並べ替え
        if not is_multi:
            c = comps[0]
            d = valid_data[c]
            bundle = sorted(zip(ns, ratios, cis), key=lambda x: x[1])
            xs = list(range(1, len(bundle) + 1))
            ys = [b[1] for b in bundle]; ycis = [b[2] for b in bundle]

            fig, ax = plt.subplots(figsize=(11, 6))
            ax.errorbar(xs, ys, yerr=ycis, fmt='d', capsize=3, markersize=2, rasterized=True,
                        label=f'{comp_label}/{base} Ratio (95% CI)')
            ax.axhline(1, color='gray', linestyle='--', label=f'{base} = 1 Baseline')
            integer_xticks(ax, xs)
            ax.set_xlabel(rcfg["xlabel"] + " (filtered & sorted)")
            ax.set_ylabel(rcfg["ylabel"])
            ax.set_title(f'{rcfg["title_prefix"]} (filtered & sorted): {bench}')
            ax.legend(); ax.grid(True, axis='y', alpha=0.3)
            save_fig(fig, os.path.join(out_dir, f'plot_{bench}_{base}-{comp_label}_relative_sorted{fs}.png'))

    print(f"Saved relative plots under: {out_dir}")
    print(f"Done: {comp_label} vs {base}")