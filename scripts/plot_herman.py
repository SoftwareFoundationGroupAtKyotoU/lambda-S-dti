# plot_herman.py
import os
import math
import numpy as np
import matplotlib.pyplot as plt
from typing import List, Dict, Any, Union

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
    ratio_with_delta_ci, integer_xticks, save_fig, robust_left_outliers_log10,
)

def _get_promoted_bytes(slot, mode):
    return slot.get(f"{mode}_promoted_bytes")

def _binomial_boundaries_between(n_total: int):
    """
    n_total が 2^n と仮定し、"区切りの縦線" を入れる半端位置を返す。
    例) n=3, 累積 = [1,4,7,8] -> 線は [1.5, 4.5, 7.5]
    """
    if n_total <= 0:
        return []
    n = round(math.log2(n_total))
    if (1 << n) != n_total:
        # 念のためズレている場合は floor に寄せる
        n = int(math.log2(max(1, n_total)))
    cum = 0
    mids = []
    for k in range(n + 1):
        cum += math.comb(n, k)
        if cum < (1 << n):        # 最後(2^n)は除外
            mids.append(cum + 0.5)
    return mids

def plot_herman(base: str, comp: Union[str, List[str]], static: bool):
    if static:
        fs = "_fs"
    else:
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
    hcfg = cfg.get("herman", {})
    outdir = hcfg.get("outdir", "herman")
    k = float(hcfg.get("mad_k", 3.5))
    min_n = int(hcfg.get("min_n", 8))

    xlabel = hcfg.get("xlabel", "Pattern for Replacing Type Variables with Dyn (n)")
    ylabel = hcfg.get("ylabel", f"Relative Execution Time ({comp_label} / {base})")
    title_prefix = hcfg.get("title_prefix", "Herman (robust)")

    root = os.path.join(date_dir, outdir)
    ensure_dir(root)

    markers = ['d', 'o', '^', 's', 'v', 'X', 'P', '*']

    for bench, n_map in data.items():
        # このベンチマークにおける、有効な comp データを集める
        # valid_data[comp_name] = { 'ns': ..., 'ratios': ... }
        valid_data = {}

        for c in comps:
            # 1) c/base promoted BYTES の比を集める
            ns, ratios_pb = [], []
            for n in sorted(n_map.keys()):
                slot = n_map[n]
                base_pb = _get_promoted_bytes(slot, base)
                comp_pb = _get_promoted_bytes(slot, c)
                if base_pb is None or comp_pb is None or not np.isfinite(base_pb) or base_pb <= 0:
                    continue
                ns.append(n)
                ratios_pb.append(float(comp_pb) / float(base_pb))

            if not ns:
                continue

            # 2) ロバスト検出（左側の外れ値：comp/base promoted bytes が極端に小さい）
            idxs, stats = robust_left_outliers_log10(ratios_pb, k=k, min_n=min_n)
            if not idxs:
                continue

            # 3) 描画用の comp/base 時間比（外れ値だけ）
            filt_ns, filt_ratio, filt_ci = [], [], []
            for i in idxs:
                n = ns[i]
                rr = ratio_with_delta_ci(n_map[n][f"{base}_times"], n_map[n][f"{c}_times"])
                if rr is None:
                    continue
                r, ci, *_ = rr
                if not np.isfinite(r):
                    continue
                filt_ns.append(n); filt_ratio.append(r); filt_ci.append(ci)

            if filt_ns:
                valid_data[c] = {
                    'ns': filt_ns, 'ratios': filt_ratio, 'cis': filt_ci,
                    'stats': stats, 'n_total': len(n_map)
                }
        
        # プロットすべきデータが無ければスキップ
        if not valid_data:
            continue

        bench_dir = os.path.join(root, bench)
        ensure_dir(bench_dir)

        # --- 区切り線の位置 ---
        n_total = max(d['n_total'] for d in valid_data.values())  # このベンチの総ミュータント数（2^n が保証されている想定）
        midlines = _binomial_boundaries_between(n_total)
        all_ticks = set()
        for d in valid_data.values():
            all_ticks.update(d['ns'])

        # (1) zigzag（縦線でグループ境界を示す）
        fig, ax = plt.subplots(figsize=(8, 6))
        ax.axhline(1, color='gray', linestyle='--', label=f'{base} = 1 Baseline')
        for i, c in enumerate(comps):
            if c not in valid_data:
                continue
            d = valid_data[c]
            marker = markers[i % len(markers)]

            label_str = f'{c}/{base} Ratio (95% CI)'

            ax.errorbar(d['ns'], d['ratios'], yerr=d['cis'], fmt=marker,
                    capsize=5, markersize=3, label=label_str)
            s = valid_data[c]['stats']
        
        if all_ticks:
            integer_xticks(ax, list(all_ticks))   # 目盛はデータ点（整数）のみに
        ax.set_xlim(0.5, n_total + 0.5)  # 全体範囲を 0.5〜2^n+0.5 に固定

        # 区切りの縦線
        for x in midlines:
            ax.axvline(x=x, color='lightgray', linestyle=':', linewidth=0.9, zorder=0)

        ax.set_title(f'{title_prefix}: {bench}')
        ax.set_xlabel(xlabel); ax.set_ylabel(ylabel)
        method = stats.get('method', 'mad')
        ax.grid(True, axis='y', linestyle='--', alpha=0.35); ax.legend()
        save_fig(fig, os.path.join(bench_dir, f'plot_{bench}_herman_zigzag{fs}.png'))

        # (2) 昇順ソート
        if not is_multi:
            c = comps[0]
            d = valid_data[c]
            bundle = sorted(zip(filt_ns, filt_ratio, filt_ci), key=lambda x: x[1])
            xs = list(range(1, len(bundle) + 1))
            ys = [b[1] for b in bundle]; ycis = [b[2] for b in bundle]
            fig, ax = plt.subplots(figsize=(11, 6))
            ax.errorbar(xs, ys, yerr=ycis, fmt='d',
                        capsize=3, markersize=2, rasterized=True, label=f'{comp_label}/{bench} Ratio (95% CI)')
            ax.axhline(1, color='gray', linestyle='--', label=f'{base} = 1 Baseline')
            ax.set_xlim(0.5, len(xs) + 0.5); ax.set_xticks([])
            ax.set_xlabel(xlabel + " (filtered & sorted)"); ax.set_ylabel(ylabel)
            ax.set_title(f'{title_prefix} (sorted): {bench}')
            ax.legend(); ax.grid(True, axis='y', alpha=0.3)
            save_fig(fig, os.path.join(bench_dir, f'plot_{bench}_{base}-{comp_label}_herman_sorted{fs}.png'))

    print(f"Saved robust Herman plots under: {root}")
    print(f"Done: {comp_label} vs {base}")