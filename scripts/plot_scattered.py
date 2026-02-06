# plot_scattered.py
import os
import numpy as np
import matplotlib.pyplot as plt
from typing import List, Dict, Any, Union

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
)

from matplotlib.ticker import FixedLocator

def plot_scattered(base: str, comp: Union[str, List[str]], static: bool):
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
    scfg = cfg["scattered"]

    out_dir = os.path.join(date_dir, scfg["outdir"])
    ensure_dir(out_dir)

    from scipy import stats

    markers = ['s', '^', 'd', 'v', '<', '>', 'p', '*']

    for bench, n_map in data.items():
        # プロット用データの収集
        # base_data: {n: (mean, ci)}
        # comp_data: {c: {n: (mean, ci)}}
        base_data = {}
        comp_data = {c: {} for c in comps}
        all_ns = set()

        for n in sorted(n_map.keys()):
            slot = n_map[n]
            
            # --- Base のデータ ---
            b_times = slot.get(f"{base}_times", [])
            if b_times:
                b_arr = np.asarray(b_times, dtype=float)
                if len(b_arr) > 0:
                    b_mean = float(np.mean(b_arr))
                    if len(b_arr) > 1:
                        b_sem = float(stats.sem(b_arr))
                        t_base = float(stats.t.ppf(0.975, len(b_arr)-1))
                        b_ci = b_sem * t_base
                    else:
                        b_ci = 0.0
                    base_data[n] = (b_mean, b_ci)
                    all_ns.add(n)

            # --- Comp のデータ (各 c について) ---
            for c in comps:
                c_times = slot.get(f"{c}_times", [])
                if c_times:
                    c_arr = np.asarray(c_times, dtype=float)
                    if len(c_arr) > 0:
                        c_mean = float(np.mean(c_arr))
                        if len(c_arr) > 1:
                            c_sem = float(stats.sem(c_arr))
                            t_comp = float(stats.t.ppf(0.975, len(c_arr)-1))
                            c_ci = c_sem * t_comp
                        else:
                            c_ci = 0.0
                        comp_data[c][n] = (c_mean, c_ci)
                        all_ns.add(n)

        # データが全くなければスキップ
        if not base_data and all(not d for d in comp_data.values()):
            continue

        # --- 3. プロット ---
        fig, ax = plt.subplots(figsize=(8, 6))

        # Base の描画 (常に黒丸)
        b_ns = sorted(base_data.keys())
        if b_ns:
            b_means = [base_data[n][0] for n in b_ns]
            b_cis = [base_data[n][1] for n in b_ns]
            ax.errorbar(b_ns, b_means, yerr=b_cis, fmt='o', color='black',
                        capsize=5, markersize=4, alpha=0.7, 
                        label=f'{base} (Base)')

        # Comps の描画
        for i, c in enumerate(comps):
            c_dict = comp_data[c]
            c_ns = sorted(c_dict.keys())
            if not c_ns:
                continue
            
            c_means = [c_dict[n][0] for n in c_ns]
            c_cis = [c_dict[n][1] for n in c_ns]
            marker = markers[i % len(markers)]
            
            # 凡例ラベル
            label_str = f'{c}'
            if not is_multi:
                label_str += ' mode (95% CI)'
            
            ax.errorbar(c_ns, c_means, yerr=c_cis, fmt=marker,
                        capsize=5, markersize=4, alpha=0.8,
                        label=label_str)

        ticks = sorted(list(all_ns))
        if ticks:
            ax.xaxis.set_major_locator(FixedLocator(ticks))
            ax.set_xlim(min(ticks) - 0.5, max(ticks) + 0.5)
        ax.set_xticklabels([])
        ax.set_xlabel(scfg["xlabel"]); ax.set_ylabel(scfg["ylabel"])
        ax.set_title(f'{scfg["title_prefix"]}: {bench} with 95% Confidence Interval')
        ax.legend()
        ax.xaxis.set_major_locator(FixedLocator(ticks))
        ax.set_xlim(min(ticks) - 0.5, max(ticks) + 0.5)
        ax.set_xticklabels([]); ax.tick_params(axis='x', length=0)
        ax.grid(True, axis='y', linestyle='--', alpha=0.35)
        fig.tight_layout()
        fig.savefig(os.path.join(out_dir, f'plot_{bench}_{base}-{comp_label}_confidence{fs}.png'), dpi=150)
        plt.close(fig)

    print(f"Saved scatter plots under: {out_dir}")
    print(f"Done: {comp_label} vs {base}")