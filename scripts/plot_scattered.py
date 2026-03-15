# plot_scattered.py
import os
import numpy as np
import matplotlib.pyplot as plt
from typing import List, Union
from scipy import stats

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir, get_plot_style,
    parse_comp_args, integer_xticks, save_fig, draw_binomial_boundaries,
    setup_plot_style, format_comp_label, apply_decorations
)

def plot_scattered(base: str, comp: Union[str, List[str]], static: bool):
    setup_plot_style() # ★ 論文用スタイルを適用

    comps, comp_label, fs, is_multi = parse_comp_args(comp, static)
    if not comps: return
    
    cfg = load_config(base, comps, static)
    latest, date_dir, data = ingest_latest_as_map(base, comps, cfg)
    scfg = cfg["scattered"]
    out_dir = os.path.join(date_dir, scfg["outdir"])
    ensure_dir(out_dir)

    for bench, n_map in data.items():
        base_data, comp_data = {}, {c: {} for c in comps}
        all_ns = set()

        for n in sorted(n_map.keys()):
            slot = n_map[n]
            # Base
            if (b_times := slot.get(f"{base}_times")):
                arr = np.asarray(b_times, dtype=float)
                ci = float(stats.sem(arr) * stats.t.ppf(0.975, len(arr)-1)) if len(arr) > 1 else 0.0
                base_data[n] = (float(np.mean(arr)), ci)
                all_ns.add(n)
            # Comps
            for c in comps:
                if (c_times := slot.get(f"{c}_times")):
                    arr = np.asarray(c_times, dtype=float)
                    ci = float(stats.sem(arr) * stats.t.ppf(0.975, len(arr)-1)) if len(arr) > 1 else 0.0
                    comp_data[c][n] = (float(np.mean(arr)), ci)
                    all_ns.add(n)

        if not base_data and all(not d for d in comp_data.values()): continue

        fig, ax = plt.subplots(figsize=(9, 4.8)) # ★ 横長サイズに変更

        base_formatted = format_comp_label(base)

        # Base描画
        if base_data:
            b_ns = sorted(base_data.keys())
            style = get_plot_style(base, -1)
            ax.errorbar(b_ns, [base_data[n][0] for n in b_ns], yerr=[base_data[n][1] for n in b_ns], 
                        fmt=style["marker"], color=style["color"], capsize=5, markersize=5, 
                        alpha=0.7, label=f'Baseline ({base_formatted})')

        # Comps描画
        for i, c in enumerate(comps):
            if not comp_data[c]: continue
            c_ns = sorted(comp_data[c].keys())
            style = get_plot_style(c, i)
            label_str = format_comp_label(c) # ★ ラベル変換
            ax.errorbar(c_ns, [comp_data[c][n][0] for n in c_ns], yerr=[comp_data[c][n][1] for n in c_ns], 
                        fmt=style["marker"], color=style["color"], capsize=5, markersize=5, 
                        alpha=0.8, label=label_str)

        # 軸・装飾
        integer_xticks(ax, list(all_ns))
        draw_binomial_boundaries(ax, len(n_map))

        ax.set_ylim(bottom=0)
        apply_decorations(ax, scfg["xlabel"], scfg["ylabel"], 
                          f'{scfg["title_prefix"]}: {bench} with 95% Confidence Interval')
                  
        ax.grid(True, axis='y', linestyle='--', alpha=0.35)
        
        save_path = os.path.join(out_dir, f'plot_{bench}_{base}-{comp_label}_confidence{fs}.png')
        save_fig(fig, save_path)

    print(f"Saved scatter plots under: {out_dir}")