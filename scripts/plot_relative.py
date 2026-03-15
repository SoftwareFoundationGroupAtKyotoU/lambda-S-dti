# plot_relative.py
import os
import numpy as np
import matplotlib.pyplot as plt
from typing import List, Union
import matplotlib.ticker as ticker

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
    ratio_with_delta_ci, integer_xticks, save_fig, get_plot_style,
    parse_comp_args, draw_binomial_boundaries,
    setup_plot_style, format_comp_label, apply_decorations
)

def apply_smart_log2_scale(ax):
    """
    Y軸を対数スケール（底2）にしつつ、値の幅が狭い場合は
    自動で細かい目盛り（0.9, 1.0, 1.1など）を補完する
    """
    ax.set_yscale('log', base=2)
    ymin, ymax = ax.get_ylim()
    
    # 最大値と最小値の比率が4倍未満（例: 0.8 〜 1.2 など狭い範囲）の場合
    if ymax / ymin < 4:
        ax.yaxis.set_major_locator(ticker.AutoLocator())
    else:
        ax.yaxis.set_major_locator(ticker.LogLocator(base=2))
        
    ax.yaxis.set_major_formatter(ticker.FuncFormatter(lambda y, _: '{:g}'.format(y)))

def plot_relative(base: str, comp: Union[str, List[str]], static: bool):
    setup_plot_style() # ★ 論文用スタイルを適用

    comps, comp_label, fs, is_multi = parse_comp_args(comp, static)
    if not comps: return
    
    cfg = load_config(base, comps, static)
    latest, date_dir, data = ingest_latest_as_map(base, comps, cfg)
    rcfg = cfg["relative"]
    out_dir = os.path.join(date_dir, rcfg["outdir"])
    ensure_dir(out_dir)

    for bench, n_map in data.items():
        valid_data = {}
        for c in comps:
            ns, ratios, cis = [], [], []
            for n in sorted(n_map.keys()):
                r = ratio_with_delta_ci(n_map[n][f"{base}_times"], n_map[n][f"{c}_times"])
                if r and np.isfinite(r[0]):
                    ns.append(n); ratios.append(r[0]); cis.append(r[1])
            if ns:
                valid_data[c] = {'ns': ns, 'ratios': ratios, 'cis': cis}

        if not valid_data: continue

        base_formatted = format_comp_label(base)

        # ==========================================
        # === zigzag版 ===
        # ==========================================
        all_ticks = set().union(*(d['ns'] for d in valid_data.values()))
        fig, ax = plt.subplots(figsize=(9, 4.8)) # ★ 縦を少し短く
        
        ax.axhline(1, color='gray', linestyle='--', label=f'Baseline ({base_formatted})')

        for i, c in enumerate(comps):
            if c not in valid_data: continue
            d = valid_data[c]
            style = get_plot_style(c, i)
            label_str = format_comp_label(c) # ★ ラベル変換
            ax.errorbar(d['ns'], d['ratios'], yerr=d['cis'], fmt=style["marker"], color=style["color"], 
                        capsize=5, label=label_str)
        
        integer_xticks(ax, list(all_ticks))
        
        apply_smart_log2_scale(ax) # ★ 賢い対数スケールを適用
        draw_binomial_boundaries(ax, len(n_map)) # ★ zigzag版には縦線を引く

        apply_decorations(ax, rcfg["xlabel"], rcfg["ylabel"], f'{rcfg["title_prefix"]}: {bench}')
        
        save_fig(fig, os.path.join(out_dir, f'plot_{bench}_{base}-{comp_label}_relative_zigzag{fs}.png'))

        # ==========================================
        # === ソート版 ===
        # ==========================================
        if not is_multi:
            c = comps[0]
            d = valid_data[c]
            style = get_plot_style(c, 0)
            bundle = sorted(zip(d['ns'], d['ratios'], d['cis'], strict=False), key=lambda x: x[1])
            xs = list(range(1, len(bundle) + 1))
            ys = [b[1] for b in bundle]; ycis = [b[2] for b in bundle]

            fig, ax = plt.subplots(figsize=(10, 4.8))
            
            label_str = format_comp_label(c)
            ax.errorbar(xs, ys, yerr=ycis, fmt=style["marker"], color=style["color"], capsize=3, 
                        label=label_str)
            ax.axhline(1, color='gray', linestyle='--', label=f'Baseline ({base_formatted})')
            
            integer_xticks(ax, xs)
            
            apply_smart_log2_scale(ax) # ★ ソート版にも適用
            # ★ ソート版には draw_binomial_boundaries を呼ばない

            apply_decorations(ax, rcfg["xlabel"] + " (filtered & sorted)", rcfg["ylabel"], 
                          f'{rcfg["title_prefix"]} (filtered & sorted): {bench}')
            
            save_fig(fig, os.path.join(out_dir, f'plot_{bench}_{base}-{comp_label}_relative_sorted{fs}.png'))

    print(f"Saved relative plots under: {out_dir}")