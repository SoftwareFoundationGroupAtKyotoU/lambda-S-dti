# plot_metric.py
import os
import matplotlib.pyplot as plt
from typing import List, Union

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir, get_plot_style,
    parse_comp_args, integer_xticks, save_fig, draw_binomial_boundaries,
    setup_plot_style, format_comp_label, apply_decorations
)

def plot_metric(base: str, comp: Union[str, List[str]], static: bool, metric_name: str, metric_label: str = None):
    setup_plot_style() # ★ 論文用スタイルを適用

    comps, comp_label, fs, is_multi = parse_comp_args(comp, static)
    if not comps: return
    if metric_label is None: metric_label = metric_name

    cfg = load_config(base, comps, static)
    latest, date_dir, data = ingest_latest_as_map(base, comps, cfg, extra_metrics=[metric_name])
    out_dir = os.path.join(date_dir, "metrics", metric_name)
    ensure_dir(out_dir)

    for bench, n_map in data.items():
        base_data, comp_data = {}, {c: {} for c in comps}
        all_ns = set()

        for n in sorted(n_map.keys()):
            slot = n_map[n]
            if (b_val := slot.get(f"{base}_{metric_name}")) is not None:
                base_data[n] = float(b_val)
                all_ns.add(n)
            for c in comps:
                if (c_val := slot.get(f"{c}_{metric_name}")) is not None:
                    comp_data[c][n] = float(c_val)
                    all_ns.add(n)

        if not base_data and all(not d for d in comp_data.values()):
            continue

        fig, ax = plt.subplots(figsize=(9, 4.8)) # ★ 横長サイズに変更

        base_formatted = format_comp_label(base)

        # Base描画
        if base_data:
            b_ns = sorted(base_data.keys())
            b_vals = [base_data[n] for n in b_ns]
            style = get_plot_style(base, -1)
            ax.plot(b_ns, b_vals, marker=style["marker"], color=style["color"], 
                    linestyle='', alpha=0.7, label=f'Baseline ({base_formatted})')

        # Comps描画
        for i, c in enumerate(comps):
            if not comp_data[c]: continue
            c_ns = sorted(comp_data[c].keys())
            c_vals = [comp_data[c][n] for n in c_ns]
            style = get_plot_style(c, i)
            label_str = format_comp_label(c) # ★ ラベル変換
            ax.plot(c_ns, c_vals, marker=style["marker"], color=style["color"], 
                    linestyle='', alpha=0.8, label=label_str)

        # 軸・装飾
        integer_xticks(ax, list(all_ns))
        draw_binomial_boundaries(ax, len(n_map))

        apply_decorations(ax, "Pattern for Replacing Type Variables with Dyn (n)", 
                          metric_label, f'{metric_label}: {bench}')
        
        ax.grid(True, axis='y', linestyle='--', alpha=0.35)
        
        save_path = os.path.join(out_dir, f'plot_{bench}_{base}-{comp_label}_{metric_name}{fs}.png')
        save_fig(fig, save_path)

    print(f"Saved {metric_name} plots under: {out_dir}")