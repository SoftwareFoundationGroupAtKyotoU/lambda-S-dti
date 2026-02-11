# plot_metric.py
import os
import matplotlib.pyplot as plt
from typing import List, Dict, Any, Union

from matplotlib.ticker import FixedLocator

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir
)

def plot_metric(base: str, comp: Union[str, List[str]], static: bool, metric_name: str, metric_label: str = None):
    """
    指定されたメトリクス（metric_name: jsonのキー）をプロットする。
    信頼区間は計算せず、生の値をプロットする。
    値は (mutant毎に) 定数であることを想定している。
    """
    if static:
        fs = "_fs"
    else:
        fs = ""

    # comp がリストの場合は "|" で結合してラベル化
    if isinstance(comp, list):
        # ["ALC", "SLC"] -> "ALC|SLC"
        comp_pattern = "|".join(comp)
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

    if metric_label is None:
        metric_label = metric_name

    # 1. データを読み込む (extra_metrics に metric_name を指定)
    cfg = load_config(base, comps, static)
    latest, date_dir, data = ingest_latest_as_map(base, comps, cfg, extra_metrics=[metric_name])

    # 出力ディレクトリ: logs/YYYY.../metrics/<metric_name>/
    out_dir = os.path.join(date_dir, "metrics", metric_name)
    ensure_dir(out_dir)

    markers = ['s', '^', 'd', 'v', '<', '>', 'p', '*']

    for bench, n_map in data.items():
        # プロット用データの収集
        # Base: {n: val}
        # Comp: {c: {n: val}}
        base_data = {}
        comp_data = {c: {} for c in comps}
        all_ns = set()

        for n in sorted(n_map.keys()):
            slot = n_map[n]
            
            # --- Base のデータ ---
            # キーは f"{base}_{metric_name}"
            b_val = slot.get(f"{base}_{metric_name}")
            if b_val is not None:
                base_data[n] = float(b_val)
                all_ns.add(n)

            # --- Comp のデータ ---
            for c in comps:
                c_val = slot.get(f"{c}_{metric_name}")
                if c_val is not None:
                    comp_data[c][n] = float(c_val)
                    all_ns.add(n)

        # データが全くなければスキップ
        if not base_data and all(not d for d in comp_data.values()):
            continue

        # --- プロット ---
        fig, ax = plt.subplots(figsize=(8, 6))

        # Base (常に黒丸)
        b_ns = sorted(base_data.keys())
        if b_ns:
            b_vals = [base_data[n] for n in b_ns]
            ax.plot(b_ns, b_vals, 'o', color='black', alpha=0.7, label=f'{base} (Base)')

        # Comps
        for i, c in enumerate(comps):
            c_dict = comp_data[c]
            c_ns = sorted(c_dict.keys())
            if not c_ns:
                continue
            
            c_vals = [c_dict[n] for n in c_ns]
            marker = markers[i % len(markers)]
            
            ax.plot(c_ns, c_vals, marker=marker, linestyle='', alpha=0.8, label=str(c))

        # 軸設定
        ticks = sorted(list(all_ns))
        if ticks:
            if FixedLocator:
                ax.xaxis.set_major_locator(FixedLocator(ticks))
            ax.set_xlim(min(ticks) - 0.5, max(ticks) + 0.5)
        
        ax.set_xticklabels([])
        ax.tick_params(axis='x', length=0)

        ax.set_xlabel("Pattern for Replacing Type Variables with Dyn (n)")
        ax.set_ylabel(metric_label)
        ax.set_title(f'{metric_label}: {bench}')
        ax.legend()
        ax.grid(True, axis='y', linestyle='--', alpha=0.35)
        
        fig.tight_layout()
        save_path = os.path.join(out_dir, f'plot_{bench}_{base}-{comp_label}_{metric_name}{fs}.png')
        fig.savefig(save_path, dpi=150)
        plt.close(fig)

    print(f"Saved {metric_name} plots under: {out_dir}")