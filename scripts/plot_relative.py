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

STATIC_BENCHMARK_ORDER = [
    "evenodd", "fib", "incsum", "loop_mono", "map_mono", 
    "tak", "loop", "map", "church_65532"
]

def plot_static_summary(base: str, comp: Union[str, List[str]]):
    """Fully-static プログラムのパフォーマンスを全ベンチマーク統合してプロットする"""
    
    # 1. 論文用フォント・スタイルの適用
    setup_plot_style()
    
    static = True
    
    # 2. 引数のパース（リスト化やラベル生成）の共通化
    comps, comp_label, fs, is_multi = parse_comp_args(comp, static)
    if not comps: return
    
    cfg = load_config(base, comps, static)
    latest, date_dir, data = ingest_latest_as_map(base, comps, cfg)
    rcfg = cfg["relative"]
    
    out_dir = os.path.join(date_dir, "static_summary")
    ensure_dir(out_dir)

    valid_benches = []
    plot_data = {c: {'ratios': [], 'cis': []} for c in comps}

    for bench in STATIC_BENCHMARK_ORDER:
        if bench not in data:
            continue
            
        n_keys = list(data[bench].keys())
        if not n_keys: continue
        n = n_keys[0] 
        slot = data[bench][n]

        b_times = slot.get(f"{base}_times", [])
        if not b_times: continue

        valid = True  # 最初をTrueにしておく
        temp_ratios = {}
        temp_cis = {}
        for c in comps:
            c_times = slot.get(f"{c}_times", [])
            r = ratio_with_delta_ci(b_times, c_times)
            if r and np.isfinite(r[0]):
                temp_ratios[c] = r[0]
                temp_cis[c] = r[1]
            else:
                valid = False  # どれか一つでも欠けていればFalseにして抜ける
                break
                
        if valid:
            valid_benches.append(bench)
            for c in comps:
                plot_data[c]['ratios'].append(temp_ratios[c])
                plot_data[c]['cis'].append(temp_cis[c])

    if not valid_benches:
        return

    # === プロット生成 ===
    fig, ax = plt.subplots(figsize=(11, 5)) 
    
    # 3. ラベル名の自動変換 (SLHC -> Id-Opt: ON...) の活用
    base_formatted = format_comp_label(base)
    ax.axhline(1, color='gray', linestyle='--', label=f'Baseline ({base_formatted})')

    xs = np.arange(len(valid_benches))
    
    # 重なり防止のジッター（ずらし）
    offset_step = 0.15 
    start_offset = - (offset_step * (len(comps) - 1)) / 2

    for i, c in enumerate(comps):
        ratios = np.array(plot_data[c]['ratios'])
        cis = np.array(plot_data[c]['cis'])
        style = get_plot_style(c, i)
        
        # 3. ラベル名の自動変換 の活用（Comp側）
        label_str = format_comp_label(c)
        
        current_xs = xs + start_offset + (i * offset_step)
        
        # エラーバーを太く・大きく
        ax.errorbar(current_xs, ratios, yerr=cis, fmt=style["marker"], color=style["color"],
                    capsize=6, elinewidth=2.5, capthick=2.5, markersize=8,
                    linestyle='', label=label_str)

    ax.set_xticks(xs)
    ax.set_xticklabels(valid_benches, rotation=30, ha='right')
    ax.set_xlim(-0.5, len(valid_benches) - 0.5)
    
    # 先ほど作成した賢い対数スケールの適用
    apply_smart_log2_scale(ax)
    
    ax.xaxis.grid(True, linestyle=':', color='lightgray', zorder=0)
    ax.yaxis.grid(True, linestyle='--', alpha=0.35)

    # 4. タイトル・軸・凡例のテーブル化、一括ON/OFF制御の適用
    # ※ HIDE_PLOT_TEXTS = True の時はテキスト類がスッキリ消えます
    apply_decorations(ax, "Fully-Static Benchmarks", rcfg["ylabel"], 
                      f"Static Performance relative to {base}")

    save_fig(fig, os.path.join(out_dir, f'plot_static_summary_{base}-{comp_label}.png'))
    print(f"Saved static summary plot under: {out_dir}")