# plot_compare.py
import os
import numpy as np
import matplotlib.pyplot as plt
from scipy import stats

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
    save_fig, setup_plot_style, apply_decorations
)

def plot_compare(mode: str, static: bool = False):
    """
    church_mono_X と church_poly_X の実行時間を比較するプロットを生成します。
    """
    setup_plot_style()

    fs = "_fs" if static else ""
    
    # comp は [mode] として config を読み込む (空リストによるエラー回避)
    cfg = load_config(mode, [mode], static)
    
    # 対象となるファイルを church_mono_1..10, church_poly_1..10 に上書き
    cfg["target_benchmarks"] = [f"church_{t}_{i}" for t in ["mono", "poly"] for i in range(1, 11)]
    # jsonファイルのパターンも単一モード用に修正
    cfg["json_pattern"] = rf"({mode})_(.*?){fs}\.(jsonl|json)$"
    
    latest, date_dir, data = ingest_latest_as_map(mode, [mode], cfg)
    
    out_dir = os.path.join(date_dir, "compare_plot")
    ensure_dir(out_dir)

    numbers = list(range(1, 11))
    mono_means, mono_cis = [], []
    poly_means, poly_cis = [], []
    valid_numbers = []

    for i in numbers:
        bench_mono = f"church_mono_{i}"
        bench_poly = f"church_poly_{i}"
        
        # `--compare` を使って変異なし(1つだけ)で実行したため、mutant_indexは '1' になります
        mono_times = data.get(bench_mono, {}).get(1, {}).get(f"{mode}_times", [])
        poly_times = data.get(bench_poly, {}).get(1, {}).get(f"{mode}_times", [])
        
        if not mono_times or not poly_times:
            continue
            
        mono_arr = np.asarray(mono_times, dtype=float)
        poly_arr = np.asarray(poly_times, dtype=float)
        
        mono_mean = float(np.mean(mono_arr))
        poly_mean = float(np.mean(poly_arr))
        
        # 95%信頼区間の計算
        mono_ci = float(stats.sem(mono_arr) * stats.t.ppf(0.975, len(mono_arr)-1)) if len(mono_arr) > 1 else 0.0
        poly_ci = float(stats.sem(poly_arr) * stats.t.ppf(0.975, len(poly_arr)-1)) if len(poly_arr) > 1 else 0.0
        
        valid_numbers.append(i)
        mono_means.append(mono_mean)
        mono_cis.append(mono_ci)
        poly_means.append(poly_mean)
        poly_cis.append(poly_ci)

    if not valid_numbers:
        print(f"[plot_compare] 比較可能なデータが見つかりませんでした (Mode: {mode})")
        return

    fig, ax = plt.subplots(figsize=(10, 5))
    
    xs = np.arange(len(valid_numbers))
    offset = 0.15 # 点を左右にずらす幅
    
    # Mono のプロット (青色、丸)
    ax.errorbar(xs - offset, mono_means, yerr=mono_cis, fmt='^', color='tab:orange',
                capsize=5, elinewidth=2, capthick=2, markersize=8,
                linestyle='', label='Mono')
                
    # Poly のプロット (オレンジ色、三角)
    ax.errorbar(xs + offset, poly_means, yerr=poly_cis, fmt='d', color='tab:green',
                capsize=5, elinewidth=2, capthick=2, markersize=8,
                linestyle='', label='Poly')
                
    ax.set_xticks(xs)
    ax.set_xticklabels([str(n) for n in valid_numbers])
    ax.set_xlim(-0.5, len(valid_numbers) - 0.5)
    
    ax.set_ylim(bottom=0) # 時間なので0始まりにする
    
    ax.xaxis.grid(True, linestyle=':', color='lightgray', zorder=0)
    ax.yaxis.grid(True, linestyle='--', alpha=0.35)
    
    apply_decorations(ax, "Church Number (n)", "Execution Time (s)", 
                      f"Performance Comparison: Mono vs Poly ({mode})")
                      
    save_path = os.path.join(out_dir, f'plot_compare_church_{mode}{fs}.png')
    save_fig(fig, save_path)
    print(f"Saved compare plot to: {save_path}")

if __name__ == "__main__":
    # テスト実行用 (直接 python plot_compare.py と叩いた場合)
    import sys
    mode_to_plot = sys.argv[1] if len(sys.argv) > 1 else "SLHC"
    plot_compare(mode_to_plot)