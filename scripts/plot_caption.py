# scripts/plot_caption.py
import os
import argparse
import matplotlib.pyplot as plt

from benchviz import (
    TARGET_PAIRS, parse_comp_args, get_plot_style, 
    format_comp_label, setup_plot_style, ensure_dir
)

def plot_all_captions(horizontal=False):
    """
    TARGET_PAIRS に定義された組み合わせごとに、
    色と形の対応を示す凡例（caption）画像を logs/caption 配下に生成します。
    """
    setup_plot_style()

    out_dir = os.path.join("logs", "caption")
    ensure_dir(out_dir)

    for base, comp in TARGET_PAIRS:
        comps, comp_label, _, _ = parse_comp_args(comp, False)
        
        fig, ax = plt.subplots(figsize=(0.1, 0.1))
        ax.axis('off') 
        
        modes = [base] + comps
        seen = set()
        unique_modes = []
        for m in modes:
            if m not in seen:
                unique_modes.append(m)
                seen.add(m)
        
        for i, mode in enumerate(unique_modes):
            desc = format_comp_label(mode)
            label_str = f"{desc}"
            style = get_plot_style(mode, i)
            
            ax.plot([], [], color=style.get("color", "black"), 
                    marker=style.get("marker", "o"), 
                    linestyle='None', markersize=10, label=label_str)
        
        # ▼ 横並びオプションの処理
        if horizontal:
            ncol = len(unique_modes)  # 項目数と同じ列数にする（完全な1行横並び）
        else:
            ncol = 1 if len(unique_modes) <= 3 else 2  # 縦並び（既存の挙動）

        ax.legend(loc='center', fontsize=12, frameon=True, 
                  title="", title_fontsize=14,
                  ncol=ncol, labelspacing=1.2, borderpad=1.0)
        
        # 横並びの時はファイル名を変えて上書きを防ぐ（任意）
        suffix = "_horizontal" if horizontal else ""
        out_filename = f"caption_{base}-{comp_label}{suffix}.png"
        out_path = os.path.join(out_dir, out_filename)
        
        fig.savefig(out_path, dpi=150, bbox_inches='tight', pad_inches=0.02)
        plt.close(fig) 
        
        print(f"✅ 凡例画像{suffix}を保存しました: {out_path}")

if __name__ == "__main__":
    # コマンドライン引数の設定
    parser = argparse.ArgumentParser(description="Generate legend captions for benchmarks.")
    parser.add_argument("--horizontal", action="store_true", 
                        help="Display the legend horizontally (in a single row).")
    args = parser.parse_args()

    plot_all_captions(horizontal=args.horizontal)