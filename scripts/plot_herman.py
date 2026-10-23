# plot_herman.py
import os
import numpy as np
import matplotlib.pyplot as plt
from typing import List, Union

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
    ratio_with_delta_ci, integer_xticks, save_fig, robust_left_outliers_log10, get_plot_style,
    parse_comp_args, draw_binomial_boundaries
)

def _get_mem_bytes(slot, mode):
    # report_herman.py と同じ指標: C 側ドライバが "mem" に書く GC 割当バイト数（フラットな数値）
    v = slot.get(f"{mode}_mem")
    return None if v is None else float(v)

def plot_herman(base: str, comp: Union[str, List[str]], static: bool):
    comps, comp_label, fs, is_multi = parse_comp_args(comp, static)
    if not comps:
        return

    cfg = load_config(base, comps, static)
    latest, date_dir, data = ingest_latest_as_map(base, comps, cfg, extra_metrics=["mem"])
    hcfg = cfg.get("herman", {})
    outdir = hcfg.get("outdir", "herman")
    k = float(hcfg.get("mad_k", 3.5))
    min_n = int(hcfg.get("min_n", 8))

    xlabel = hcfg.get("xlabel", "Pattern for Replacing Type Variables with Dyn (n)")
    ylabel = hcfg.get("ylabel", f"Relative Execution Time ({comp_label} / {base})")
    title_prefix = hcfg.get("title_prefix", "Herman (robust)")

    root = os.path.join(date_dir, outdir)
    # NOTE: ここで root を作らない。実際に図を保存するときだけ ensure_dir する
    #       （mem が記録されていないログ（GRIFT 等）では 1 枚も描かないため、
    #        先に作ると空の herman/ フォルダだけが残る）。

    wrote = 0

    for bench, n_map in data.items():
        # このベンチマークにおける、有効な comp データを集める
        # valid_data[comp_name] = { 'ns': ..., 'ratios': ... }
        valid_data = {}

        for c in comps:
            # 1) c/base の GC 割当バイト数（mem）の比を集める
            ns, ratios_pb = [], []
            for n in sorted(n_map.keys()):
                slot = n_map[n]
                base_pb = _get_mem_bytes(slot, base)
                comp_pb = _get_mem_bytes(slot, c)
                if base_pb is None or comp_pb is None or not np.isfinite(base_pb) or base_pb <= 0:
                    continue
                ns.append(n)
                ratios_pb.append(float(comp_pb) / float(base_pb))

            if not ns:
                continue

            # 2) ロバスト検出（左側の外れ値：comp/base の mem が極端に小さい）
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
        ensure_dir(bench_dir)  # root もここで初めて作られる

        # --- 区切り線の位置 ---
        n_total = max(d['n_total'] for d in valid_data.values())  # このベンチの総ミュータント数（2^n が保証されている想定）
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
            style = get_plot_style(c, i)

            label_str = f'{c}/{base} Ratio (95% CI)'

            ax.errorbar(d['ns'], d['ratios'], yerr=d['cis'], fmt=style["marker"], color=style["color"],
                    capsize=5, markersize=3, label=label_str)
        
        if all_ticks:
            integer_xticks(ax, list(all_ticks))   # 目盛はデータ点（整数）のみに
        ax.set_xlim(0.5, n_total + 0.5)  # 全体範囲を 0.5〜2^n+0.5 に固定

        draw_binomial_boundaries(ax, n_total)  # 区切りの縦線

        ax.set_title(f'{title_prefix}: {bench}')
        ax.set_xlabel(xlabel); ax.set_ylabel(ylabel)
        ax.grid(True, axis='y', linestyle='--', alpha=0.35); ax.legend()
        save_fig(fig, os.path.join(bench_dir, f'plot_{bench}_{base}-{comp_label}_herman_zigzag{fs}.png'))
        wrote += 1

        # (2) 昇順ソート
        if not is_multi:
            c = comps[0]
            d = valid_data[c]
            style = get_plot_style(c, 0)
            bundle = sorted(zip(d['ns'], d['ratios'], d['cis']), key=lambda x: x[1])
            xs = list(range(1, len(bundle) + 1))
            ys = [b[1] for b in bundle]; ycis = [b[2] for b in bundle]
            fig, ax = plt.subplots(figsize=(11, 6))
            ax.errorbar(xs, ys, yerr=ycis, fmt=style["marker"], color=style["color"],
                        capsize=3, markersize=2, rasterized=True, label=f'{comp_label}/{base} Ratio (95% CI)')
            ax.axhline(1, color='gray', linestyle='--', label=f'{base} = 1 Baseline')
            ax.set_xlim(0.5, len(xs) + 0.5); ax.set_xticks([])
            ax.set_xlabel(xlabel + " (filtered & sorted)"); ax.set_ylabel(ylabel)
            ax.set_title(f'{title_prefix} (sorted): {bench}')
            ax.legend(); ax.grid(True, axis='y', alpha=0.3)
            save_fig(fig, os.path.join(bench_dir, f'plot_{bench}_{base}-{comp_label}_herman_sorted{fs}.png'))
            wrote += 1

    if wrote:
        print(f"Saved {wrote} robust Herman plot(s) under: {root}")
        print(f"Done: {comp_label} vs {base}")
    else:
        print(f"[plot_herman] skipped {comp_label} vs {base}: "
              f"no mem (GC-allocated bytes) outliers in logs")