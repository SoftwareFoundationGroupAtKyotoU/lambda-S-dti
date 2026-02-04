# plot_scattered.py
import os
import numpy as np
import matplotlib.pyplot as plt

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
)

from matplotlib.ticker import FixedLocator

def plot_scattered(base: str, comp: str, static: bool):
    fs = ""
    if static:
        fs = "_fs"
    cfg = load_config(base, comp, static)
    latest, date_dir, data = ingest_latest_as_map(base, comp, cfg)
    scfg = cfg["scattered"]

    out_dir = os.path.join(date_dir, scfg["outdir"])
    ensure_dir(out_dir)

    from scipy import stats

    for bench, n_map in data.items():
        ns, base_means, base_cis, comp_means, comp_cis = [], [], [], [], []
        for n in sorted(n_map.keys()):
            b = n_map[n][f"{base}_times"]; c = n_map[n][f"{comp}_times"]
            if not b or not c: 
                continue
            b = np.asarray(b, dtype=float); c = np.asarray(c, dtype=float)
            base_mean = float(np.mean(b)); comp_mean = float(np.mean(c))

            if len(b) > 1:
                base_sem = float(stats.sem(b)); t_base = float(stats.t.ppf(0.975, len(b)-1)); base_ci = base_sem * t_base
            else: base_ci = 0.0

            if len(c) > 1:
                comp_sem = float(stats.sem(c)); t_comp = float(stats.t.ppf(0.975, len(c)-1)); comp_ci = comp_sem * t_comp
            else: comp_ci = 0.0

            ns.append(n); base_means.append(base_mean); base_cis.append(base_ci); comp_means.append(comp_mean); comp_cis.append(comp_ci)

        if not ns: 
            continue

        ticks = sorted(set(ns))
        fig, ax = plt.subplots(figsize=(8, 6))
        ax.errorbar(ns, base_means, yerr=base_cis, fmt='o', capsize=5, markersize=3, label=f'{base} mode (95% CI)')
        ax.errorbar(ns, comp_means, yerr=comp_cis, fmt='s', capsize=5, markersize=3, label=f'{comp} mode (95% CI)')
        ax.set_xlabel(scfg["xlabel"]); ax.set_ylabel(scfg["ylabel"])
        ax.set_title(f'{scfg["title_prefix"]}: {bench} with 95% Confidence Interval')
        ax.legend()
        ax.xaxis.set_major_locator(FixedLocator(ticks))
        ax.set_xlim(min(ticks) - 0.5, max(ticks) + 0.5)
        ax.set_xticklabels([]); ax.tick_params(axis='x', length=0)
        ax.grid(True, axis='y', linestyle='--', alpha=0.35)
        fig.tight_layout()
        fig.savefig(os.path.join(out_dir, f'plot_{bench}_{base}-{comp}_confidence{fs}.png'), dpi=150)
        plt.close(fig)

    print(f"Saved scatter plots under: {out_dir}")
    print(f"Done: {comp} vs {base}")