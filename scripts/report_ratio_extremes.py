# report_ratio_extremes.py
import os
import numpy as np

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
    ratio_with_delta_ci, write_mutants_markdown,
    base, comp
)

def main():
    cfg = load_config()
    latest, date_dir, data = ingest_latest_as_map(cfg)
    rcfg = cfg["ratio_extremes"]

    out_high = os.path.join(date_dir, rcfg["outdir_high"])
    out_low  = os.path.join(date_dir, rcfg["outdir_low"])
    ensure_dir(out_high); ensure_dir(out_low)

    for bench, n_map in data.items():
        computed = []
        for n, slot in n_map.items():
            r = ratio_with_delta_ci(slot[f"{base}_times"], slot[f"{comp}_times"])
            if r is None:
                continue
            ratio, ci, cm, sm, nc, ns = r
            if not np.isfinite(ratio):
                continue
            if rcfg.get("require_ci_excludes_1", True):
                if (ratio - ci) <= 1.0 <= (ratio + ci):
                    continue
            computed.append((
                n, ratio, ci, cm, sm, nc, ns,
                {
                    "after_mutate": slot.get("after_mutate"),
                    "after_insertion": slot.get("after_insertion"),
                    "after_translation": slot.get("after_translation"),
                }
            ))

        high_cases = sorted([c for c in computed if c[1] >= rcfg["ratio_high_min"]], key=lambda x: x[1], reverse=True)
        low_cases  = sorted([c for c in computed if c[1] <= rcfg["ratio_low_max"]], key=lambda x: x[1])

        if high_cases:
            bench_dir = os.path.join(out_high, bench); ensure_dir(bench_dir)
            md_path = os.path.join(bench_dir, f"{bench}_ratio_high.md")
            write_mutants_markdown(
                md_path,
                header=f'Ratio High report for **{bench}**',
                latest_dirname=latest,
                filter_note=f'{comp}/{base} ≥ {rcfg["ratio_high_min"]} ' + ('and CI excludes 1' if rcfg.get("require_ci_excludes_1", True) else ''),
                cases=high_cases
            )

        if low_cases:
            bench_dir = os.path.join(out_low, bench); ensure_dir(bench_dir)
            md_path = os.path.join(bench_dir, f"{bench}_ratio_low.md")
            write_mutants_markdown(
                md_path,
                header=f'Ratio Low report for **{bench}**',
                latest_dirname=latest,
                filter_note=f'{comp}/{base} ≤ {rcfg["ratio_low_max"]} ' + ('and CI excludes 1' if rcfg.get("require_ci_excludes_1", True) else ''),
                cases=low_cases
            )

    print(f"Saved ratio-high reports under: {out_high}")
    print(f"Saved ratio-low  reports under: {out_low}")

if __name__ == "__main__":
    main()
