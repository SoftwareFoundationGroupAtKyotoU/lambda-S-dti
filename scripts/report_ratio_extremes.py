# report_ratio_extremes.py
import os
import numpy as np

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir, check_pair_exists,
    ratio_with_delta_ci, write_mutants_markdown,
    latest_date_dir, TARGET_PAIRS,
)

def run_ratio_extremes(base: str, comp: str, static: bool, date_dir: str, latest: str, rcfg: dict):
    cfg = load_config(base, [comp], static)
    _latest, _date_dir, data = ingest_latest_as_map(base, [comp], cfg)
    fs = "_fs" if static else ""

    out_high = os.path.join(date_dir, rcfg["outdir_high"], f"{base}-{comp}")
    out_low = os.path.join(date_dir, rcfg["outdir_low"], f"{base}-{comp}")

    for bench, n_map in data.items():
        computed = []
        for n, slot in n_map.items():
            r = ratio_with_delta_ci(slot[f"{base}_times"], slot[f"{comp}_times"])
            if r is None:
                continue
            ratio, ci, bm, cm, nb, nc = r
            if not np.isfinite(ratio):
                continue
            if rcfg.get("require_ci_excludes_1", True):
                if (ratio - ci) <= 1.0 <= (ratio + ci):
                    continue
            computed.append((
                n, ratio, ci, bm, cm, nb, nc,
                {"after_mutate": slot.get("after_mutate")},
            ))

        high_cases = sorted([c for c in computed if c[1] >= rcfg["ratio_high_min"]], key=lambda x: x[1], reverse=True)
        low_cases = sorted([c for c in computed if c[1] <= rcfg["ratio_low_max"]], key=lambda x: x[1])

        if high_cases:
            ensure_dir(out_high)
            bench_dir = os.path.join(out_high, bench); ensure_dir(bench_dir)
            md_path = os.path.join(bench_dir, f"{bench}_ratio_high{fs}.md")
            write_mutants_markdown(
                base, comp, md_path,
                header=f'Ratio High report for **{bench}** — `{comp}` / `{base}`{fs}',
                latest_dirname=latest,
                filter_note=f'{comp}/{base} >= {rcfg["ratio_high_min"]} ' + ('and CI excludes 1' if rcfg.get("require_ci_excludes_1", True) else ''),
                cases=high_cases
            )

        if low_cases:
            ensure_dir(out_low)
            bench_dir = os.path.join(out_low, bench); ensure_dir(bench_dir)
            md_path = os.path.join(bench_dir, f"{bench}_ratio_low{fs}.md")
            write_mutants_markdown(
                base, comp, md_path,
                header=f'Ratio Low report for **{bench}** — `{comp}` / `{base}`{fs}',
                latest_dirname=latest,
                filter_note=f'{comp}/{base} <= {rcfg["ratio_low_max"]} ' + ('and CI excludes 1' if rcfg.get("require_ci_excludes_1", True) else ''),
                cases=low_cases
            )

def main():
    latest, date_dir = latest_date_dir("logs")
    rcfg = {"outdir_high": "ratio_high", "outdir_low": "ratio_low",
            "ratio_high_min": 1.2, "ratio_low_max": 0.5, "require_ci_excludes_1": True}
    if TARGET_PAIRS:
        rcfg = load_config(TARGET_PAIRS[0][0], TARGET_PAIRS[0][1], False).get("ratio_extremes", rcfg)

    for base, comps in TARGET_PAIRS:
        for static in (False, True):
            if not check_pair_exists(date_dir, base, comps, static):
                continue
            for comp in comps:
                run_ratio_extremes(base, comp, static, date_dir, latest, rcfg)

    print(f"Saved ratio-high reports under: {os.path.join(date_dir, rcfg['outdir_high'])}")
    print(f"Saved ratio-low  reports under: {os.path.join(date_dir, rcfg['outdir_low'])}")

if __name__ == "__main__":
    main()
