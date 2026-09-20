# report_herman.py
import os
import numpy as np

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir, check_pair_exists,
    ratio_with_delta_ci, write_mutants_markdown, robust_left_outliers_log10,
    latest_date_dir, TARGET_PAIRS,
)

def _get_mem_bytes(slot, mode):
    # C側ドライバは "mem" をフラットな GC 割当バイト数として書く
    # （nested な alloc_words_per_run/alloc_bytes_per_run は現行スキーマには無い）
    return slot.get(f"{mode}_mem")

def run_herman(base: str, comp: str, static: bool, date_dir: str, latest: str, hcfg: dict):
    cfg = load_config(base, [comp], static)
    _latest, _date_dir, data = ingest_latest_as_map(base, [comp], cfg, extra_metrics=["mem"])

    outdir = hcfg.get("outdir", "herman")
    k = float(hcfg.get("mad_k", 3.5))
    min_n = int(hcfg.get("min_n", 8))
    fs = "_fs" if static else ""

    root = os.path.join(date_dir, outdir, f"{base}-{comp}")

    for bench, n_map in data.items():
        # 1) ベンチ内で comp/base の GC割当バイト数の比を収集
        ns, ratios = [], []
        for n in sorted(n_map.keys()):
            slot = n_map[n]
            base_mem = _get_mem_bytes(slot, base)
            comp_mem = _get_mem_bytes(slot, comp)
            if base_mem is None or comp_mem is None:
                continue
            base_mem = float(base_mem); comp_mem = float(comp_mem)
            if not np.isfinite(base_mem) or base_mem <= 0:
                continue
            ns.append(n)
            ratios.append(comp_mem / base_mem)

        if not ns:
            continue

        # 2) ロバスト左側外れ値（"極端に少ないメモリ"）抽出
        idxs, stats = robust_left_outliers_log10(ratios, k=k, min_n=min_n)
        if not idxs:
            continue

        # 3) Markdown 用にまとめ（comp/base 実行時間比も添える）
        cases = []
        for i in idxs:
            n = ns[i]
            slot = n_map[n]
            rr = ratio_with_delta_ci(slot[f"{base}_times"], slot[f"{comp}_times"])
            if rr is None:
                continue
            r, ci, bm, cm, nb, nc = rr
            cases.append((
                n, r, ci, bm, cm, nb, nc,
                {"after_mutate": slot.get("after_mutate")},
            ))

        if not cases:
            continue

        ensure_dir(root)
        bench_dir = os.path.join(root, bench)
        ensure_dir(bench_dir)
        md_path = os.path.join(bench_dir, f"{bench}_herman{fs}.md")

        note = (f"Robust left-outlier on log10({comp}/{base} GC-allocated bytes), "
                f"method={stats.get('method','mad')}, "
                + (f"k={k}, " if stats.get('method','mad')=='mad' else "")
                + f"n={stats.get('n','-')} (min_n={min_n})")

        write_mutants_markdown(
            base, comp, md_path,
            header=f'Herman (robust) report for **{bench}** — `{comp}` / `{base}`{fs}',
            latest_dirname=latest,
            filter_note=note,
            cases=sorted(cases, key=lambda x: x[1])  # comp/base 時間比の小さい順（速い方から）
        )

def main():
    latest, date_dir = latest_date_dir("logs")
    hcfg = {"outdir": "herman", "mad_k": 3.5, "min_n": 8}
    if TARGET_PAIRS:
        hcfg = load_config(TARGET_PAIRS[0][0], TARGET_PAIRS[0][1], False).get("herman", hcfg)

    wrote_any = False
    for base, comps in TARGET_PAIRS:
        for static in (False, True):
            if not check_pair_exists(date_dir, base, comps, static):
                continue
            for comp in comps:
                run_herman(base, comp, static, date_dir, latest, hcfg)
                wrote_any = True

    root = os.path.join(date_dir, hcfg.get("outdir", "herman"))
    if wrote_any:
        print(f"Saved robust Herman reports under: {root}")
    else:
        print("No Herman outliers found for any TARGET_PAIRS entry.")

if __name__ == "__main__":
    main()
