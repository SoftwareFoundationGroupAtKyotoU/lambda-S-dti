# report_ablation_summary.py
#
# bin/bench.ml の軸別アブレーション（基準値 untypedALHMT から1軸だけ反転）の各軸の
# 寄与度、GRIFT（GRIFTCM = C backend, GRIFTLLVMM = LLVM backend）との比較、完全静的
# ビルドとの比較を、ratio（comp_mean_time / base_mean_time）の幾何平均として
# まとめた Markdown サマリーを出力する。モード名は benchviz.TARGET_PAIRS と同じ。
#
# mutant数がベンチマーク間で大きく偏る（4〜数百）ため、
#   1. ベンチマークごとに全mutantのratioの幾何平均を取り、
#   2. さらにベンチマーク間で（mutant数によらず）等重みで幾何平均する
# という2段集計にする。これにより mutant数が極端に多いベンチマークが
# pooled 値を支配しない。
import os
import math
from typing import Dict, List, Optional, Tuple

from benchviz import load_config, ingest_latest_as_map, latest_date_dir, ensure_dir, mean_time


def geomean(xs: List[float]) -> Optional[float]:
    vals = [x for x in xs if x is not None and x > 0 and math.isfinite(x)]
    if not vals:
        return None
    return math.exp(sum(math.log(v) for v in vals) / len(vals))


def bench_mutant_ratios(base: str, comp: str, static: bool = False) -> Dict[str, List[float]]:
    """bench -> [comp_mean_time / base_mean_time for each mutant present on both sides]"""
    cfg = load_config(base, [comp], static)
    _latest, _date_dir, data = ingest_latest_as_map(base, [comp], cfg)

    out: Dict[str, List[float]] = {}
    for bench, n_map in data.items():
        ratios = []
        for _n, slot in n_map.items():
            b_times = slot.get(f"{base}_times", [])
            c_times = slot.get(f"{comp}_times", [])
            if not b_times or not c_times:
                continue
            b_mean, c_mean = mean_time(b_times), mean_time(c_times)
            if b_mean is not None and c_mean is not None:
                ratios.append(c_mean / b_mean)
        if ratios:
            out[bench] = ratios
    return out


def summarize(ratios_by_bench: Dict[str, List[float]]) -> Tuple[Dict[str, float], Optional[float]]:
    per_bench = {}
    for bench, ratios in ratios_by_bench.items():
        gm = geomean(ratios)
        if gm is not None:
            per_bench[bench] = gm
    pooled = geomean(list(per_bench.values()))
    return per_bench, pooled


def write_table(md, base: str, comp: str, ratios_by_bench: Dict[str, List[float]],
                 per_bench: Dict[str, float], pooled: Optional[float], note: str = "") -> None:
    md.write(f"### `{comp}` / `{base}`\n\n")
    if note:
        md.write(f"{note}\n\n")
    if not per_bench:
        md.write("_No overlapping mutants found for this pair._\n\n")
        return
    md.write("`ratio < 1.0` means `" + comp + "` is faster than `" + base + "`.\n\n")
    md.write("| benchmark | mutants | geomean ratio | min | max |\n")
    md.write("|---|---:|---:|---:|---:|\n")
    for bench in sorted(per_bench.keys()):
        ratios = ratios_by_bench[bench]
        md.write(f"| {bench} | {len(ratios)} | {per_bench[bench]:.4f} "
                  f"| {min(ratios):.4f} | {max(ratios):.4f} |\n")
    if pooled is not None:
        md.write(f"| **pooled (geomean of per-bench geomeans)** | | **{pooled:.4f}** | | |\n")
    md.write("\n")


def headline_row(md, label: str, pooled: Optional[float]) -> None:
    if pooled is None:
        md.write(f"| {label} | n/a |\n")
        return
    speedup = 1.0 / pooled if pooled > 0 else float("nan")
    faster = "comp" if pooled < 1.0 else "base"
    md.write(f"| {label} | {pooled:.4f} ({speedup:.2f}x, {faster} faster) |\n")


def main() -> None:
    log_root = "logs"
    latest, date_dir = latest_date_dir(log_root)
    ensure_dir(date_dir)
    out_path = os.path.join(date_dir, "report_ablation_summary.md")

    base_mode = "untypedALHMT"
    pairs = [
        # (section, base, comp, static, note)。ratio = comp / base なので、
        # base に「その最適化を切った側」を置くと ratio < 1 = 最適化が効いている。
        ("id_opt (A vs S)",       "untypedSLHMT", base_mode, False, "id-application optimization (`alt` translation) ON (`A`) vs OFF (`S`)."),
        ("lazy vs eager (L vs E)", "untypedELHMT", base_mode, False, "Lazy (`L`) vs eager (`E`) list coercions."),
        ("hash-consing (H vs h)", "untypedALhMT", base_mode, False, "Coercion hash-consing + compose memoization ON (`H`) vs OFF (`h`)."),
        ("monotonic vs guarded (M vs G)", "untypedALHGT", base_mode, False, "Monotonic (`M`) vs guarded (`G`) references/arrays."),
        ("tvs_opt (T vs t)",      "untypedALHMt", base_mode, False, "Type-variable optimization ON (`T`) vs OFF (`t`)."),
        ("untyped vs typed source", "typedALHMT", base_mode, False, "Same configuration on the untyped vs the typed source. Benchmarks whose two sources have different mutant counts are excluded (mutant_index would not align)."),
        ("untypedALHMT vs GRIFTCM (C backend)", "GRIFTCM", base_mode, False, "GRIFT compiled with its C backend, monotonic references. Only benchmarks present on both sides are shown."),
        ("untypedALHMT vs GRIFTLLVMM (LLVM backend)", "GRIFTLLVMM", base_mode, False, "GRIFT compiled with its LLVM backend (grift's default), monotonic references."),
        ("Fully-static floor: untypedALHMT", "untypedSTATICEhGT", base_mode, True, "Single fully-typed (no `?`) mutant per benchmark, compared against the fully-static reference build (no coercion machinery at all)."),
        ("Fully-static floor: GRIFTCMS", "untypedSTATICEhGT", "GRIFTCMS", True, "Same fully-typed comparison for GRIFT's C backend with `--static`."),
    ]
    sections = [
        ("1. Single-axis ablation from untypedALHMT", 0, 6),
        ("2. untypedALHMT vs GRIFT", 6, 8),
        ("3. Fully-static floor (no `?`/Dyn at all, single mutant per benchmark)", 8, 10),
    ]

    results = []
    for label, base, comp, static, note in pairs:
        ratios_by_bench = bench_mutant_ratios(base, comp, static)
        per_bench, pooled = summarize(ratios_by_bench)
        results.append((label, base, comp, static, note, ratios_by_bench, per_bench, pooled))

    with open(out_path, "w", encoding="utf-8") as md:
        md.write("# Ablation & GRIFT-comparison summary\n\n")
        md.write(f"- Log dir: `{latest}`\n")
        md.write("- All ratios are `comp_mean_time / base_mean_time`, computed per mutant, "
                  "then geomean within a benchmark, then geomean across benchmarks "
                  "(equal weight per benchmark, regardless of how many mutants it has, so "
                  "benchmarks with many mutants do not dominate the pooled value).\n")
        md.write("- No formal CI is computed here (that would need a bootstrap over "
                  "benchmarks/mutants); the per-benchmark `min`/`max` columns are a crude "
                  "robustness indicator instead. For per-mutant CIs see `relative/` plots "
                  "(`ratio_with_delta_ci`).\n\n")

        md.write("## Headline numbers (pooled, equal weight per benchmark)\n\n")
        md.write("| comparison | pooled geomean ratio |\n")
        md.write("|---|---|\n")
        for label, base, comp, static, note, ratios_by_bench, per_bench, pooled in results:
            headline_row(md, label, pooled)
        md.write("\n")

        for title, lo, hi in sections:
            md.write(f"## {title}\n\n")
            for label, base, comp, static, note, ratios_by_bench, per_bench, pooled in results[lo:hi]:
                md.write(f"#### {label}\n\n")
                write_table(md, base, comp, ratios_by_bench, per_bench, pooled, note)

    print(f"Saved ablation summary report to: {out_path}")


if __name__ == "__main__":
    main()
