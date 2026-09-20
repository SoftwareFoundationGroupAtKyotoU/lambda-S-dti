# report_ablation_summary.py
#
# A（id適用最適化）/H（hash-consing & compose memo化）の寄与度、および
# GRIFT（GRIFTCM=Cバックエンド, GRIFTM=Racketバックエンド）との比較を、
# ratio（comp_mean_time / base_mean_time）の幾何平均としてまとめた
# Markdownサマリーを出力する。
#
# mutant数がベンチマーク間で大きく偏る（4〜2048）ため、
#   1. ベンチマークごとに全mutantのratioの幾何平均を取り、
#   2. さらにベンチマーク間で（mutant数によらず）等重みで幾何平均する
# という2段集計にする。これにより church-65532/quicksort のような
# mutant数が極端に多いベンチマークが pooled 値を支配しない。
import os
import math
from typing import Dict, List, Optional, Tuple

from benchviz import load_config, ingest_latest_as_map, latest_date_dir, ensure_dir


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
            b_mean = sum(b_times) / len(b_times)
            c_mean = sum(c_times) / len(c_times)
            if b_mean > 0 and c_mean > 0:
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

    pairs = [
        # (section, base, comp, static, note)
        ("A effect, H off",  "SLNM", "ALNM", False, "A = id-application optimization (`alt` translation) ON vs OFF, with H (hash-consing) OFF on both sides."),
        ("A effect, H on",   "SLHM", "ALHM", False, "Same A on/off contrast, but with H ON on both sides."),
        ("H effect, A off",  "SLNM", "SLHM", False, "H = coercion hash-consing + compose memoization ON vs OFF, with A OFF on both sides."),
        ("H effect, A on",   "ALNM", "ALHM", False, "Same H on/off contrast, but with A ON on both sides."),
        ("A+H combined",     "SLNM", "ALHM", False, "Fully-unoptimized baseline vs fully-optimized (A+H) config."),
        ("ALHM vs GRIFTCM (C backend)",  "GRIFTCM", "ALHM", False, "GRIFT compiled with its C backend, monotonic references. Only benchmarks present on both sides are shown (GRIFT run is missing church-65532/loop)."),
        ("ALHM vs GRIFTM (Racket backend)", "GRIFTM", "ALHM", False, "GRIFT's own (Racket/perf) backend, monotonic references."),
        ("Fully-static floor: ALHM",    "STATICENG", "ALHM", True, "Single fully-typed (no `?`) mutant per benchmark, compared against the fully-static reference build (no coercion machinery at all)."),
        ("Fully-static floor: GRIFTCM", "STATICENG", "GRIFTCM", True, "Same fully-typed comparison for GRIFT's C backend."),
        ("Fully-static floor: GRIFTM",  "STATICENG", "GRIFTM", True, "Same fully-typed comparison for GRIFT's Racket backend."),
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
                  "(equal weight per benchmark, regardless of how many mutants that "
                  "benchmark has — mutant counts range from 4 to 2048 across benchmarks "
                  "in this run, so a flat pooled geomean would be dominated by "
                  "`church-65532`/`quicksort`).\n")
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

        md.write("## 1. Optimization ablation (A, H)\n\n")
        for label, base, comp, static, note, ratios_by_bench, per_bench, pooled in results[:5]:
            md.write(f"#### {label}\n\n")
            write_table(md, base, comp, ratios_by_bench, per_bench, pooled, note)

        md.write("## 2. ALHM vs GRIFT\n\n")
        for label, base, comp, static, note, ratios_by_bench, per_bench, pooled in results[5:7]:
            md.write(f"#### {label}\n\n")
            write_table(md, base, comp, ratios_by_bench, per_bench, pooled, note)

        md.write("## 3. Fully-static floor (no `?`/Dyn at all, single mutant per benchmark)\n\n")
        for label, base, comp, static, note, ratios_by_bench, per_bench, pooled in results[7:]:
            md.write(f"#### {label}\n\n")
            write_table(md, base, comp, ratios_by_bench, per_bench, pooled, note)

        md.write("## 4. L (eager/lazy) and M (monotonic/guarded) — not varied in this run\n\n")
        md.write(
            "Every OCaml-side log file in this run has mode char 2 fixed to `L` (lazy) "
            "and mode char 4 fixed to `M` (monotonic) — no `E`/`G` counterpart exists in "
            "`" + latest + "`, so their contribution cannot be quantified from this dataset. "
            "`memo.md` has the author's own qualitative notes on the eager/lazy tradeoff: "
            "for a list of length n, attaching a coercion costs `n` compose calls eagerly vs "
            "`1` lazily, but decomposing it via a head/tail match costs `0` eagerly vs `2` "
            "lazily — i.e. lazy defers/batches composition that eager pays incrementally, "
            "which is a plausible explanation for cases where eager loses on list-heavy "
            "benchmarks, but this is a hypothesis from the notes, not a measurement in "
            "this run.\n\n"
        )

    print(f"Saved ablation summary report to: {out_path}")


if __name__ == "__main__":
    main()
