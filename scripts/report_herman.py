# report_herman.py
import os
import numpy as np

from benchviz import (
    load_config, ingest_latest_as_map, ensure_dir,
    ratio_with_delta_ci, write_mutants_markdown, robust_left_outliers_log10, 
    base, comp
)

def _get_promoted_bytes(slot, mode):
    # 期待キー: "{base}_promoted_bytes" / "{comp}_promoted_bytes"
    return slot.get(f"{mode}_promoted_bytes")

def main():
    cfg = load_config()
    latest, date_dir, data = ingest_latest_as_map(cfg)
    hcfg = cfg.get("herman", {})
    outdir = hcfg.get("outdir", "herman")
    k = float(hcfg.get("mad_k", 3.5))
    min_n = int(hcfg.get("min_n", 8))

    root = os.path.join(date_dir, outdir)
    ensure_dir(root)

    for bench, n_map in data.items():
        # 1) ベンチ内で comp/base promoted BYTES の比を収集
        ns, ratios = [], []
        for n in sorted(n_map.keys()):
            slot = n_map[n]
            base_pb = _get_promoted_bytes(slot, f"{base}")
            comp_pb = _get_promoted_bytes(slot, f"{comp}")
            if base_pb is None or comp_pb is None or not np.isfinite(base_pb) or base_pb <= 0:
                continue
            ns.append(n)
            ratios.append(float(comp_pb) / float(base_pb))

        if not ns:
            continue

        # 2) ロバスト左側外れ値（“極端に小さい”）抽出
        idxs, stats = robust_left_outliers_log10(ratios, k=k, min_n=min_n)
        if not idxs:
            continue

        # 3) Markdown 用にまとめ（S/C 実行時間比も添える）
        cases = []
        for i in idxs:
            n = ns[i]
            slot = n_map[n]
            rr = ratio_with_delta_ci(slot[f"{base}_times"], slot[f"{comp}_times"])
            if rr is None:
                # 時間が取れていなくてもコード断片だけは載せたいなら ci=0 等で継続可
                continue
            r, ci, cm, sm, nc, nsamp = rr
            cases.append((
                n, r, ci, cm, sm, nc, nsamp,
                {
                    "after_mutate": slot.get("after_mutate"),
                    "after_insertion": slot.get("after_insertion"),
                    "after_translation": slot.get("after_translation"),
                }
            ))

        if not cases:
            continue

        bench_dir = os.path.join(root, bench)
        ensure_dir(bench_dir)
        md_path = os.path.join(bench_dir, f"{bench}_herman.md")

        # ヘッダと検出パラメータの注記
        note = (f"Robust left-outlier on log10(S/C promoted bytes), "
                f"method={stats.get('method','mad')}, "
                + (f"k={k}, " if stats.get('method','mad')=='mad' else "")
                + f"n={stats.get('n','-')} (min_n={min_n})")

        write_mutants_markdown(
            md_path,
            header=f'Herman (robust) report for **{bench}**',
            latest_dirname=latest,
            filter_note=note,
            cases=sorted(cases, key=lambda x: x[1], reverse=True)  # S/C 時間比の大きい順
        )

    print(f"Saved robust Herman reports under: {root}")

if __name__ == "__main__":
    main()
