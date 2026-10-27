# report_absolute_times.py
import os
import argparse
import numpy as np
from typing import List

try:
    from scipy import stats
except ImportError:
    stats = None

from benchviz import latest_date_dir, ensure_dir, parse_log_filename, iter_log_records, mean_time

def report_absolute_longest(target: str, static: bool, top_k: int = 30, extra_metrics: List[str] = None):
    """
    指定したターゲットのjsonlファイルを読み込み、
    絶対的な平均実行時間が長い Mutant Top K を抽出し、
    追加のメトリクス（cast回数など）と共に Markdown レポートを出力する。
    """
    if extra_metrics is None:
        extra_metrics = []

    log_root = "logs"
    
    # 最新のログディレクトリを取得
    try:
        latest, date_dir = latest_date_dir(log_root)
    except SystemExit as e:
        print(e)
        return

    fs_suffix = "_fs" if static else ""
    out_dir = os.path.join(date_dir, f"report_{target}_absolute_top{top_k}")
    ensure_dir(out_dir)

    # ターゲットに一致するファイル名を探す（ファイル名の分解は他スクリプトと共通）
    target_files = []
    for f in sorted(os.listdir(date_dir)):
        parsed = parse_log_filename(f)
        if parsed is not None and parsed[0] == target and parsed[2] == static:
            target_files.append((f, parsed[1]))

    if not target_files:
        print(f"No jsonl files found for target '{target}' (static={static}) in {date_dir}")
        return

    for filename, bench_name in target_files:
        filepath = os.path.join(date_dir, filename)
        computed = []

        for obj in iter_log_records(filepath):
            n = int(obj.get("mutant_index", -1))
            times = obj.get("times_sec", [])
            mean_val = mean_time(times)
            if mean_val is None:
                continue
            arr = np.asarray(times, dtype=float)

            if stats is not None and len(arr) > 1:
                ci = float(stats.sem(arr) * stats.t.ppf(0.975, len(arr)-1))
            else:
                ci = 0.0
            
            # 追加メトリクスの抽出
            extracted_extras = {}
            for m in extra_metrics:
                # jsonl 内にキーが存在しない場合は "N/A" とする
                extracted_extras[m] = obj.get(m, "N/A")
                
            computed.append({
                "n": n,
                "mean": mean_val,
                "ci": ci,
                "runs": len(arr),
                "extra_metrics": extracted_extras,
                "after_mutate": obj.get("after_mutate"),
            })
        
        # 平均実行時間の降順でソート
        longest_cases = sorted(computed, key=lambda x: x["mean"], reverse=True)[:top_k]
        
        if longest_cases:
            bench_dir = os.path.join(out_dir, bench_name)
            ensure_dir(bench_dir)
            
            md_path = os.path.join(bench_dir, f"{bench_name}_{target}_absolute_top{top_k}{fs_suffix}.md")
            
            # Markdownの生成
            with open(md_path, "w", encoding="utf-8") as md:
                md.write(f"# Top {top_k} Longest Absolute Execution Time for **{bench_name}** ({target})\n\n")
                md.write(f"- Log dir: `{latest}`\n")
                md.write(f"- File: `{filename}`\n\n")
                
                md.write("## Summary\n\n")
                
                # 動的なテーブルヘッダーの作成
                headers = ["mutant_index", "mean time (s)", "95% CI ±", "runs"] + extra_metrics
                md.write("| " + " | ".join(headers) + " |\n")
                md.write("|" + "|".join(["---:"] * len(headers)) + "|\n")
                
                # テーブル行の書き込み
                for c in longest_cases:
                    row = [
                        str(c["n"]),
                        f"{c['mean']:.6g}",
                        f"{c['ci']:.3g}",
                        str(c["runs"])
                    ]
                    for m in extra_metrics:
                        val = c["extra_metrics"][m]
                        # 小数点を含む数値の場合はフォーマットする
                        if isinstance(val, float):
                            row.append(f"{val:.6g}")
                        else:
                            row.append(str(val))
                            
                    md.write("| " + " | ".join(row) + " |\n")
                md.write("\n")
                
                # 詳細セクションの書き込み
                for c in longest_cases:
                    md.write(f"## Mutant {c['n']} — Mean: {c['mean']:.6g} s (±{c['ci']:.3g})\n\n")
                    
                    # 取得した追加メトリクスをリストとして表示
                    if extra_metrics:
                        md.write("**Metrics:**\n")
                        for m in extra_metrics:
                            val = c["extra_metrics"][m]
                            md.write(f"- `{m}`: {val}\n")
                        md.write("\n")
                    
                    am = c.get("after_mutate") or ""
                    md.write("**after_mutate**:\n\n```ocaml\n")
                    md.write(am)
                    md.write("\n```\n\n")

    print(f"Saved absolute longest execution time reports under: {out_dir}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Report Top K longest absolute execution times with extra metrics.")
    parser.add_argument("--target", type=str, required=True, help="Target component to analyze (e.g., SLHC)")
    parser.add_argument("--static", action="store_true", help="Use static (_fs) files")
    parser.add_argument("--top", type=int, default=30, help="Number of top mutants to report (default: 30)")
    parser.add_argument("--metrics", nargs='*', default=[], help="Additional metrics to extract from jsonl (e.g. casts inferences)")
    
    args = parser.parse_args()
    report_absolute_longest(args.target, args.static, args.top, args.metrics)