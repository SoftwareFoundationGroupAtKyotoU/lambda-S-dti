# benchviz.py
import os
import re
import json
from typing import Dict, Any, List, Tuple, Optional

import numpy as np

try:
    # プロットするスクリプトだけ matplotlib を import する想定
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FixedLocator
except Exception:
    plt = None
    FixedLocator = None

try:
    from scipy import stats
except Exception:
    stats = None

base = "AEC"
comp = "ALC"

# =========================
# 設定まわり
# =========================
_DEFAULT_CONFIG = {
    "log_root": "logs",
    "json_pattern": fr"({base}|{comp})_(.*?)\.(jsonl|json)$",
    "target_benchmarks": [
        "church_big", "church_small", "church",
        "evenodd", "fib", "tak", "loop", "fold", "map",
        "mklist", "zipwith", 
    ],
    # 相対グラフ
    "relative": {
        "outdir": "relative",
        "xlabel": "Pattern for Replacing Type Variables with Dyn (n)",
        "ylabel": f"Relative Execution Time ({comp} / {base})",
        "title_prefix": "Relative Performance",
        "zigzag_tiers": 10,
        "zigzag_fontsize": 5
    },
    # 散布グラフ
    "scattered": {
        "outdir": "scattered",
        "xlabel": "Pattern for Replacing Type Variables with Dyn (n)",
        "ylabel": "Execution Time (seconds)",
        "title_prefix": "Benchmark"
    },
    # Herman
    "herman": {
        "outdir": "herman",
        "mad_k": 1,
        "min_n": 2,
        "xlabel": "Pattern for Replacing Type Variables with Dyn (n)",
        "ylabel": f"Relative Execution Time ({comp} / {base})",
        "title_prefix": "Herman (robust)"
    },
    # 極端比レポート
    "ratio_extremes": {
        "outdir_high": "ratio_high",
        "outdir_low": "ratio_low",
        "ratio_high_min": 1.2,
        "ratio_low_max": 0.5,
        "require_ci_excludes_1": True
    }
}

def load_config(path: str = "benchviz.config.json") -> Dict[str, Any]:
    """外部 JSON を読み込み、デフォルトとマージして返す。読み込んだ有効設定を標準出力に表示する。"""
    cfg: Dict[str, Any] = dict(_DEFAULT_CONFIG)  # 既定ベース
    used_path = None
    user: Dict[str, Any] = {}

    if os.path.exists(path):
        used_path = path
        try:
            with open(path, "r", encoding="utf-8") as f:
                user = json.load(f)
        except json.JSONDecodeError as e:
            print(f"[benchviz] 設定ファイルの解析に失敗しました: {path}: {e}")
            user = {}

        # dict はシャローにマージ（dict 同士のみマージ／他は置換）
        for k, v in user.items():
            if isinstance(v, dict) and isinstance(cfg.get(k), dict):
                merged = dict(cfg[k]); merged.update(v)
                cfg[k] = merged
            else:
                cfg[k] = v

    # 有効設定を表示
    print("[benchviz] Effective configuration "
          f"(path: {used_path if used_path else '<defaults only>'})")
    print(json.dumps(cfg, ensure_ascii=False, indent=2, sort_keys=True))

    return cfg


# =========================
# 共通 I/O
# =========================

def latest_date_dir(log_root: str) -> Tuple[str, str]:
    dates = [d for d in os.listdir(log_root) if os.path.isdir(os.path.join(log_root, d))]
    if not dates:
        raise SystemExit(f"No log directories found under '{log_root}/'.")
    latest = max(dates)  # "YYYYMMDD-HH:MM:SS" は辞書順=時系列
    return latest, os.path.join(log_root, latest)


def ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)


def _extract_c_pm_from_mem(mem_obj: Any) -> Optional[float]:
    """'mem' → promoted/minor（words/Run）比（base 用）"""
    if not isinstance(mem_obj, dict):
        return None
    alloc = mem_obj.get("alloc_words_per_run")
    if not isinstance(alloc, dict):
        return None
    minor = alloc.get("minor")
    promoted = alloc.get("promoted")
    if minor is None or promoted is None:
        return None
    try:
        minor = float(minor)
        promoted = float(promoted)
    except Exception:
        return None
    if minor <= 0:
        return None
    return promoted / minor

def _extract_promoted_bytes(mem_obj: Any) -> Optional[float]:
    """'mem' → alloc_bytes_per_run.promoted（bytes/Run）を返す。無ければ None。"""
    if not isinstance(mem_obj, dict):
        return None
    ab = mem_obj.get("alloc_bytes_per_run")
    if not isinstance(ab, dict):
        return None
    p = ab.get("promoted")
    if p is None:
        return None
    try:
        return float(p)
    except Exception:
        return None


def ingest_latest_as_map(cfg: Dict[str, Any]) -> Tuple[str, str, Dict[str, Dict[int, Dict[str, Any]]]]:
    """
    最新ログディレクトリから、
      bench -> mutant_index -> {
        'C_times': [], 'S_times': [],
        'after_mutate': str|None, 'after_insertion': str|None, 'after_translation': str|None,
        'C_pm': float|None
      }
    の辞書を返す。
    """
    log_root = cfg["log_root"]
    json_pattern = re.compile(cfg["json_pattern"])
    target_benchmarks = set(cfg["target_benchmarks"])

    latest, date_dir = latest_date_dir(log_root)

    data_by_benchmark: Dict[str, Dict[int, Dict[str, Any]]] = {}

    def ensure_slot(bench: str, n: int):
        if bench not in data_by_benchmark:
            data_by_benchmark[bench] = {}
        if n not in data_by_benchmark[bench]:
            data_by_benchmark[bench][n] = {
                f"{base}_times": [], f"{comp}_times": [],
                "after_mutate": None, "after_insertion": None, "after_translation": None,
                f"{base}_pm": None,
                f"{base}_promoted_bytes": None,
                f"{comp}_promoted_bytes": None
            }

    def update_from_obj(obj: Dict[str, Any], mode: str, bench: str):
        n = int(obj.get("mutant_index"))
        times = obj.get("times_sec", [])
        am = obj.get("after_mutate")
        ai = obj.get("after_insertion")
        at = obj.get("after_translation")
        mem = obj.get("mem")

        ensure_slot(bench, n)
        slot = data_by_benchmark[bench][n]

        if isinstance(times, list):
            (slot[f"{base}_times"] if mode == base else slot[f"{comp}_times"]).extend(times)
        if am and slot["after_mutate"] is None:
            slot["after_mutate"] = am
        if ai and slot["after_insertion"] is None:
            slot["after_insertion"] = ai
        if mode == comp and at:
            slot["after_translation"] = at
        if mode == base and slot[f"{base}_pm"] is None:
            cpm = _extract_c_pm_from_mem(mem)
            if cpm is not None:
                slot[f"{base}_pm"] = cpm
        if mem is not None:
            pb = _extract_promoted_bytes(mem)
            if pb is not None:
                key = f"{base}_promoted_bytes" if mode == base else f"{comp}_promoted_bytes"
                if slot[key] is None:
                    slot[key] = pb

    for filename in os.listdir(date_dir):
        m = json_pattern.match(filename)
        if not m:
            continue
        mode, bench, ext = m.group(1), m.group(2), m.group(3)
        if bench not in target_benchmarks:
            continue
        path = os.path.join(date_dir, filename)
        if ext == "jsonl":
            with open(path, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    update_from_obj(json.loads(line), mode, bench)
        else:
            with open(path, "r", encoding="utf-8") as f:
                top = json.load(f)
            for mobj in top.get("mutants", []):
                update_from_obj(mobj, mode, bench)

    return latest, date_dir, data_by_benchmark


# =========================
# 統計ユーティリティ
# =========================

def ratio_with_delta_ci(base_vals: List[float], comp_vals: List[float]) -> Optional[Tuple[float, float, float, float, int, int]]:
    """
    comp/base 比と 95%CI（デルタ法）を返す:
      (ratio, ci, base_mean, comp_mean, n_base, n_comp)
    標本が少なすぎる場合は None。
    """
    if len(base_vals) == 0 or len(comp_vals) == 0:
        return None
    base_array = np.asarray(base_vals, dtype=float)
    comp_array = np.asarray(comp_vals, dtype=float)
    base_mean = float(np.mean(base_array))
    comp_mean = float(np.mean(comp_array))
    if not np.isfinite(base_mean) or not np.isfinite(comp_mean) or base_mean <= 0 or comp_mean <= 0:
        return None

    ratio = comp_mean / base_mean
    n_base, n_comp = len(base_array), len(comp_array)
    if stats is None:
        # SciPy 無い場合は CI=0 とする
        return ratio, 0.0, base_mean, comp_mean, n_base, n_comp

    base_var = float(np.var(base_array, ddof=1)) if n_base > 1 else 0.0
    comp_var = float(np.var(comp_array, ddof=1)) if n_comp > 1 else 0.0
    if n_base > 1 and n_comp > 1:
        rel_var = (comp_var / n_comp) / (comp_mean ** 2) + (base_var / n_base) / (base_mean ** 2)
        se = ratio * np.sqrt(rel_var)
        t_val = float(stats.t.ppf(0.975, min(n_base, n_comp) - 1))
        ci = se * t_val
    else:
        ci = 0.0

    return ratio, ci, base_mean, comp_mean, n_base, n_comp


# =========================
# プロット補助
# =========================

def integer_xticks(ax, ticks: List[int]) -> None:
    """x 軸を整数 tick に固定し、ラベルは出さない。"""
    if FixedLocator is None:
        return
    ax.xaxis.set_major_locator(FixedLocator(sorted(ticks)))
    ax.set_xlim(min(ticks) - 0.5, max(ticks) + 0.5)
    ax.set_xticklabels([])
    ax.tick_params(axis='x', length=0)


def save_fig(fig, path: str, dpi: int = 150, tight: bool = True):
    if tight:
        fig.savefig(path, dpi=dpi, bbox_inches="tight")
    else:
        fig.savefig(path, dpi=dpi)
    plt.close(fig)


# =========================
# Markdown 出力補助
# =========================

def write_mutants_markdown(md_path: str,
                           header: str,
                           latest_dirname: str,
                           filter_note: str,
                           cases: List[Tuple[int, float, float, float, float, int, int, Dict[str, Any]]]):
    """
    cases: (n, ratio, ci, base_mean, comp_mean, n_base, n_comp, code_dict)
    """
    with open(md_path, "w", encoding="utf-8") as md:
        md.write(f"# {header}\n\n")
        md.write(f"- Log dir: `{latest_dirname}`\n")
        md.write(f"- Filter: {filter_note}\n\n")

        if not cases:
            md.write("_No mutants matched the filter._\n")
            return

        md.write("## Summary\n\n")
        md.write(f"| mutant_index | {comp}/{base} ratio | 95% CI ± | {base} mean (s) | {comp} mean (s) | n{base} | n{comp} |\n")
        md.write("|---:|---:|---:|---:|---:|---:|---:|\n")
        for (n, r, ci, bm, cm, nb, nc, _) in cases:
            md.write(f"| {n} | {r:.6g} | {ci:.3g} | {bm:.6g} | {cm:.6g} | {nb} | {nc} |\n")
        md.write("\n")

        for (n, r, ci, bm, cm, nb, nc, code) in cases:
            md.write(f"## Mutant {n} — {comp}/{base}: {r:.6g} (±{ci:.3g})\n\n")
            am = code.get("after_mutate") or ""
            ai = code.get("after_insertion") or ""
            at = code.get("after_translation")
            md.write("**after_mutate**:\n\n```ocaml\n")
            md.write(am)
            md.write("\n```\n\n")

            md.write(f"**after_insertion ({base})**:\n\n```ocaml\n")
            md.write(ai)
            md.write("\n```\n\n")

            if at:
                md.write(f"**after_translation ({comp})**:\n\n```ocaml\n")
                md.write(at)
                md.write("\n```\n\n")

# =========================
# 異常値検出
# =========================

def _safe_log_ratio(comp_prom, base_prom, eps=None):
    if base_prom is None or not np.isfinite(base_prom) or base_prom <= 0:
        return None
    if comp_prom is None or not np.isfinite(comp_prom):
        return None
    r = comp_prom / base_prom
    # 後で eps でまとめてクリップするのでそのまま返す
    return r

def robust_left_outliers_log10(ratios, k=3.5, min_n=4):
    """
    ratios: 正の比（S/C promoted bytes）の配列（None は除外）
    戻り値: (indices_outliers, stats_dict)
    """
    vals = np.array([r for r in ratios if r is not None and r > 0.0], dtype=float)
    if len(vals) < min_n:
        return [], {"reason": "too_few_samples", "n": len(vals)}

    # ε でクリップ（S=0 のような値を受け入れる）
    pos = vals[vals > 0]
    eps = np.min(pos) * 0.5 if np.any(pos > 0) else 1e-300
    y = np.log10(np.maximum(vals, eps))

    m = np.median(y)
    mad = np.median(np.abs(y - m))
    if mad <= 1e-12:
        # フォールバック: IQR フェンス（強い外れ値）
        q1, q3 = np.percentile(y, [25, 75])
        iqr = max(q3 - q1, 1e-12)
        fence = q1 - 3.0 * iqr
        mask = (y <= fence)
        idx = np.where(mask)[0].tolist()
        return idx, {"method": "iqr", "q1": q1, "q3": q3, "fence": fence, "n": len(vals)}

    z = 0.6745 * (y - m) / mad
    mask = (z <= -abs(k))
    idx = np.where(mask)[0].tolist()
    return idx, {"method": "mad", "median": m, "mad": mad, "k": k, "n": len(vals)}