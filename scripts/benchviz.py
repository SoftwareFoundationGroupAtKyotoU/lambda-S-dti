# benchviz.py
import os
import re
import json
from typing import Dict, Any, List, Tuple, Optional, Union
import math

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

# 旧命名（S/A x E/L x H/N x M/G の総当たり式）は bin/bench.ml が ablation 方式
# （ALHMT 基準値 + 単軸反転: --id_opt/--hash/--tvs_opt/--typed）に置き換わったため、
# 実際のログに出てくるモード文字列も変わった。過去ログとの互換のため残してはいるが、
# 現行の bin/bench.ml が出す jsonl は下の新命名側しかマッチしない。
# 旧命名（参考として残す。現行ログには存在しない）:
# TARGET_PAIRS = [
#     ("SLNM", ["ALHM", "SLHM", "ALNM"]),
#     ("SLHM", ["ALHM"]),
#     ("ALNM", ["ALHM"]),
#     ("GRIFTCM", ["ALHM"]),
#     ("GRIFTM", ["ALHM"]),
#     ("STATICENG", ["ALHM", "GRIFTCM", "GRIFTM"]),
# ]

# 新命名（ablation 方式, lib/bench/bench_target.ml の ablation_mode_str）。
# 基準値は untypedALHMT（Alt, Lazy, Hash-consing on, Monotonic, tvs_opt on）。
# 各 comp は基準値から1軸だけ反転させたもの:
#   untypedSLHMT  = id_opt off（A→S,       --id_opt）
#   untypedELHMT  = eager（L→E,             --eager）
#   untypedALhMT  = hash-consing off（H→h,  --hash）
#   untypedALHGT  = guarded（M→G,           --monotonic）
#   untypedALHMt  = tvs_opt off（T→t,       --tvs_opt）
#   typedALHMT    = typed/untyped 軸（untyped→typed ソースに差し替え, --typed）
#   untypedSTATICEhGT = 完全静的コンパイル（DTI/coercion機構なし）
# GRIFT 側（lib/bench/bench_grift.ml）: GRIFTLLVMM（LLVM backend）/ GRIFTCM（C backend）/ GRIFTCMS（C backend, --static）。
# mutant_index は ML 側と grift 側で同じスロット選択を指す。
TARGET_PAIRS = [ # (base, comp)。comp が全部揃っていないペアは plot_all 側でスキップされる
    ("untypedALHMT", ["untypedSLHMT", "untypedALhMT", "untypedALHMt"]),  # 4軸まとめて概観
    # ("untypedSLHMT", ["untypedALHMT"]),   # id_opt 効果
    # ("untypedELHMT", ["untypedALHMT"]),   # eager/lazy 効果
    # ("untypedALhMT", ["untypedALHMT"]),   # hash-consing 効果
    # ("untypedALHGT", ["untypedALHMT"]),   # guarded/monotonic 効果
    # ("untypedALHMt", ["untypedALHMT"]),   # tvs_opt 効果
    # ("typedALHMT", ["untypedALHMT"]),     # typed/untyped 効果
    ("typedALHMT", ["GRIFTCM", "untypedALHMT"]),        # GRIFT C backend との比較
    # ("GRIFTLLVMM", ["untypedALHMT"]),     # GRIFT LLVM backend（grift 既定）との比較
    ("untypedSTATICEhGT", ["untypedALHMT", "typedALHMT", "GRIFTCMS", "GRIFTCM"]),  # static実行時のみ有効（完全静的 vs 完全動的基準値）
]

STYLE_MAP = {
    # --- 旧命名（参考として残す） ---
    # "SLNM":      {"color": "#1f77b4", "marker": "o"},  # 丸
    # "SLNG":     {"color": "#aec7e8", "marker": "s"},  # 四角
    # "SLHM":      {"color": "#17becf", "marker": "^"},  # 上三角
    # "SLHG":     {"color": "#9edae5", "marker": "v"},  # 下三角
    # "ALNM":      {"color": "#ff7f0e", "marker": "D"},  # ダイヤ（大）
    # "ALNG":     {"color": "#ffbb78", "marker": "d"},  # ダイヤ（小）
    # "ALHM":      {"color": "#d62728", "marker": "<"},  # 左三角
    # "ALHG":     {"color": "#ff9896", "marker": ">"},  # 右三角
    # "GRIFT":    {"color": "#2ca02c", "marker": "P"},  # プラス（太）
    # "GRIFTC":   {"color": "#9467bd", "marker": "X"},  # バツ（太）
    # "GRIFTM":   {"color": "#e377c2", "marker": "*"},  # スター（旧名。現 GRIFTLLVMM）
    # "STATICENG": {"color": "#7f7f7f", "marker": "h"},  # 六角形

    # --- 新命名（ablation 方式）。全プロット種別（herman/relative/scattered/
    #     metric/compare/stacked_time/derived_metrics）で共通してこの色を使う ---
    "untypedALHMT":      {"color": "#d62728", "marker": "<"},  # 基準値（旧ALHM相当）
    "untypedSLHMT":      {"color": "#1f77b4", "marker": "o"},  # id_opt off（旧SLHM相当）
    "untypedELHMT":      {"color": "#17becf", "marker": "^"},  # eager
    "untypedALhMT":      {"color": "#ff7f0e", "marker": "D"},  # hash off（旧ALNM相当）
    "untypedALHGT":      {"color": "#8c564b", "marker": "v"},  # guarded
    "untypedALHMt":      {"color": "#2ca02c", "marker": "P"},  # tvs_opt off
    "typedALHMT":        {"color": "#9467bd", "marker": "X"},  # typed軸
    "untypedSTATICEhGT": {"color": "#7f7f7f", "marker": "h"},  # 完全静的
    "GRIFTCM":           {"color": "#20b2aa", "marker": "8"},  # 八角形に変更
    "GRIFTCMS":          {"color": "#bcbd22", "marker": "s"},  # GRIFT C backend --static
    "GRIFTLLVMM":        {"color": "#e377c2", "marker": "*"},  # GRIFT LLVM backend
}

# =========================
# 設定まわり
# =========================
def format_comp_label(name: str) -> str:
    """
    SLHなどの文字列を論文用語に変換する。
    1文字目: S(Id-Opt ON), A(Id-Opt OFF)
    3文字目: H(HashCons ON), N(HashCons OFF)
    ※2文字目(L等)は無視する。
    """
    # if len(name) == 4:
    #     # id_opt = "ON" if name[0].upper() == 'S' else "OFF"
    #     hc_opt = "ON" if name[2].upper() == 'H' else "OFF"
    #     return f"Gradti (HashCons: {hc_opt})"
    # if name == "STATICEN"
    # if name == "SLH":
    #     return "Polymorphic"
    #     # return "Gradti"
    # if name == "ALN":
    #     return "Molymorphic"
    # if name == "GRIFTC":
    #     return "Grift (C backend)"
    return name

# プロット対象のベンチマークとその表示順（lib/bench/bench_config.ml の
# grift_benchmarks → gtp_benchmarks → originals の順に揃える。同ファイルで
# コメントアウトされている church-2/church-4/sieve 等は含めない）。
# ログのファイル名分解（parse_log_filename）、get_config の "target_benchmarks"、
# plot_relative.plot_static_summary の横軸の並びがすべてこれを参照する。
BENCHMARK_ORDER = [
    "array", "blacksholes", "fft", "matmult", "n_body", "quicksort", "ray", "tak",
    "fsm",
    "church-65536", "evenodd", "fib", "loop",
    "fold", "incsum", "map", "mklist", "zipwith",
]

def get_config(base: str, comp: List[str], static: bool) -> Dict[str, Any]:
    """baseとcompを受け取って、そのペア専用の設定辞書を返す"""
    comp_label = "|".join(comp)

    return {
        "log_root": "logs",
        "static": static,
        "target_benchmarks": list(BENCHMARK_ORDER),
        # 相対グラフ
        "relative": {
            "outdir": "relative",
            "xlabel": "Mutant index (ordered by number of dynamized slots)",
            "xlabel_sorted": "Mutants (sorted by relative time)",
            "ylabel": f"Execution time relative to {base}",
            "title_prefix": "Relative performance",
            "zigzag_tiers": 10,
            "zigzag_fontsize": 5
        },
        # 散布グラフ
        "scattered": {
            "outdir": "scattered",
            "xlabel": "Mutant index (ordered by number of dynamized slots)",
            "ylabel": "Execution time (s, mean with 95% CI)",
            "title_prefix": "Execution time"
        },
        # Herman
        "herman": {
            "outdir": "herman",
            "mad_k": 1,
            "min_n": 2,
            "xlabel": "Mutant index (ordered by number of dynamized slots)",
            "ylabel": f"Execution time relative to {base}",
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

def load_config(base: str, comp: List[str], static: bool, path: str = "benchviz.config.json") -> Dict[str, Any]:
    """外部 JSON を読み込み、デフォルトとマージして返す。読み込んだ有効設定を標準出力に表示する。"""
    cfg = get_config(base, comp, static)  # 既定ベース
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

def check_pair_exists(log_dir: str, base: str, comp: Union[str, List[str]], static: bool) -> bool:
    """指定されたログディレクトリに base と comp（リストなら全部）のログが含まれているか確認"""
    comps = comp if isinstance(comp, list) else [comp]
    present = {parsed[0] for parsed in (parse_log_filename(f) for f in os.listdir(log_dir))
               if parsed is not None and parsed[2] == static}
    return base in present and all(c in present for c in comps)

def get_plot_style(comp_name: str, index: int) -> dict:
    """コンポーネント名から固定の色とマーカーを取得する"""
    if comp_name in STYLE_MAP:
        return STYLE_MAP[comp_name]
    
    # 未定義の場合はmatplotlibのデフォルトサイクルから取得
    if plt is None:
        return {"color": "black", "marker": "o"}
    
    fallback_colors = plt.rcParams['axes.prop_cycle'].by_key()['color']
    fallback_markers = ['o', 'h', 'D', '+', 'x']
    return {
        "color": fallback_colors[index % len(fallback_colors)],
        "marker": fallback_markers[index % len(fallback_markers)]
    }


# =========================
# 共通 I/O
# =========================

_TIMESTAMP_DIR = re.compile(r"\d{8}-\d{2}:\d{2}:\d{2}")


def latest_date_dir(log_root: str) -> Tuple[str, str]:
    """既定では logs/ 以下で辞書順（=時系列）最新のディレクトリを使う。
    複数人/複数セッションが同じ logs/ を共有していると、他セッションが後から
    作ったディレクトリの方が「最新」判定されてしまうことがあるため、
    環境変数 BENCH_LOG_DIR でディレクトリ名を明示指定できるようにしてある
    （例: BENCH_LOG_DIR=20260923-10:33:53 make plot）。"""
    override = os.environ.get("BENCH_LOG_DIR")
    if override:
        path = os.path.join(log_root, override)
        if not os.path.isdir(path):
            raise SystemExit(f"BENCH_LOG_DIR={override!r} not found under '{log_root}/'.")
        return override, path

    # 名前を付け直したディレクトリ（例: array-quicksort-tak-church-loop）は英字が数字より
    # 辞書順で後ろに来て常に「最新」になってしまうので、自動選択はタイムスタンプ名だけに限る。
    # 名前付きのものは BENCH_LOG_DIR で指定する。
    dates = [d for d in os.listdir(log_root)
             if os.path.isdir(os.path.join(log_root, d)) and _TIMESTAMP_DIR.fullmatch(d)]
    if not dates:
        raise SystemExit(f"No timestamped log directories found under '{log_root}/' "
                         f"(set BENCH_LOG_DIR to use a named one).")
    latest = max(dates)  # "YYYYMMDD-HH:MM:SS" は辞書順=時系列
    return latest, os.path.join(log_root, latest)


def ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)


# ---- ログ読み込みの共通部品（全スクリプトがこれを使う） ----

LOG_EXTENSIONS = (".jsonl", ".json")
_BENCHMARKS_BY_LEN = sorted(BENCHMARK_ORDER, key=len, reverse=True)


def parse_log_filename(fname: str, benchmarks: Optional[List[str]] = None) -> Optional[Tuple[str, str, bool]]:
    """"<mode>_<benchmark>[_fs].json(l)" を (mode, benchmark, is_static) に分解する。
    "n_body" のようにベンチマーク名自体が '_' を含むので、既知のベンチマーク名
    （既定は BENCHMARK_ORDER）への末尾一致で判定する（長い名前から試す）。
    マッチしなければ None。"""
    ext = next((e for e in LOG_EXTENSIONS if fname.endswith(e)), None)
    if ext is None:
        return None
    core = fname[: -len(ext)]
    is_static = core.endswith("_fs")
    if is_static:
        core = core[: -len("_fs")]
    names = _BENCHMARKS_BY_LEN if benchmarks is None else sorted(benchmarks, key=len, reverse=True)
    for bench in names:
        suffix = "_" + bench
        if core.endswith(suffix) and len(core) > len(suffix):
            return core[: -len(suffix)], bench, is_static
    return None


def iter_log_records(path: str):
    """jsonl（1行1 mutant）と json（{"mode", "file", "mutants": [...]}）の両方を読む。"""
    with open(path, "r", encoding="utf-8") as f:
        if path.endswith(".jsonl"):
            for line in f:
                line = line.strip()
                if line:
                    yield json.loads(line)
        else:
            top = json.load(f)
            for rec in top.get("mutants", []):
                rec.setdefault("mode", top.get("mode"))
                yield rec


def mean_time(samples: Any) -> Optional[float]:
    """1 mutant の代表実行時間 = times_sec の算術平均（Takikawa POPL'16 / Grift PLDI'19 と同じ）。
    空・非有限・平均が 0 以下（タイマ分解能未満で全部 0 など）なら None。
    全スクリプトの実行時間はこの関数（または同じ定義の ratio_with_delta_ci）を通す。"""
    if not isinstance(samples, list) or not samples:
        return None
    values = np.asarray(samples, dtype=float)
    if not np.all(np.isfinite(values)):
        return None
    mean = float(np.mean(values))
    return mean if mean > 0 else None


def dynamized_slots(after_mutate: Optional[str]) -> int:
    """mutant の動的度 = Dyn 化された注釈の数。ML 側は '?'、grift 側（S式）は 'Dyn'。"""
    text = after_mutate or ""
    if text.lstrip().startswith("("):
        return len(re.findall(r"\bDyn\b", text))
    return text.count("?")


_ALIGNMENT_WARNINGS: set = set()  # 同じ警告をプロットのたびに繰り返さない


def ingest_latest_as_map(base: str, comp: List[str], cfg: Dict[str, Any], extra_metrics: List[str] = None) -> Tuple[str, str, Dict[str, Dict[int, Dict[str, Any]]]]:
    """
    最新ログディレクトリの base / comp の（static なら *_fs の、そうでなければ非 _fs の）
    ログから、
      bench -> mutant_index -> {
        '<mode>_times': [...],            # mode ∈ {base} ∪ comp
        '<mode>_<metric>': value|None,    # extra_metrics（例: "mem", "cast"）
        'after_mutate': str|None,         # base の mutant を優先
      }
    の辞書を返す。static かどうかは cfg["static"] で判定する。
    """
    target_benchmarks = cfg["target_benchmarks"]
    modes = [base] + [c for c in comp if c != base]
    extra_metrics = extra_metrics or []

    latest, date_dir = latest_date_dir(cfg["log_root"])

    data_by_benchmark: Dict[str, Dict[int, Dict[str, Any]]] = {}

    def ensure_slot(bench: str, n: int) -> Dict[str, Any]:
        per_bench = data_by_benchmark.setdefault(bench, {})
        if n not in per_bench:
            slot: Dict[str, Any] = {"after_mutate": None}
            for mode in modes:
                slot[f"{mode}_times"] = []
                for m in extra_metrics:
                    slot[f"{mode}_{m}"] = None
            per_bench[n] = slot
        return per_bench[n]

    mutant_counts: Dict[Tuple[str, str], int] = {}  # (bench, mode) -> 最大 mutant_index
    for filename in sorted(os.listdir(date_dir)):
        parsed = parse_log_filename(filename, target_benchmarks)
        if parsed is None:
            continue
        mode, bench, is_static = parsed
        if mode not in modes or is_static != cfg["static"]:
            continue
        for obj in iter_log_records(os.path.join(date_dir, filename)):
            index = int(obj["mutant_index"])
            mutant_counts[(bench, mode)] = max(mutant_counts.get((bench, mode), 0), index)
            slot = ensure_slot(bench, index)
            times = obj.get("times_sec")
            if isinstance(times, list):
                slot[f"{mode}_times"].extend(times)
            # typedALHMT vs untypedALHMT のように base と comp で元プログラムが違う
            # ペアがあるので、after_mutate は base のものを優先する
            if obj.get("after_mutate") and (slot["after_mutate"] is None or mode == base):
                slot["after_mutate"] = obj["after_mutate"]
            for m in extra_metrics:
                if obj.get(m) is not None:
                    slot[f"{mode}_{m}"] = obj[m]

    # mutant_index で base と comp を突き合わせるので、両者の mutant 数（= スロット数から
    # 決まる列挙）が違うと同じ index が別のスロット選択を指してしまう（typedALHMT と
    # untypedALHMT で元プログラムのスロット数が違う church-65536 など）。その comp は
    # そのベンチマークでは比較対象から外す。
    for (bench, mode), count in sorted(mutant_counts.items()):
        base_count = mutant_counts.get((bench, base))
        if mode == base or base_count is None or count == base_count:
            continue
        warning = (f"[benchviz] {bench}: {mode} has {count} mutants but {base} has {base_count}; "
                   f"mutant_index does not align, so {mode} is excluded for {bench}")
        if warning not in _ALIGNMENT_WARNINGS:
            _ALIGNMENT_WARNINGS.add(warning)
            print(warning)
        for slot in data_by_benchmark[bench].values():
            slot[f"{mode}_times"] = []
            for m in extra_metrics:
                slot[f"{mode}_{m}"] = None

    return latest, date_dir, data_by_benchmark

def setup_plot_style():
    """論文用にフォントサイズやマーカーサイズを大きくし、見やすくする"""
    if plt is None: return
    plt.rcParams.update({
        'font.size': 14,          # 全体のベースサイズ
        'axes.titlesize': 15,     # タイトル
        'axes.labelsize': 14,     # 軸ラベル
        'xtick.labelsize': 13,    # X軸目盛り
        'ytick.labelsize': 13,    # Y軸目盛り
        'legend.fontsize': 12,    # 凡例
        'lines.markersize': 5,    # マーカー
        'lines.linewidth': 1.5    # 線の太さ
    })

# =========================
# プロット補助 (追記・共通化モジュール)
# =========================

def parse_comp_args(comp: Union[str, List[str]], static: bool) -> Tuple[List[str], str, str, bool]:
    """
    引数の正規化と共通変数の生成を行う。
    戻り値: (compsリスト, compラベル, fsサフィックス, 複数比較フラグ)
    """
    fs = "_fs" if static else ""
    if isinstance(comp, list):
        # 重複を順序保持で除去（TARGET_PAIRS に同じモードが2回入っていても
        # plot_data の dict 化と append ループで長さがズレて errorbar が落ちるのを防ぐ）
        comps = list(dict.fromkeys(comp))
        return comps, "|".join(comps), fs, True
    return [comp], comp, fs, False

def _binomial_boundaries_between(n_total: int) -> List[float]:
    """n_total が 2^n と仮定し、"区切りの縦線" を入れる位置を返す。"""
    if n_total <= 0:
        return []
    n = round(math.log2(n_total))
    if (1 << n) != n_total:
        n = int(math.log2(max(1, n_total)))
    cum = 0
    mids = []
    for k in range(n + 1):
        cum += math.comb(n, k)
        if cum < (1 << n):
            mids.append(cum + 0.5)
    return mids

def draw_binomial_boundaries(ax, n_total: int):
    """2^n の境界線（縦の点線）をグラフに描画する"""
    midlines = _binomial_boundaries_between(n_total)
    for x in midlines:
        ax.axvline(x=x, color='lightgray', linestyle=':', linewidth=0.9, zorder=0)

# タイトル・軸ラベル・凡例を消した図（論文でキャプションを別に付ける用）が欲しいときは
# BENCH_HIDE_PLOT_TEXTS=1 make plot のように指定する。既定は表示する。
HIDE_PLOT_TEXTS = os.environ.get("BENCH_HIDE_PLOT_TEXTS", "0") == "1"

def apply_decorations(ax, xlabel: str, ylabel: str, title: str):
    """タイトル、軸ラベル、凡例の描画を共通化し、フラグで一括ON/OFFする"""
    if not HIDE_PLOT_TEXTS:
        ax.set_xlabel(xlabel)
        ax.set_ylabel(ylabel)
        ax.set_title(title, pad=55)
        ax.legend(bbox_to_anchor=(0.5, 1.02), loc='lower center', ncol=2, 
                  frameon=True, borderaxespad=0., fontsize=11, handletextpad=0.5)

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

def write_mutants_markdown(base: str, 
                           comp: str,
                           md_path: str,
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
            md.write("**after_mutate**:\n\n```ocaml\n")
            md.write(am)
            md.write("\n```\n\n")

# =========================
# 異常値検出
# =========================

def robust_left_outliers_log10(ratios, k=3.5, min_n=4):
    """
    ratios: 正の比（comp/base の mem = GC 割当バイト数）の配列（None は除外）
    戻り値: (indices_outliers, stats_dict)
    """
    vals = np.array([r for r in ratios if r is not None and r > 0.0], dtype=float)
    if len(vals) < min_n:
        return [], {"reason": "too_few_samples", "n": len(vals)}

    # ε でクリップ（comp=0 のような値を受け入れる）
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