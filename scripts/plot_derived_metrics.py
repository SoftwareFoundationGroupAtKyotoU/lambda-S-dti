# plot_derived_metrics.py
#
# ベンチマークログ（logs/<timestamp>/*.jsonl）に既に記録されているカウンタから、
# 追加計測なしで求まる派生指標を集計・プロットし、Markdown レポートにまとめる。
#
#   1. cache_hit_rate    : compose_cached / compose（hash-consing の実効果）
#   2. compose_depth     : compose_max_depth の分布（合成の深さが有界に留まるか）
#   3. time_per_cast     : mean(times_sec) / cast（cast 数の桁違いを正規化したコスト）
#   4. coerce_breakdown  : coerce_* の構成比（どの種類の coercion 適用が支配的か）
#   5. dti_rate          : sum(dti_*) / cast（型変数の動的具体化の発生率）
#   6. elasticity        : ln(time) を Dyn 化スロット数に回帰した傾き（1スロットあたり何%遅くなるか）
#                          + 非線形性（2次項の ΔBIC、前半/後半の傾き比）
#   7. mem_vs_cast       : mem（GC_get_total_bytes の差分）と cast の相関
#
# 動的度の横軸は mutant_index ではなく「Dyn 化スロット数」。mutate.ml は選ばれたスロットの
# 注釈を丸ごと TyDyn に置き換えるので、untyped ソースでは after_mutate 中の '?' の数が
# そのままスロット数になる（mutant 1 = 0 = 最も静的）。typed ソース（mono_copies で1スロットが
# 複数の '?' になる）と grift（1スロットが複数の 'Dyn' になる）は数え方がずれるので、
# 同じ mutant_index（全モードで同じスロット選択を指す）の untyped 側のスロット数に揃える
# （align_slots）。untyped 側のログがないベンチだけ、各モード自身の数え方
# （benchviz.dynamized_slots）のまま残す。
#
# ファイル名の分解・レコード読み込み・実行時間の定義（mean_time = times_sec の平均）は
# benchviz の共通関数を使い、他のスクリプトと揃えてある。
# 出力: <date_dir>/derived_metrics[_static]/<metric>/*.png と derived_metrics_report.md, per_mutant.csv

import os
import csv
import math
import statistics
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

import numpy as np
import matplotlib.pyplot as plt
from scipy import stats

from benchviz import (
    latest_date_dir, ensure_dir, save_fig, setup_plot_style, get_plot_style, format_comp_label,
    parse_log_filename, iter_log_records, mean_time, dynamized_slots,
)

COERCE_KEYS = ["coerce_id", "coerce_fun", "coerce_list", "coerce_tuple",
               "coerce_ref", "coerce_array", "coerce_tv", "coerce_bot"]
DTI_KEYS = ["dti_fn", "dti_li", "dti_tp", "dti_rf", "dti_ar",
            "dti_int", "dti_bool", "dti_float", "dti_unit"]

# coerce_* の構成比用の固定カテゴリ色（順序固定、COERCE_KEYS と1対1）
COERCE_COLORS = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100",
                 "#e87ba4", "#008300", "#4a3aa7", "#e34948"]


# =========================
# 読み込み
# =========================

@dataclass
class Row:
    bench: str
    mode: str
    idx: int
    slots: int
    time: Optional[float]  # mean(times_sec)（benchviz.mean_time）。未計測なら None
    rec: dict

    def num(self, key: str) -> Optional[float]:
        v = self.rec.get(key)
        if isinstance(v, bool) or not isinstance(v, (int, float)):
            return None
        return float(v)

    def total(self, keys: List[str]) -> Optional[float]:
        vals = [self.num(k) for k in keys]
        if all(v is None for v in vals):
            return None
        return sum(v for v in vals if v is not None)


Data = Dict[str, Dict[str, List[Row]]]  # bench -> mode -> rows


def collect(date_dir: str, static: bool) -> Data:
    data: Data = {}
    for fname in sorted(os.listdir(date_dir)):
        parsed = parse_log_filename(fname)
        if parsed is None:
            continue
        mode, bench, is_static = parsed
        if is_static != static:
            continue
        rows = [Row(bench, mode, int(d["mutant_index"]), dynamized_slots(d.get("after_mutate")),
                    mean_time(d.get("times_sec")), d)
                for d in iter_log_records(os.path.join(date_dir, fname))]
        if rows:
            data.setdefault(bench, {})[mode] = sorted(rows, key=lambda r: r.idx)
    for mode_rows in data.values():
        align_slots(mode_rows)
    return data


SLOT_REFERENCE_MODE = "untypedALHMT"


def align_slots(mode_rows: Dict[str, List["Row"]]) -> None:
    """typed / grift の行のスロット数を、同じ mutant_index の untyped 側の値で置き換える。
    参照は untypedALHMT、なければ他の untyped モード（どれも同じソースなので値は同じ）。"""
    ref_mode = SLOT_REFERENCE_MODE if SLOT_REFERENCE_MODE in mode_rows else next(
        (m for m in sorted(mode_rows) if m.startswith("untyped")), None)
    if ref_mode is None:
        return
    ref = {r.idx: r.slots for r in mode_rows[ref_mode]}
    for mode, rows in mode_rows.items():
        if mode.startswith("untyped"):
            continue
        for r in rows:
            if r.idx in ref:
                r.slots = ref[r.idx]


# =========================
# 指標の定義
# =========================

def _ratio(a: Optional[float], b: Optional[float]) -> Optional[float]:
    if a is None or b is None or b <= 0:
        return None
    return a / b


def hit_rate(r: Row) -> Optional[float]:
    return _ratio(r.num("compose_cached"), r.num("compose"))


def max_depth(r: Row) -> Optional[float]:
    return r.num("compose_max_depth")


def ns_per_cast(r: Row) -> Optional[float]:
    v = _ratio(r.time, r.num("cast"))
    return None if v is None else v * 1e9


def dti_rate(r: Row) -> Optional[float]:
    return _ratio(r.total(DTI_KEYS), r.num("cast"))


def most_dynamic(rows: List[Row], ok: Callable[[Row], bool]) -> List[Row]:
    """ok を満たす行のうち、Dyn 化スロット数が最大のもの（同数なら全部）。"""
    cand = [r for r in rows if ok(r)]
    if not cand:
        return []
    m = max(r.slots for r in cand)
    return [r for r in cand if r.slots == m]


def pooled_ratio(rows: List[Row], num_keys: List[str], den_key: str) -> Optional[float]:
    """Σnum / Σden（mutant ごとの比の平均ではなく、総量の比）。"""
    n = [r.total(num_keys) for r in rows]
    d = [r.num(den_key) for r in rows]
    pairs = [(a, b) for a, b in zip(n, d) if a is not None and b is not None]
    den = sum(b for _, b in pairs)
    return sum(a for a, _ in pairs) / den if den > 0 else None


# =========================
# 回帰（指標6）と相関（指標7）
# =========================

@dataclass
class Elasticity:
    n: int
    levels: int
    max_slots: int
    slope: float          # d ln(time) / d slot
    slope_se: float
    pct_per_slot: float   # exp(slope) - 1
    pct_lo: float
    pct_hi: float
    r2_lin: float
    r2_quad: Optional[float]
    quad_coef: Optional[float]
    dbic: Optional[float]  # BIC(lin) - BIC(quad)。大きいほど2次項が必要
    early: Optional[float]  # 低 dynamism 側の傾き（レベル中央値ベース, ln/slot）
    late: Optional[float]
    observed_ratio: Optional[float]  # median(t @ max slots) / median(t @ 0 slots)
    shape: str
    coefs_lin: Tuple[float, float]
    coefs_quad: Optional[Tuple[float, float, float]]


def _r2(y: np.ndarray, yhat: np.ndarray) -> float:
    ss = float(np.sum((y - y.mean()) ** 2))
    return 1.0 - float(np.sum((y - yhat) ** 2)) / ss if ss > 0 else float("nan")


def _bic(y: np.ndarray, yhat: np.ndarray, k: int) -> float:
    n = len(y)
    rss = max(float(np.sum((y - yhat) ** 2)), 1e-300)
    return n * math.log(rss / n) + k * math.log(n)


def _level_slope(xs: List[int], ys: List[float]) -> Optional[float]:
    if len(xs) < 2:
        return None
    return float(np.polyfit(np.array(xs, float), np.array(ys, float), 1)[0])


def _shape(implied: float, early: Optional[float], late: Optional[float]) -> str:
    """前半/後半の傾き（ln/slot）から曲がり方を分類する。
    implied = 線形フィットが示す完全 Dyn 化時の変化率（exp(b*N) - 1）。"""
    if abs(implied) < 0.05:
        return "flat"
    if early is None or late is None:
        return "n/a (<3 levels)"
    if early > 0:
        r = late / early
        if r < -0.5:
            return "rise then fall"
        if r < 0.5:
            return "concave (saturating)"  # 後半の傾きが前半の半分未満（小さな下降=頭打ちも含む）
        return "convex (accelerating)" if r > 2.0 else "~linear"
    if late > 0:
        return "convex (flat/fall then rise)"
    return "decreasing"


def elasticity(rows: List[Row]) -> Optional[Elasticity]:
    pts = [(r.slots, r.time) for r in rows if r.time is not None and r.time > 0]
    if len(pts) < 3:
        return None
    x = np.array([p[0] for p in pts], float)
    y = np.log(np.array([p[1] for p in pts], float))
    levels = sorted(set(int(v) for v in x))
    if len(levels) < 2:
        return None

    lr = stats.linregress(x, y)
    b, se = float(lr.slope), float(lr.stderr)
    yhat_lin = lr.intercept + lr.slope * x
    r2_lin = _r2(y, yhat_lin)

    r2_quad = quad_coef = dbic = None
    coefs_quad = None
    if len(levels) >= 3 and len(pts) >= 4:
        c2, c1, c0 = np.polyfit(x, y, 2)
        yhat_quad = c0 + c1 * x + c2 * x * x
        r2_quad = _r2(y, yhat_quad)
        quad_coef = float(c2)
        coefs_quad = (float(c0), float(c1), float(c2))
        if len(pts) >= 6:
            dbic = _bic(y, yhat_lin, 2) - _bic(y, yhat_quad, 3)

    # 前半/後半の傾き: スロット数レベルごとの ln(time) 中央値に対して、
    # 下半分のレベルと上半分のレベルで別々に直線を当てる（レベル数が奇数なら中央を共有）
    lv_med = {lv: float(np.median(y[x == lv])) for lv in levels}
    k = len(levels)
    lower, upper = levels[: (k + 1) // 2], levels[k // 2:]
    early = late = None
    if k >= 3:
        early = _level_slope(lower, [lv_med[l] for l in lower])
        late = _level_slope(upper, [lv_med[l] for l in upper])

    observed = None
    if levels[0] == 0:
        observed = math.exp(lv_med[levels[-1]] - lv_med[0])

    max_slots = levels[-1]
    shape = _shape(math.exp(b * max_slots) - 1.0, early, late)
    if dbic is not None and dbic >= 6.0 and shape == "~linear":
        shape = "~linear (curvature by BIC)"
    if len(pts) < 8:
        shape += " [low n]"

    return Elasticity(
        n=len(pts), levels=k, max_slots=max_slots, slope=b, slope_se=se,
        pct_per_slot=math.expm1(b),
        pct_lo=math.expm1(b - 1.96 * se), pct_hi=math.expm1(b + 1.96 * se),
        r2_lin=r2_lin, r2_quad=r2_quad, quad_coef=quad_coef, dbic=dbic,
        early=early, late=late, observed_ratio=observed, shape=shape,
        coefs_lin=(float(lr.intercept), b), coefs_quad=coefs_quad)


@dataclass
class Correlation:
    n: int
    pearson_log: Optional[float]  # log10(mem) vs log10(cast)
    spearman: Optional[float]
    spearman_p: Optional[float]
    note: str


def mem_cast_corr(rows: List[Row]) -> Optional[Correlation]:
    pts = [(r.num("cast"), r.num("mem")) for r in rows]
    pts = [(c, m) for c, m in pts if c is not None and m is not None]
    if len(pts) < 3:
        return None
    c = np.array([p[0] for p in pts]); m = np.array([p[1] for p in pts])
    if np.all(c == c[0]) or np.all(m == m[0]):
        return Correlation(len(pts), None, None, None,
                           "cast constant" if np.all(c == c[0]) else "mem constant")
    sp = stats.spearmanr(c, m)
    pos = (c > 0) & (m > 0)
    pl = None
    if pos.sum() >= 3 and np.ptp(c[pos]) > 0 and np.ptp(m[pos]) > 0:
        pl = float(stats.pearsonr(np.log10(c[pos]), np.log10(m[pos]))[0])
    return Correlation(len(pts), pl, float(sp.correlation), float(sp.pvalue), "")


# =========================
# プロット補助
# =========================

def _modes(data: Data) -> List[str]:
    return sorted({m for md in data.values() for m in md})


def _styles(modes: List[str]) -> Dict[str, dict]:
    return {m: get_plot_style(m, i) for i, m in enumerate(modes)}


def grouped_barh(values: Dict[str, Dict[str, Optional[float]]], modes: List[str],
                 xlabel: str, title: str, path: str, log: bool = False,
                 err: Optional[Dict[str, Dict[str, Tuple[float, float]]]] = None,
                 xlim: Optional[Tuple[float, float]] = None, drop_all_zero: bool = False) -> bool:
    """ベンチマーク（行）× モード（色）の横棒。値が None のセルは描かない。
    log=True のとき 0 は描けないので棒の代わりに "0" と書く。"""
    benches = [b for b in sorted(values) if any(values[b].get(m) is not None for m in modes)]
    used = [m for m in modes if any(values[b].get(m) is not None for b in benches)]
    if drop_all_zero:  # 例: hash-off モードの hit rate は定義上 0 なので図から外す
        used = [m for m in used if any((values[b].get(m) or 0) != 0 for b in benches)]
    if not benches or not used:
        return False
    if log and not any((values[b].get(m) or 0) > 0 for b in benches for m in used):
        log = False  # 全部 0 なら log 軸は張れない（0 の棒が並ぶ linear 図にする）
    st = _styles(modes)
    h = 0.8 / len(used)
    fig, ax = plt.subplots(figsize=(9.0, min(16.0, max(3.0, 0.12 * len(benches) * len(used) + 1.5))))
    for j, m in enumerate(used):
        ys, xs, xerr = [], [], [[], []]
        for i, b in enumerate(benches):
            v = values[b].get(m)
            if v is None:
                continue
            y = i + (j - (len(used) - 1) / 2) * h
            if log and v <= 0:
                ax.text(0.0, y, " 0", transform=ax.get_yaxis_transform(), va="center", fontsize=8,
                        color="#555555")
                continue
            ys.append(y); xs.append(v)
            if err is not None:
                lo, hi = err[b][m]
                xerr[0].append(max(v - lo, 0.0)); xerr[1].append(max(hi - v, 0.0))
        ax.barh(ys, xs, height=h * 0.9, color=st[m]["color"], label=format_comp_label(m),
                xerr=xerr if err is not None and xs else None,
                error_kw={"elinewidth": 1, "capsize": 2, "ecolor": "#333333"})
    ax.set_yticks(range(len(benches)))
    ax.set_yticklabels(benches)
    ax.invert_yaxis()
    if log:
        ax.set_xscale("log")
    if xlim:
        ax.set_xlim(*xlim)
    ax.set_xlabel(xlabel)
    ax.set_title(title)
    ax.grid(True, axis="x", linestyle="--", alpha=0.3)
    ax.legend(loc="best", fontsize=8, frameon=True)
    ensure_dir(os.path.dirname(path))
    save_fig(fig, path)
    return True


def vs_slots(bench: str, mode_rows: Dict[str, List[Row]], fn: Callable[[Row], Optional[float]],
             ylabel: str, title: str, path: str, logy: bool = False,
             agg: Callable[[List[float]], float] = statistics.median, agg_label: str = "median") -> bool:
    """横軸 = Dyn 化スロット数。各 mutant を点、スロット数レベルごとの集約値を線で描く。"""
    modes = sorted(mode_rows)
    st = _styles(modes)
    fig, ax = plt.subplots(figsize=(8.0, 5.5))
    drawn = False
    n_modes = len(modes)
    for j, m in enumerate(modes):
        pts = [(r.slots, fn(r)) for r in mode_rows[m]]
        pts = [(s, v) for s, v in pts if v is not None and (not logy or v > 0)]
        if not pts:
            continue
        drawn = True
        off = (j - (n_modes - 1) / 2) * 0.08  # 同じスロット数の点がモード間で重ならないよう少しずらす
        ax.scatter([s + off for s, _ in pts], [v for _, v in pts], s=12, alpha=0.35,
                   color=st[m]["color"], marker=st[m]["marker"], linewidths=0)
        lv: Dict[int, List[float]] = {}
        for s, v in pts:
            lv.setdefault(s, []).append(v)
        xs = sorted(lv)
        ax.plot(xs, [agg(lv[s]) for s in xs], color=st[m]["color"], linewidth=2,
                marker=st[m]["marker"], markersize=5, label=f"{format_comp_label(m)} ({agg_label})")
    if not drawn:
        plt.close(fig)
        return False
    if logy:
        ax.set_yscale("log")
    ax.set_xlabel("Dynamized annotation slots ('?' count)")
    ax.set_ylabel(ylabel)
    ax.set_title(f"{bench}: {title}")
    ax.grid(True, linestyle="--", alpha=0.3)
    ax.legend(fontsize=8, frameon=True)
    ensure_dir(os.path.dirname(path))
    save_fig(fig, path)
    return True


# =========================
# 各指標
# =========================

def _fmt(v: Optional[float], f: str = "{:.3g}") -> str:
    return "–" if v is None or (isinstance(v, float) and math.isnan(v)) else f.format(v)


def md_table(header: List[str], rows: List[List[str]]) -> List[str]:
    out = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    out += ["| " + " | ".join(r) + " |" for r in rows]
    return out


def ratio_metric(data: Data, modes: List[str], out: str, name: str, fn: Callable[[Row], Optional[float]],
                 summary: Callable[[List[Row]], Optional[float]], ok: Callable[[Row], bool],
                 ylabel: str, title: str, log: bool, xlim=None, fmt="{:.3g}", drop_all_zero=False) -> List[str]:
    """指標 1/3/5 共通: 最も動的な mutant での集約値（横棒）+ ベンチマーク毎の vs スロット数プロット。"""
    vals: Dict[str, Dict[str, Optional[float]]] = {}
    table = []
    for b, md in sorted(data.items()):
        vals[b] = {}
        for m, rows in sorted(md.items()):
            top = most_dynamic(rows, ok)
            v = summary(top) if top else None
            vals[b][m] = v
            all_v = [x for x in (fn(r) for r in rows) if x is not None]
            table.append([b, m, _fmt(v, fmt), str(top[0].slots) if top else "–", str(len(top)),
                          _fmt(min(all_v) if all_v else None, fmt), _fmt(max(all_v) if all_v else None, fmt)])
        vs_slots(b, md, fn, ylabel, title, os.path.join(out, name, f"{b}.png"), logy=log)
    grouped_barh(vals, modes, f"{ylabel} (most dynamic mutants)", f"{title} at the most dynamic mutants",
                 os.path.join(out, name, "_summary.png"), log=log, xlim=xlim, drop_all_zero=drop_all_zero)
    return md_table(["benchmark", "mode", "most-dynamic", "slots", "#mutants", "min (all)", "max (all)"], table)


def metric_depth(data: Data, modes: List[str], out: str) -> List[str]:
    st = _styles(modes)
    benches = sorted(b for b, md in data.items() if any(max_depth(r) is not None for rs in md.values() for r in rs))
    fig, ax = plt.subplots(figsize=(max(9.0, 0.6 * len(benches) + 2), 5.5))
    w = 0.8 / max(1, len(modes))
    table = []
    labeled = set()
    for b in sorted(set(data) - set(benches)):
        table.append([b, "*", "0", "–", "–", "–", "(no compose_max_depth recorded)", "–"])
    for i, b in enumerate(benches):
        for j, m in enumerate(modes):
            rows = data[b].get(m)
            if not rows:
                continue
            d = [int(v) for v in (max_depth(r) for r in rows) if v is not None]
            if not d:
                continue
            x = i + (j - (len(modes) - 1) / 2) * w
            cnt: Dict[int, int] = {}
            for v in d:
                cnt[v] = cnt.get(v, 0) + 1
            # 点の面積 = その深さを取った mutant の割合
            ax.scatter([x] * len(cnt), list(cnt), s=[8 + 160 * c / len(d) for c in cnt.values()],
                       color=st[m]["color"], marker=st[m]["marker"], alpha=0.8, linewidths=0,
                       label=None if m in labeled else format_comp_label(m))
            labeled.add(m)
            # 相関（スロット数 vs 深さ）: 発散するなら正に強く出る
            sl = [r.slots for r in rows if max_depth(r) is not None]
            rho = None
            if len(set(sl)) > 1 and len(set(d)) > 1:
                rho = float(stats.spearmanr(sl, d).correlation)
            table.append([b, m, str(len(d)), str(min(d)), _fmt(statistics.median(d)), str(max(d)),
                          " ".join(f"{k}:{v}" for k, v in sorted(cnt.items())), _fmt(rho, "{:+.2f}")])
        vs_slots(b, data[b], max_depth, "compose_max_depth", "compose_max_depth vs dynamism",
                 os.path.join(out, "compose_depth", f"{b}.png"), agg=max, agg_label="max")
    if table:
        ax.set_xticks(range(len(benches)))
        ax.set_xticklabels(benches, rotation=45, ha="right")
        ax.set_ylabel("compose_max_depth")
        ax.set_title("Distribution of compose_max_depth over all mutants (dot area = share of mutants)")
        ax.yaxis.get_major_locator().set_params(integer=True)
        ax.grid(True, axis="y", linestyle="--", alpha=0.3)
        ax.legend(fontsize=8, frameon=True, markerscale=0.8)
        ensure_dir(os.path.join(out, "compose_depth"))
        save_fig(fig, os.path.join(out, "compose_depth", "_summary.png"))
    else:
        plt.close(fig)
    return md_table(["benchmark", "mode", "#mutants", "min", "median", "max", "depth:count",
                     "Spearman(slots, depth)"], table)


def metric_coerce(data: Data, modes: List[str], out: str) -> List[str]:
    table = []
    for m in modes:
        benches, fracs, totals = [], [], []
        for b in sorted(data):
            rows = data[b].get(m)
            if not rows:
                continue
            sums = [sum(v for v in (r.num(k) for r in rows) if v is not None) for k in COERCE_KEYS]
            tot = sum(sums)
            if tot <= 0:
                continue
            benches.append(b); totals.append(tot); fracs.append([s / tot for s in sums])
            dom = COERCE_KEYS[int(np.argmax(sums))].replace("coerce_", "")
            table.append([b, m, f"{tot:.3g}"] + [f"{100 * f:.1f}" for f in fracs[-1]] + [dom])
        if not benches:
            continue
        fig, ax = plt.subplots(figsize=(10.0, max(3.0, 0.4 * len(benches) + 1.8)))
        left = np.zeros(len(benches))
        for k, key in enumerate(COERCE_KEYS):
            w = np.array([f[k] for f in fracs])
            # 2px 相当の白い区切り線で隣接セグメントを分離
            ax.barh(range(len(benches)), w, left=left, color=COERCE_COLORS[k], height=0.7,
                    edgecolor="white", linewidth=1.0, label=key.replace("coerce_", ""))
            left += w
        for i, t in enumerate(totals):
            ax.text(1.01, i, f"{t:.2g}", va="center", fontsize=8, color="#333333")
        ax.set_yticks(range(len(benches)))
        ax.set_yticklabels(benches)
        ax.invert_yaxis()
        ax.set_xlim(0, 1)
        ax.set_xlabel("Share of coercion applications (summed over all mutants); right: total count")
        ax.set_title(f"coerce_* breakdown: {format_comp_label(m)}")
        ax.legend(ncol=8, fontsize=8, loc="upper center", bbox_to_anchor=(0.5, -0.12), frameon=False)
        ensure_dir(os.path.join(out, "coerce_breakdown"))
        save_fig(fig, os.path.join(out, "coerce_breakdown", f"{m}.png"))
    return md_table(["benchmark", "mode", "total"] + [k.replace("coerce_", "") + " %" for k in COERCE_KEYS]
                    + ["dominant"], table)


def metric_dti_tags(data: Data) -> List[str]:
    """DTI 発火のタグ別内訳（全 mutant 合計）。発火ゼロの組は省く。"""
    table = []
    for b, md in sorted(data.items()):
        for m, rows in sorted(md.items()):
            sums = [sum(v for v in (r.num(k) for r in rows) if v is not None) for k in DTI_KEYS]
            tot = sum(sums)
            if tot > 0:
                table.append([b, m, f"{tot:.3g}"] + [f"{100 * s / tot:.1f}" if s else "·" for s in sums])
    if not table:
        return ["(no DTI events recorded in any benchmark/mode)"]
    return md_table(["benchmark", "mode", "total DTI"] + [k.replace("dti_", "") + " %" for k in DTI_KEYS], table)


def metric_elasticity(data: Data, modes: List[str], out: str) -> List[str]:
    st = _styles(modes)
    vals: Dict[str, Dict[str, Optional[float]]] = {}
    errs: Dict[str, Dict[str, Tuple[float, float]]] = {}
    table = []
    for b, md in sorted(data.items()):
        vals[b], errs[b] = {}, {}
        fig, ax = plt.subplots(figsize=(8.0, 5.5))
        drawn = False
        for j, m in enumerate(sorted(md)):
            rows = md[m]
            e = elasticity(rows)
            if e is None:
                continue
            if e.n >= 8:  # low-n（evenodd/fib 等の4 mutant）は CI が桁違いに広く軸を潰すので表のみ
                vals[b][m] = 100 * e.pct_per_slot
                errs[b][m] = (100 * e.pct_lo, 100 * e.pct_hi)
            table.append([b, m, str(e.n), str(e.max_slots), f"{100 * e.pct_per_slot:+.2f}",
                          f"[{100 * e.pct_lo:+.2f}, {100 * e.pct_hi:+.2f}]", _fmt(e.r2_lin, "{:.2f}"),
                          _fmt(e.r2_quad, "{:.2f}"), _fmt(e.dbic, "{:+.1f}"),
                          _fmt(None if e.early is None else 100 * math.expm1(e.early), "{:+.2f}"),
                          _fmt(None if e.late is None else 100 * math.expm1(e.late), "{:+.2f}"),
                          _fmt(e.observed_ratio, "{:.2f}x"), f"{math.exp(e.slope * e.max_slots):.2f}x",
                          e.shape])
            # 図: 完全静的 mutant の中央値を 1 とした相対時間（log 軸）+ 線形/2次フィット
            base = math.exp(e.coefs_lin[0]) if e.observed_ratio is None else \
                statistics.median([r.time for r in rows if r.slots == 0 and r.time])
            pts = [(r.slots, r.time / base) for r in rows if r.time]
            off = (j - (len(md) - 1) / 2) * 0.08
            ax.scatter([s + off for s, _ in pts], [v for _, v in pts], s=12, alpha=0.35,
                       color=st[m]["color"], marker=st[m]["marker"], linewidths=0)
            xs = np.linspace(0, e.max_slots, 100)
            lb = math.log(base)
            ax.plot(xs, np.exp(e.coefs_lin[0] + e.coefs_lin[1] * xs - lb), color=st[m]["color"], linewidth=2,
                    label=f"{format_comp_label(m)}: {100 * e.pct_per_slot:+.1f}%/slot, {e.shape}")
            if e.coefs_quad is not None:
                c0, c1, c2 = e.coefs_quad
                ax.plot(xs, np.exp(c0 + c1 * xs + c2 * xs * xs - lb), color=st[m]["color"],
                        linewidth=1.2, linestyle="--")
            drawn = True
        if drawn:
            ax.set_yscale("log")
            ax.set_xlabel("Dynamized annotation slots ('?' count)")
            ax.set_ylabel("Execution time relative to fully static mutant")
            ax.set_title(f"{b}: log-linear fit (solid) vs quadratic (dashed)")
            ax.grid(True, linestyle="--", alpha=0.3)
            ax.legend(fontsize=7, frameon=True)
            ensure_dir(os.path.join(out, "elasticity"))
            save_fig(fig, os.path.join(out, "elasticity", f"{b}.png"))
        else:
            plt.close(fig)
    grouped_barh(vals, modes, "Slowdown per dynamized slot (%), 95% CI", "Elasticity of execution time w.r.t. dynamism (n ≥ 8 mutants)",
                 os.path.join(out, "elasticity", "_summary.png"), err=errs)
    if not table:
        return ["(not computable: every benchmark/mode has fewer than 2 distinct slot counts with timings — "
                "e.g. the `_fs` logs contain only the fully static mutant)"]
    return md_table(["benchmark", "mode", "n", "max slots", "%/slot", "95% CI", "R² lin", "R² quad",
                     "ΔBIC", "early %/slot", "late %/slot", "observed max/0", "fit max/0", "shape"], table)


def metric_mem_cast(data: Data, modes: List[str], out: str) -> List[str]:
    st = _styles(modes)
    vals: Dict[str, Dict[str, Optional[float]]] = {}
    table = []
    for b, md in sorted(data.items()):
        vals[b] = {}
        fig, ax = plt.subplots(figsize=(8.0, 5.5))
        drawn = False
        for m in sorted(md):
            c = mem_cast_corr(md[m])
            if c is None:
                continue
            vals[b][m] = c.spearman
            table.append([b, m, str(c.n), _fmt(c.spearman, "{:+.2f}"), _fmt(c.spearman_p, "{:.1e}"),
                          _fmt(c.pearson_log, "{:+.2f}"), c.note])
            pts = [(r.num("cast"), r.num("mem")) for r in md[m]]
            pts = [(x, y) for x, y in pts if x and y and x > 0 and y > 0]
            if pts:
                lbl = f"{format_comp_label(m)} (ρ={_fmt(c.spearman, '{:+.2f}')})"
                ax.scatter([p[0] for p in pts], [p[1] for p in pts], s=14, alpha=0.5,
                           color=st[m]["color"], marker=st[m]["marker"], linewidths=0, label=lbl)
                drawn = True
        if drawn:
            ax.set_xscale("log"); ax.set_yscale("log")
            ax.set_xlabel("cast (count)")
            ax.set_ylabel("mem (bytes allocated, GC_get_total_bytes delta)")
            ax.set_title(f"{b}: allocation vs casts per mutant")
            ax.grid(True, linestyle="--", alpha=0.3)
            ax.legend(fontsize=8, frameon=True)
            ensure_dir(os.path.join(out, "mem_vs_cast"))
            save_fig(fig, os.path.join(out, "mem_vs_cast", f"{b}.png"))
        else:
            plt.close(fig)
    grouped_barh(vals, modes, "Spearman ρ (mem, cast) over mutants", "Correlation between allocation and casts",
                 os.path.join(out, "mem_vs_cast", "_summary.png"), xlim=(-1.05, 1.05))
    return md_table(["benchmark", "mode", "n", "Spearman ρ", "p", "Pearson r (log-log)", "note"], table)


# =========================
# CSV / レポート
# =========================

def write_csv(data: Data, path: str) -> None:
    cols = ["benchmark", "mode", "mutant_index", "slots", "mean_time_sec", "cast", "compose", "compose_cached",
            "cache_hit_rate", "compose_max_depth", "ns_per_cast", "dti_total", "dti_rate", "mem"] + COERCE_KEYS
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(cols)
        for b, md in sorted(data.items()):
            for m, rows in sorted(md.items()):
                for r in rows:
                    w.writerow([b, m, r.idx, r.slots, r.time, r.num("cast"), r.num("compose"),
                                r.num("compose_cached"), hit_rate(r), max_depth(r), ns_per_cast(r),
                                r.total(DTI_KEYS), dti_rate(r), r.num("mem")] + [r.num(k) for k in COERCE_KEYS])


def run(date_dir: str, static: bool = False) -> int:
    data = collect(date_dir, static=static)
    if not data:
        print(f"[plot_derived_metrics] no data found in {date_dir} (static={static})")
        return 0
    out = os.path.join(date_dir, "derived_metrics" + ("_static" if static else ""))
    ensure_dir(out)
    modes = _modes(data)

    rep: List[str] = [f"# Derived metrics ({os.path.basename(date_dir)}{', static' if static else ''})", "",
                      "Dynamism = number of dynamized annotation slots (`?` count in the untyped "
                      "mutant's `after_mutate`; typed and GRIFT rows use the untyped count of the same "
                      "`mutant_index`). Execution time of a mutant = mean of its `times_sec`. "
                      "\"Most dynamic\" = the mutants with the largest slot count among those with the "
                      "required counters (ties are pooled).", ""]

    rep += ["## 1. Cache hit rate (compose_cached / compose)", "",
            "Most-dynamic value is pooled: Σcompose_cached / Σcompose. Modes with hashing off (`h`) are 0 by construction.", ""]
    rep += ratio_metric(data, modes, out, "cache_hit_rate", hit_rate,
                        lambda rs: pooled_ratio(rs, ["compose_cached"], "compose"),
                        lambda r: (r.num("compose") or 0) > 0,
                        "compose_cached / compose", "cache hit rate", log=False, xlim=(0, 1.05), drop_all_zero=True)

    rep += ["", "## 2. compose_max_depth", "",
            "A positive Spearman correlation with a growing max would indicate depth diverging with dynamism.", ""]
    rep += metric_depth(data, modes, out)

    rep += ["", "## 3. Time per cast (mean(times_sec) / cast, ns)", "",
            "Total run time divided by casts, so it includes non-cast work: an upper bound on per-cast cost, "
            "most meaningful where casts dominate. Most-dynamic value = median over the tied mutants.", ""]
    rep += ratio_metric(data, modes, out, "time_per_cast", ns_per_cast,
                        lambda rs: statistics.median([v for v in map(ns_per_cast, rs) if v is not None]),
                        lambda r: ns_per_cast(r) is not None,
                        "ns per cast", "time per cast", log=True)

    rep += ["", "## 4. coerce_* breakdown (% of all coercion applications, summed over all mutants)", ""]
    rep += metric_coerce(data, modes, out)

    rep += ["", "## 5. DTI rate (Σdti_* / cast)", "", "Most-dynamic value is pooled: Σdti / Σcast.", ""]
    rep += ratio_metric(data, modes, out, "dti_rate", dti_rate,
                        lambda rs: pooled_ratio(rs, DTI_KEYS, "cast"),
                        lambda r: (r.num("cast") or 0) > 0 and r.total(DTI_KEYS) is not None,
                        "DTI events / cast", "DTI rate", log=True)
    rep += ["", "### DTI events by tag", ""] + metric_dti_tags(data)

    rep += ["", "## 6. Elasticity of execution time w.r.t. dynamism", "",
            "OLS of ln(mean time) on slot count over all mutants; %/slot = exp(slope) − 1 (95% CI from the slope's SE). "
            "Non-linearity: ΔBIC = BIC(linear) − BIC(quadratic) (≥ 6: strong evidence for curvature; needs n ≥ 6), "
            "and early/late slopes fitted to per-level medians of the lower/upper half of slot levels. "
            "Shape (r = late/early, early > 0): r < −0.5 → rise then fall, r < 0.5 → concave (saturating), "
            "r > 2 → convex (accelerating), otherwise ~linear; `flat` when the fitted full-dynamism ratio is within ±5%; "
            "`[low n]` when fewer than 8 timed mutants. "
            "`observed max/0` is the two-point ratio used so far; `fit max/0` is what the linear fit implies.", ""]
    rep += metric_elasticity(data, modes, out)

    rep += ["", "## 7. mem vs cast", "",
            "Across mutants of one benchmark/mode. Both grow with dynamism, so a high ρ says the two move together, "
            "not that casts cause the allocation.", ""]
    rep += metric_mem_cast(data, modes, out)

    with open(os.path.join(out, "derived_metrics_report.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(rep) + "\n")
    write_csv(data, os.path.join(out, "per_mutant.csv"))
    print(f"[plot_derived_metrics] wrote plots, report and CSV for {len(data)} benchmarks to {out}")
    return len(data)


def main() -> None:
    setup_plot_style()
    latest, date_dir = latest_date_dir("logs")
    print(f"[plot_derived_metrics] using {date_dir}")
    run(date_dir, static=False)
    run(date_dir, static=True)


if __name__ == "__main__":
    main()
