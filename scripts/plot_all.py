
from benchviz import (
    latest_date_dir, check_pair_exists, TARGET_PAIRS
)

from plot_herman import plot_herman
from plot_relative import plot_relative
from plot_scattered import plot_scattered

def run_plots(base, comp, static, date_dir):
	"""
	1つのペア (base, comp) または (base, [comp1, comp2...]) に対してプロットを実行する。
	comp がリストの場合は、Hermanのみ「リスト全体」と「個別」の両方を実行し、
	他は「個別」のみ実行する。
	"""
	# ログの存在チェック
	# benchviz.check_pair_exists はリストにも対応済み
	if not check_pair_exists(date_dir, base, comp, static):
		print(f"Skipping: Missing logs for {base} or {comp} in {date_dir}")
		return

	if isinstance(comp, list):
		# === comp がリストの場合 (["ALC", "SLC"] など) ===
	
		# 1. Herman にはリスト全体を渡す (重ね合わせグラフの生成)
		plot_herman(base, comp, static)
		plot_relative(base, comp, static)
		plot_scattered(base, comp, static)

		# 2. リストの各要素について個別にプロットを実行
		for c in comp:
			# 個別 Herman (単体グラフの生成)
			plot_herman(base, c, static)
			plot_relative(base, c, static)
			plot_scattered(base, c, static)

	else:
		# === comp が単一の文字列の場合 ===
		plot_herman(base, comp, static)
		plot_relative(base, comp, static)
		plot_scattered(base, comp, static)

def main():
	latest_ts, date_dir = latest_date_dir("logs")

	# Non-static (_fs なし) のプロット
	print("=== Processing Non-Static Logs ===")
	for base, comp in TARGET_PAIRS:
		run_plots(base, comp, False, date_dir)

	print("\n=== Processing Static Logs ===")
	# Static (_fs あり) のプロット
	for base, comp in TARGET_PAIRS:
		run_plots(base, comp, True, date_dir)

if __name__ == "__main__":
    main()