
from benchviz import (
    latest_date_dir, check_pair_exists, TARGET_PAIRS
)

from plot_herman import (
	plot_herman
)

from plot_relative import (
	plot_relative
)

from plot_scattered import (
	plot_scattered
)

def main():
	latest_ts, date_dir = latest_date_dir("logs")

	for base, comp in TARGET_PAIRS:
		if not check_pair_exists(date_dir, base, comp, False):
			print(f"Skipping: Missing logs for {base} or {comp} in {date_dir}")
			continue

		plot_herman(base, comp, False)
		plot_relative(base, comp, False)
		plot_scattered(base, comp, False)

	for base, comp in TARGET_PAIRS:
		if not check_pair_exists(date_dir, base, comp, True):
			print(f"Skipping: Missing logs for {base} or {comp} in {date_dir}")
			continue

		plot_herman(base, comp, True)
		plot_relative(base, comp, True)
		plot_scattered(base, comp, True)

if __name__ == "__main__":
    main()