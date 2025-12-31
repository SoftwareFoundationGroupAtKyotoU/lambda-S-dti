import sys, importlib, pathlib, re
reqs = [l.strip() for l in pathlib.Path("scripts/requirements.txt").read_text().splitlines()
        if l.strip() and not l.strip().startswith("#")]
miss = []
norm = lambda s: re.split(r"[<>=~!]", s, 1)[0].replace("-", "_")
for r in reqs:
    n = norm(r)
    try:
        importlib.import_module(n)
    except Exception:
        miss.append(r)
if miss:
    print("❌ Missing python packages (import failed):", ", ".join(miss))
    sys.exit(1)
print("✅ Python requirements OK")