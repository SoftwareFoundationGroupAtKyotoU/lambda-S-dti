#!/bin/bash
# 各ベンチマークについて、全 mutant × 全 mode（test/check_mutants.exe --dynamize --static が
# 展開する組み合わせ全部）の標準出力が、下記に人手で登録した正解値と一致するかを
# 確認する正当性テスト。compile_test/dotests.sh と同じ思想（run_test filename expected_output）
# だが、対象はベンチマークのソース＋mutation機構（lib/bench/*, lib/backend/builder.ml の
# Builder.build_run_bench_check）を、test/check_mutants.ml の専用ハーネス経由で確認する。
#
# 何も標準出力しないベンチ（church-2/church-4/fold/fold-mono/map/map-mono/mklist/
# zipwith/zipwith-mono）は比較対象がないため対象外。
#
# 使用法: 有効な opam switch 上で実行すること（`eval $(opam env)` 済み、または
#         `opam exec -- ./compile_test/mutation_test.sh`）。

set -u

SELF="$(readlink -f "$0")"
ROOT="$(dirname "$(dirname "$SELF")")"
cd "$ROOT"

BIN="_build/default/test/check_mutants.exe"
if [ ! -x "$BIN" ]; then
  echo "building test/check_mutants.exe ..."
  dune build test/check_mutants.exe || exit 1
fi

# target => samples/input/<target>.txt（dynamize が使う）での正解の標準出力。
declare -A EXPECTED=(
  [tak]="9"
  [fib]="9227465"
  [church-65532]="65536"
  [evenodd]="true"
  [loop]="0"
  [loop-mono]="0"
  [incsum]="2003000"
  [array]="50000"
  [matmult]="38852480"
  [quicksort]="9999"
)

# --static は samples/input/<target>_fs.txt を使う。ほとんどのターゲットは
# 通常入力と _fs 入力が同じ値なので EXPECTED をそのまま使ってよいが、
# 一部（例: incsum）は _fs 入力のサイズが異なり正解も異なるため、
# ここに載っているターゲットだけ個別の値で上書きする。
declare -A EXPECTED_STATIC=(
  [incsum]="50015000"
  [array]="100000"
)

LOGDIR="$(mktemp -d)"
trap 'rm -rf "$LOGDIR"' EXIT

PIDS=()
NAMES=()
LOGFILES=()
for target in "${!EXPECTED[@]}"; do
  expected="${EXPECTED[$target]}"
  expected_static="${EXPECTED_STATIC[$target]:-$expected}"
  logfile="$LOGDIR/$target.dynamize.log"
  ( "$BIN" "$target" --dynamize --expected "$expected" ) > "$logfile" 2>&1 &
  PIDS+=($!); NAMES+=("$target (dynamize)"); LOGFILES+=("$logfile")
  logfile="$LOGDIR/$target.static.log"
  ( "$BIN" "$target" --static --expected "$expected_static" ) > "$logfile" 2>&1 &
  PIDS+=($!); NAMES+=("$target (static)"); LOGFILES+=("$logfile")
done

FAIL=0
for i in "${!PIDS[@]}"; do
  pid="${PIDS[$i]}"
  name="${NAMES[$i]}"
  if wait "$pid"; then
    echo "OK     $name"
  else
    echo "FAILED $name"
    grep -h "\[FAIL\]\|Skip\]" "${LOGFILES[$i]}" | sed 's/^/         /'
    FAIL=1
  fi
done

exit $FAIL
