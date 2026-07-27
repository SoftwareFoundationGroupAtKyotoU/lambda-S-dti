#!/bin/bash

# スクリプトの絶対パスを cd の前に確定させる（worker再起動用）
SELF="$(readlink -f "$0")"

# スクリプトのあるディレクトリに移動（CIのどこから呼んでも動くようにする）
cd "$(dirname "$SELF")"

# --- worker モード -----------------------------------------------------
# xargs -P から `bash "$SELF" --worker <index> <test_dir> <filename> <opt> <expected>`
# の形で1ジョブぶんだけ呼ばれる。結果は $RESULT_DIR/<index> に書き出す
# (複数workerの標準出力が同時に混ざって化けるのを防ぐため)。
if [ "$1" = "--worker" ]; then
  shift
  index="$1" test_dir="$2" filename="$3" opt="$4" expected="$5"
  filepath="${test_dir:+$test_dir/}$filename"
  out="$RESULT_DIR/$index"

  actual=$(cd "${test_dir:-.}" && lSdti "$filename" $opt 2>&1)

  if [ "$actual" = "$expected" ]; then
    echo "Testing $filepath ($opt) ... OK" > "$out"
    exit 0
  else
    {
      echo "Testing $filepath ($opt) ... FAILED"
      echo "  Options:  $opt"
      echo "  Expected: \"$expected\""
      echo "  Got:      \"$actual\""
    } > "$out"
    exit 1
  fi
fi

# --- 通常モード：ジョブを列挙してから並列実行 ---------------------------

JOB_QUEUE="$(mktemp)"
RESULT_DIR="$(mktemp -d)"
export RESULT_DIR
JOB_INDEX=0
FAILED=0

cleanup() {
  rm -f "$JOB_QUEUE"
  rm -rf "$RESULT_DIR"
}
trap cleanup EXIT

# run_test は実行はせず、(index, test_dir, filename, opt, expected) を
# NUL区切りでジョブキューに積むだけにする。expected には改行を含む
# 複数行文字列が来ることがあるが、NUL区切り + xargs -0 ならそのまま扱える。
run_test() {
  local filename="$1" expected="$2" skip_flag="$3"
  local filepath="${TEST_DIR:+$TEST_DIR/}$filename"

  for opt in \
    "-c                         "\
    "-c -a                      "\
    "-c    -e                   "\
    "-c -a -e                   "\
    "-c          --non_monotonic"\
    "-c -a       --non_monotonic"\
    "-c    -e    --non_monotonic"\
    "-c -a -e    --non_monotonic"\
    "-c       -b --non_monotonic"\
    "-c    -e -b --non_monotonic"\
    "-c          --static       "\
    ; do
    if [[ "$opt" == *"--static"* ]] && [[ "$skip_flag" == "skip_static" ]]; then
      echo "Testing $filepath ($opt) ... SKIPPED (As requested)"
      continue
    fi

    JOB_INDEX=$((JOB_INDEX + 1))
    printf '%s\0%s\0%s\0%s\0%s\0' \
      "$JOB_INDEX" "$TEST_DIR" "$filename" "$opt" "$expected" >> "$JOB_QUEUE"
  done
}

# 各ディレクトリの tests.sh を順に実行（ジョブの列挙のみ、まだ何も実行しない）
for TEST_DIR in \
  minCaml \
  issues \
  original/bool \
  original/dynamic \
  original/int \
  original/list \
  original/match \
  original/ref \
  original/tuple \
  original \
  paper
  do
  [ -f "$TEST_DIR/tests.sh" ] && source "$TEST_DIR/tests.sh"
done

# ジョブキューを並列 (CPU数ぶん) に投げる。1ジョブ = 5フィールド (-n5)。
NPROC="$(nproc 2>/dev/null || echo 4)"
if [ "$JOB_INDEX" -gt 0 ]; then
  xargs -0 -n5 -P "$NPROC" bash "$SELF" --worker < "$JOB_QUEUE"
  XARGS_STATUS=$?
else
  XARGS_STATUS=0
fi

# 結果をジョブ番号順に表示
for i in $(seq 1 "$JOB_INDEX"); do
  [ -f "$RESULT_DIR/$i" ] && cat "$RESULT_DIR/$i"
done

if [ "$XARGS_STATUS" -ne 0 ]; then
  FAILED=1
fi

if [ $FAILED -eq 1 ]; then
  echo "Some tests failed."
  exit 1
else
  echo "All tests passed."
fi
