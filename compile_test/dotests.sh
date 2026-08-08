#!/bin/bash

SELF="$(readlink -f "$0")"
cd "$(dirname "$SELF")"

# =====================================================================
# 子プロセス
# =====================================================================
if [ "$1" = "--worker" ]; then
  shift
  index="$1" test_dir="$2" filename="$3" opt="$4" expected="$5"
  
  filepath="${test_dir:+$test_dir/}$filename"

  # lSdti が並列実行により同じファイルを操作して「File exists」で落ちる対策。
  # エラーに "File exists" が含まれている場合は少し待ってリトライする（最大5回）
  for i in {1..5}; do
    actual=$(cd "${test_dir:-.}" && lSdti "$filename" $opt 2>&1)
    
    if [[ "$actual" != *"File exists"* ]]; then
      break # 競合エラー以外（正常終了、または普通のテスト失敗）ならループを抜ける
    fi
    
    # 競合発生時：0.1秒〜0.9秒ランダムに待機してリトライ
    sleep "0.$((RANDOM % 9 + 1))"
  done

  # 実行が終わった直後に、直接画面(標準出力)へ出力
  if [ "$actual" = "$expected" ]; then
    echo "Testing $filepath ($opt) ... OK"
    exit 0
  else
    # 他の出力と混ざるのを防ぐため、echo -e で一度に出力
    echo -e "Testing $filepath ($opt) ... FAILED\n  Options:  $opt\n  Expected: \"$expected\"\n  Got:      \"$actual\""
    exit 1
  fi
fi

# =====================================================================
# 親プロセス
# =====================================================================

JOB_QUEUE="$(mktemp)"
JOB_INDEX=0
FAILED=0

cleanup() {
  rm -f "$JOB_QUEUE"
}
trap cleanup EXIT

# ---------------------------------------------------------------------
# テストケースをキューに登録する関数
# ---------------------------------------------------------------------
run_test() {
  local filename="$1" expected="$2" skip_flag="$3"
  local filepath="${TEST_DIR:+$TEST_DIR/}$filename"

  for opt in \
    "-c -O0                         "\
    "-c -O0 -a                      "\
    "-c -O0    -e                   "\
    "-c -O0 -a -e                   "\
    "-c -O0          --non_monotonic"\
    "-c -O0 -a       --non_monotonic"\
    "-c -O0    -e    --non_monotonic"\
    "-c -O0 -a -e    --non_monotonic"\
    "-c -O0       -b --non_monotonic"\
    "-c -O0    -e -b --non_monotonic"\
    "-c -O0          --static       "\
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

# ---------------------------------------------------------------------
# テスト定義の読み込み
# ---------------------------------------------------------------------
for TEST_DIR in \
  minCaml \
  issues \
  original/array \
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

# ---------------------------------------------------------------------
# ジョブキューの並列実行
# ---------------------------------------------------------------------
NPROC="$(nproc 2>/dev/null || echo 4)"

if [ "$JOB_INDEX" -gt 0 ]; then
  # xargsで並列実行（リアルタイム出力）
  xargs -0 -n5 -P "$NPROC" bash "$SELF" --worker < "$JOB_QUEUE"
  XARGS_STATUS=$?
else
  XARGS_STATUS=0
fi

# ---------------------------------------------------------------------
# 終了判定
# ---------------------------------------------------------------------
if [ "$XARGS_STATUS" -ne 0 ]; then
  FAILED=1
fi

if [ $FAILED -eq 1 ]; then
  echo "Some tests failed."
  exit 1
else
  echo "All tests passed."
fi