#!/bin/bash

# スクリプトのあるディレクトリに移動（CIのどこから呼んでも動くようにする）
cd "$(dirname "$0")"

FAILED=0

# テスト実行用の関数
# TEST_DIR が設定されているとき: cd "$TEST_DIR" してから lSdti "$filename" を実行
# TEST_DIR が未設定のとき:       compile_test/ からそのまま実行
run_test() {
  local filename="$1" expected="$2" skip_flag="$3"
  local filepath="${TEST_DIR:+$TEST_DIR/}$filename"
  local actual

  for opt in "-c" "-c -a" "-c -b --non_monotonic" "-c --static"; do
    if [[ "$opt" == *"--static"* ]] && [[ "$skip_flag" == "skip_static" ]]; then
      echo "Testing $filepath ($opt) ... SKIPPED (As requested)"
      continue
    fi

    echo -n "Testing $filepath ($opt) ... "
    actual=$(cd "${TEST_DIR:-.}" && lSdti "$filename" $opt 2>&1)

    if [ "$actual" = "$expected" ]; then
      echo "OK"
    else
      echo "FAILED"
      echo "  Options:  $opt"
      echo "  Expected: \"$expected\""
      echo "  Got:      \"$actual\""
      FAILED=1
    fi
  done
}

# 各ディレクトリの tests.sh を順に実行
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
  paper \
  do
  [ -f "$TEST_DIR/tests.sh" ] && source "$TEST_DIR/tests.sh"
done


if [ $FAILED -eq 1 ]; then
  echo "Some tests failed."
  exit 1
else
  echo "All tests passed."
fi
