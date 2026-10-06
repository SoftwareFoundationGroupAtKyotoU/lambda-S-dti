#!/bin/bash
# Entry point of the benchmark container (copied to /usr/local/bin by the
# Dockerfile, outside /app so that `-v $(pwd):/app` does not hide it).
set -e

COMMAND=$1
# 引数が何も指定されなかった場合は bash を起動する
if [ -z "$COMMAND" ]; then
  exec /bin/bash
fi
shift

case "$COMMAND" in
  bench)
    # bind mount した logs/ に、ホストのユーザーが書き換えられないファイルを残さない。
    # 以前は実行後に chown するだけだったため、Ctrl+C や docker stop で止めると
    # chown まで到達せず（PID 1 の bash は子の終了を待つ間シグナルを処理せず、
    # 10 秒後に SIGKILL される）、make plot の前に sudo chmod が必要になっていた。
    #   (1) umask 0000: 作るファイルとディレクトリを誰でも書き換え・削除できるようにする
    #       （chown まで到達しなかった場合の保険）
    #   (2) ベンチを子プロセスで動かし、INT/TERM を子に転送して、終了後に必ず chown する
    #       （docker run -e HOST_UID=$(id -u) -e HOST_GID=$(id -g) を渡したとき）
    umask 0000
    set +e
    dune exec ./_build/default/bin/bench.exe -- "$@" &
    child=$!
    trap 'kill -TERM "$child" 2>/dev/null' INT TERM
    # wait はシグナルで中断されると 128 を超える値で戻るので、子が終わるまで待ち直す
    while :; do
      wait "$child"
      status=$?
      kill -0 "$child" 2>/dev/null || break
    done
    trap - INT TERM
    if [ -n "${HOST_UID:-}" ] && [ -n "${HOST_GID:-}" ]; then
      chown -R "${HOST_UID}:${HOST_GID}" /app/logs 2>/dev/null || true
    fi
    exit "$status"
    ;;
  main)
    exec dune exec ./_build/default/bin/main.exe -- "$@"
    ;;
  *)
    # 上記以外（bashなど）が指定された場合はそのまま実行
    exec "$COMMAND" "$@"
    ;;
esac
