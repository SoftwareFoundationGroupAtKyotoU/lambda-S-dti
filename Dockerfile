# File: Dockerfile
FROM ubuntu:20.04
ENV DEBIAN_FRONTEND=noninteractive

# -----------------------------------------------------------------------------
# 1. 依存パッケージの一括インストール
# -----------------------------------------------------------------------------
RUN apt-get update && apt-get install -y \
    curl git make gcc g++ m4 unzip pkg-config libgmp-dev \
    racket llvm-11-dev clang-11 \
    python3 python3-pip \
    opam \
    lsb-release wget software-properties-common gnupg \
    libgc-dev libcjson-dev \
    && rm -rf /var/lib/apt/lists/*

# -----------------------------------------------------------------------------
# 2. LLVM 18 と Grift のセットアップ
# -----------------------------------------------------------------------------
# Clang 18 のインストールと標準コマンドとしての登録
RUN wget https://apt.llvm.org/llvm.sh && \
    chmod +x llvm.sh && \
    ./llvm.sh 18 && \
    rm llvm.sh && \
    ln -sf /usr/bin/clang-18 /usr/bin/clang && \
    ln -sf /usr/bin/clang++-18 /usr/bin/clang++ && \
    ln -sf /usr/bin/clang-18 /usr/bin/cc && \
    ln -sf /usr/bin/clang++-18 /usr/bin/c++

# Griftのインストール
ENV LLVM_CONFIG=llvm-config-11
RUN raco pkg install --auto --name grift https://github.com/Gradual-Typing/Grift.git
RUN ln -s $(racket -e '(require setup/dirs) (displayln (find-user-console-bin-dir))')/grift /usr/local/bin/grift

# -----------------------------------------------------------------------------
# 3. OCaml (lambda-S-dti) のセットアップ
# -----------------------------------------------------------------------------
RUN opam init -y --disable-sandboxing --compiler=5.2.0

ENV OPAM_SWITCH_PREFIX=/root/.opam/5.2.0
ENV CAML_LD_LIBRARY_PATH=/root/.opam/5.2.0/lib/stublibs:/root/.opam/5.2.0/lib/ocaml/stublibs:/root/.opam/5.2.0/lib/ocaml
ENV OCAML_TOPLEVEL_PATH=/root/.opam/5.2.0/lib/toplevel
ENV MANPATH=/root/.opam/5.2.0/man
ENV PATH="/root/.opam/5.2.0/bin:$PATH"

# 必要なOCamlパッケージ
RUN opam install -y dune core menhir ppx_jane core_unix ounit2 yojson core_bench

# -----------------------------------------------------------------------------
# 4. ソースコードのコピーとビルド
# -----------------------------------------------------------------------------
WORKDIR /app
COPY . .

RUN opam pin add lambda-S-dti . -y --no-action && \
    dune build

ENV CC=clang-18
ENV CXX=clang++-18

# -----------------------------------------------------------------------------
# 5. ENTRYPOINT スクリプトの作成と設定
# -----------------------------------------------------------------------------
RUN echo '#!/bin/bash\n\
set -e\n\
\n\
COMMAND=$1\n\
# 引数が何も指定されなかった場合は bash を起動する\n\
if [ -z "$COMMAND" ]; then\n\
  exec /bin/bash\n\
fi\n\
shift\n\
\n\
case "$COMMAND" in\n\
  bench)\n\
    exec dune exec ./_build/default/bin/bench.exe -- "$@"\n\
    ;; \n\
  main)\n\
    exec dune exec ./_build/default/bin/main.exe -- "$@"\n\
    ;;\n\
  *)\n\
    # 上記以外（bashなど）が指定された場合はそのまま実行\n\
    exec "$COMMAND" "$@"\n\
    ;;\n\
esac\n\
' > /app/entrypoint.sh && chmod +x /app/entrypoint.sh

# コンテナの入り口をスクリプトに固定
ENTRYPOINT ["/app/entrypoint.sh"]