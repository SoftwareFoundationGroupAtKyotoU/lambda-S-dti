FROM ubuntu:20.04
ENV DEBIAN_FRONTEND=noninteractive

# 1. 必要なツールと開発用パッケージ(g++, racket-dev)を一括インストール
RUN apt-get update && apt-get install -y \
    racket \
    llvm-11-dev \
    clang-11 \
    make \
    gcc \
    g++ \
    git \
    && rm -rf /var/lib/apt/lists/*

# 2. Griftのインストール
RUN raco pkg install --auto --name grift https://github.com/Gradual-Typing/Grift.git

# 3. 環境変数の永続化
# LLVMの設定ツールを指定
ENV LLVM_CONFIG=llvm-config-11

# 4. Griftのバイナリが置かれたディレクトリを環境変数PATHに追加
# これにより、どのディレクトリからでも「grift」コマンドが打てるようになります
ENV PATH="/root/.racket/7.2/bin:${PATH}"

# 5. コンテナ起動時のデフォルトディレクトリを設定
WORKDIR /root
