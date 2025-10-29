# Makefile
# OCaml/dune のビルド・実行・テスト、ベンチ、グラフ生成(uv)を一発で

SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
.ONESHELL:
.DEFAULT_GOAL := build

# ----- Verbosity -----------------------------------------------------------
VERBOSE ?= 0
ifeq ($(VERBOSE),0)
.SILENT:
endif

# ----- Config --------------------------------------------------------------
REQUIRED_OCAML_CMDS := ocamlc opam dune
REQUIRED_OCAML_PACKAGES := dune menhir alcotest core_bench owl linenoise
OPAM_UPDATE ?= 0   # 必要なときだけ: OPAM_UPDATE=1 make setup

# python コマンド名（python 優先・無ければ python3）
PYTHON := $(shell command -v python 2>/dev/null || command -v python3 2>/dev/null)

# ----- Helpers -------------------------------------------------------------
# opam の環境をロードして任意コマンドを実行（switch 出力は -s で安定化）
define OPAM_RUN
bash -lc 'set -euo pipefail; \
  eval "$$(opam env --switch=$$(opam switch show -s 2>/dev/null) --set-switch --shell=bash 2>/dev/null || opam env --shell=bash)"; \
  $(1)'
endef

# 速度最適化: opam list を1回だけ呼び、完全一致で不足分のみ導入
define ENSURE_OPAM_PACKAGES
@$(call OPAM_RUN, \
  if [ "$(OPAM_UPDATE)" = "1" ]; then \
    echo "ℹ️ opam update..."; opam update -y >/dev/null; \
  fi; \
  installed="$$(opam list --installed --short --columns=name 2>/dev/null | sort -u)"; \
  missing=(); \
  for p in $(1); do \
    echo "$$installed" | grep -Fxq "$$p" || missing+=("$$p"); \
  done; \
  if [ "$${#missing[@]}" -gt 0 ]; then \
    echo "ℹ️ Installing opam packages: $${missing[*]}"; \
    opam install -y $${missing[*]}; \
  else \
    echo "✅ All required opam packages already installed."; \
  fi; \
  echo "✅ opam packages OK: $(1)")
endef

# ----- Targets -------------------------------------------------------------
.PHONY: setup build run test benchmark graph clean opam-update \
        check-ocaml check-ocaml-pkgs check-python check-uv check-py-reqs

# 初回セットアップ（OCamlパッケージ導入）
setup: check-ocaml check-ocaml-pkgs
	@true

# ビルド（デフォルト）
build: check-ocaml check-ocaml-pkgs
	@$(call OPAM_RUN, dune build)

# 実行
run: check-ocaml check-ocaml-pkgs
	@$(call OPAM_RUN, dune exec ./bin/main.exe)

# テスト（alcotest 必須：共通チェックで導入）
test: check-ocaml check-ocaml-pkgs
	@$(call OPAM_RUN, dune runtest)

# ベンチ（core_bench / owl）
benchmark: check-ocaml check-ocaml-pkgs
	@$(call OPAM_RUN, dune exec ./bin/bench.exe)

# グラフ生成（uv venv + 依存導入 + 実行）
plot: check-python check-uv
	@if [ ! -f scripts/requirements.txt ]; then \
		printf "%s\n" numpy matplotlib scipy > scripts/requirements.txt; \
		echo "📝 Created default scripts/requirements.txt (numpy matplotlib scipy)"; \
	fi
	@uv venv
	@uv pip install -q -r scripts/requirements.txt
	@uv run python scripts/check_requirements.py
	@uv run python scripts/plot_relative.py
	@uv run python scripts/plot_scattered.py
	@uv run python scripts/plot_herman.py
	@echo "✅ Graphs generated."

# レポート生成（uv venv + 依存導入 + 実行）
report: check-python check-uv
	@if [ ! -f scripts/requirements.txt ]; then \
		printf "%s\n" numpy matplotlib scipy > scripts/requirements.txt; \
		echo "📝 Created default scripts/requirements.txt (numpy matplotlib scipy)"; \
	fi
	@uv venv
	@uv pip install -q -r scripts/requirements.txt
	@uv run python scripts/check_requirements.py
	@uv run python scripts/report_herman.py
	@uv run python scripts/report_ratio_extremes.py
	@echo "✅ Graphs generated."

# お掃除
clean:
	@dune clean || true
	@rm -rf .venv

# opam update だけ実行したい場合に便利
opam-update:
	@$(call OPAM_RUN, opam update -y; echo "✅ opam update done.")

# ----- Checks --------------------------------------------------------------
check-ocaml:
	@for cmd in $(REQUIRED_OCAML_CMDS); do \
		if ! command -v $$cmd >/dev/null 2>&1; then \
			echo "❌ Missing $$cmd. Please install OCaml/opam/dune."; \
			exit 1; \
		fi; \
	done
	@echo "✅ OCaml toolchain OK ($(REQUIRED_OCAML_CMDS))."

# dune/menhir/alcotest/core_bench/owl の不足分のみ入れる
check-ocaml-pkgs: check-ocaml
	$(ENSURE_OPAM_PACKAGES)

# python or python3
check-python:
	@if command -v python >/dev/null 2>&1 || command -v python3 >/dev/null 2>&1; then \
		echo "✅ Python OK."; \
	else \
		echo "❌ python (or python3) not found."; \
		exit 1; \
	fi

# uv
check-uv:
	@if ! command -v uv >/dev/null 2>&1; then \
		echo "ℹ️ Installing uv..."; \
		curl -LsSf https://astral.sh/uv/install.sh | sh; \
	fi
	@if ! command -v uv >/dev/null 2>&1; then \
		echo "❌ uv not found after install. Ensure $$HOME/.local/bin is in PATH."; \
		exit 1; \
	fi
	@echo "✅ uv OK."

# scripts/requirements.txt の存在チェックが欲しい場合
check-py-reqs:
	@if [ ! -f scripts/requirements.txt ]; then \
		echo "❌ scripts/requirements.txt not found."; exit 1; \
	fi
	@echo "✅ scripts/requirements.txt found."
