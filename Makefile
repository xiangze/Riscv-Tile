# =============================================================================
#  Makefile  ―  tile-riscv 開発コマンド集
#
#  前提: Docker + Docker Compose がインストール済みであること
#
#  使い方:
#    make help          # コマンド一覧を表示
#    make setup         # 初回セットアップ（イメージビルド + submodule 初期化）
#    make build         # riscv-tests → hex ファイル生成
#    make test          # 全テスト実行
#    make verilog       # SystemVerilog 生成
#    make shell         # 開発シェル起動
# =============================================================================

# ── 変数 ─────────────────────────────────────────────────────────────────────

IMAGE      := tile-riscv
COMPOSE    := docker compose
RUN        := $(COMPOSE) run --rm

# テスト対象の絞り込み（例: make test FILTER=add）
FILTER     ?=

# タイル配列サイズ（Verilog 生成時に参照）
ROWS       ?= 4
COLS       ?= 4

# ── カラー出力 ────────────────────────────────────────────────────────────────

BOLD  := \033[1m
GREEN := \033[32m
CYAN  := \033[36m
RESET := \033[0m

# =============================================================================
#  初回セットアップ
# =============================================================================

.PHONY: setup
setup: ## 🚀 初回セットアップ（イメージビルド + submodule 初期化）
	@echo "$(BOLD)$(GREEN)=== [1/3] Initializing git submodules ===$(RESET)"
	git submodule update --init --recursive
	@echo "$(BOLD)$(GREEN)=== [2/3] Building Docker image ===$(RESET)"
	$(COMPOSE) build
	@echo "$(BOLD)$(GREEN)=== [3/3] Building riscv-tests hex files ===$(RESET)"
	$(RUN) build
	@echo ""
	@echo "$(BOLD)$(GREEN)Setup complete! Run 'make test' to verify.$(RESET)"

# =============================================================================
#  Docker イメージ管理
# =============================================================================

.PHONY: image image-rebuild image-clean

image: ## 🐳 Docker イメージをビルド（キャッシュあり）
	$(COMPOSE) build

image-rebuild: ## 🐳 Docker イメージをキャッシュなしで再ビルド
	$(COMPOSE) build --no-cache

image-clean: ## 🗑️  Docker イメージを削除
	docker rmi $(IMAGE):latest 2>/dev/null || true
	@echo "Image removed."

# =============================================================================
#  テスト hex ファイルのビルド
# =============================================================================

.PHONY: build build-ui build-um build-clean

build: ## 🔨 riscv-tests（rv32ui + rv32um）を hex にビルド
	$(RUN) build

build-ui: ## 🔨 rv32ui（整数命令テスト）のみビルド
	$(RUN) base make -C tests rv32ui

build-um: ## 🔨 rv32um（乗除算テスト）のみビルド
	$(RUN) base make -C tests rv32um

build-clean: ## 🗑️  hex / ELF ビルド成果物を削除
	$(RUN) base make -C tests clean

# =============================================================================
#  テスト実行
# =============================================================================

.PHONY: test test-ui test-um test-filter

test: ## ✅ 全テストを実行（rv32ui + rv32um）
	$(RUN) test

test-ui: ## ✅ rv32ui テストのみ実行
	$(RUN) test-ui

test-um: ## ✅ rv32um テストのみ実行
	$(RUN) test-um

test-filter: ## ✅ 特定テストを実行（例: make test-filter FILTER=add）
	@if [ -z "$(FILTER)" ]; then \
	  echo "Usage: make test-filter FILTER=<test_name>"; \
	  echo "Example: make test-filter FILTER=add"; \
	  exit 1; \
	fi
	$(RUN) base sbt "testOnly tileriscv.RV32UITests -- -z $(FILTER)"

# =============================================================================
#  SystemVerilog 生成
# =============================================================================

.PHONY: verilog verilog-show

verilog: ## ⚡ SystemVerilog を生成（generated/ に出力）
	$(RUN) verilog
	@echo ""
	@echo "Generated files:"
	@ls -lh generated/ 2>/dev/null || echo "(no files yet)"

verilog-show: ## 📄 生成された SystemVerilog を表示
	@ls generated/*.sv 2>/dev/null || (echo "No .sv files. Run 'make verilog' first." && exit 1)
	@echo "--- generated SystemVerilog files ---"
	@ls -lh generated/*.sv

# =============================================================================
#  一括実行
# =============================================================================

.PHONY: all ci

all: ## 🎯 ビルド → テスト → Verilog 生成を順番に実行
	$(RUN) all

ci: ## 🤖 CI 相当の処理をローカルで実行（all と同等）
	@echo "$(BOLD)$(CYAN)=== Running CI pipeline locally ===$(RESET)"
	$(MAKE) build
	$(MAKE) test
	$(MAKE) verilog
	@echo "$(BOLD)$(GREEN)=== CI pipeline passed ===$(RESET)"

# =============================================================================
#  開発ユーティリティ
# =============================================================================

.PHONY: shell shell-root list-tests disasm

shell: ## 🐚 開発用インタラクティブシェルを起動
	$(RUN) shell

shell-root: ## 🐚 root で開発シェルを起動
	$(COMPOSE) run --rm --user root shell

list-tests: ## 📋 ビルド済みテスト一覧を表示
	$(RUN) base make -C tests list

disasm: ## 🔍 ELF を逆アセンブル（例: make disasm TEST=rv32ui-p-add）
	@if [ -z "$(TEST)" ]; then \
	  echo "Usage: make disasm TEST=<test_name>"; \
	  echo "Example: make disasm TEST=rv32ui-p-add"; \
	  exit 1; \
	fi
	$(RUN) base riscv64-unknown-elf-objdump -d tests/build/$(TEST)

# =============================================================================
#  クリーン
# =============================================================================

.PHONY: clean clean-all

clean: ## 🗑️  テスト成果物（hex / ELF）を削除
	$(RUN) base make -C tests clean

clean-all: clean image-clean ## 🗑️  全成果物 + Docker イメージを削除
	docker compose down --volumes 2>/dev/null || true
	rm -rf generated/
	@echo "All artifacts removed."

# =============================================================================
#  ヘルプ
# =============================================================================

.PHONY: help

help: ## 📖 このヘルプを表示
	@echo ""
	@echo "$(BOLD)tile-riscv — よく使うコマンド$(RESET)"
	@echo ""
	@echo "$(CYAN)初回セットアップ:$(RESET)"
	@grep -E '^setup:' $(MAKEFILE_LIST) | \
	  awk 'BEGIN {FS = ":.*?## "}; {printf "  $(BOLD)%-20s$(RESET) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(CYAN)イメージ管理:$(RESET)"
	@grep -E '^image[^:]*:.*## ' $(MAKEFILE_LIST) | \
	  awk 'BEGIN {FS = ":.*?## "}; {printf "  $(BOLD)%-20s$(RESET) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(CYAN)テスト hex ビルド:$(RESET)"
	@grep -E '^build[^:]*:.*## ' $(MAKEFILE_LIST) | \
	  awk 'BEGIN {FS = ":.*?## "}; {printf "  $(BOLD)%-20s$(RESET) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(CYAN)テスト実行:$(RESET)"
	@grep -E '^test[^:]*:.*## ' $(MAKEFILE_LIST) | \
	  awk 'BEGIN {FS = ":.*?## "}; {printf "  $(BOLD)%-20s$(RESET) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(CYAN)Verilog 生成:$(RESET)"
	@grep -E '^verilog[^:]*:.*## ' $(MAKEFILE_LIST) | \
	  awk 'BEGIN {FS = ":.*?## "}; {printf "  $(BOLD)%-20s$(RESET) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(CYAN)一括実行:$(RESET)"
	@grep -E '^(all|ci):.*## ' $(MAKEFILE_LIST) | \
	  awk 'BEGIN {FS = ":.*?## "}; {printf "  $(BOLD)%-20s$(RESET) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(CYAN)開発ユーティリティ:$(RESET)"
	@grep -E '^(shell|shell-root|list-tests|disasm):.*## ' $(MAKEFILE_LIST) | \
	  awk 'BEGIN {FS = ":.*?## "}; {printf "  $(BOLD)%-20s$(RESET) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(CYAN)クリーン:$(RESET)"
	@grep -E '^clean[^:]*:.*## ' $(MAKEFILE_LIST) | \
	  awk 'BEGIN {FS = ":.*?## "}; {printf "  $(BOLD)%-20s$(RESET) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(CYAN)変数:$(RESET)"
	@echo "  $(BOLD)FILTER$(RESET)  テスト絞り込み  例: make test-filter FILTER=add"
	@echo "  $(BOLD)TEST$(RESET)    逆アセ対象      例: make disasm TEST=rv32ui-p-add"
	@echo ""

# デフォルトターゲット
.DEFAULT_GOAL := help