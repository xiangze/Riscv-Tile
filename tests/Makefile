# =============================================================================
#  tests/Makefile  ―  riscv-tests サブモジュールから rv32ui / rv32um をビルド
#
#  使い方
#    make           ← 全テストをビルド → hex/ に出力
#    make rv32ui    ← RV32I 整数命令テストのみ
#    make rv32um    ← RV32M 乗除算テストのみ
#    make clean     ← 生成物を削除
#    make list      ← ビルドされたテスト一覧を表示
# =============================================================================

# ── ツールチェーン ────────────────────────────────────────────────────────────
RISCV_PREFIX  ?= riscv64-unknown-elf-
RISCV_GCC     := $(RISCV_PREFIX)gcc
RISCV_OBJCOPY := $(RISCV_PREFIX)objcopy
RISCV_OBJDUMP := $(RISCV_PREFIX)objdump
PYTHON        := python3

# ── コンパイルオプション（RV32IM, bare-metal, no stdlib） ─────────────────────
ARCH_RV32I  := -march=rv32i  -mabi=ilp32
ARCH_RV32IM := -march=rv32im -mabi=ilp32
GCC_OPTS    := -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles

# ── ディレクトリ ──────────────────────────────────────────────────────────────
HERE         := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
RISCV_TESTS  := $(HERE)../riscv-tests
ISA_DIR      := $(RISCV_TESTS)/isa
MACROS_DIR   := $(ISA_DIR)/macros/scalar
ENV_DIR      := $(HERE)env
OUT_DIR      := $(HERE)build
HEX_DIR      := $(HERE)hex
SCRIPTS_DIR  := $(HERE)scripts

# ── テスト一覧（submodule から自動列挙） ──────────────────────────────────────
RV32UI_SRCS  := $(wildcard $(ISA_DIR)/rv32ui/*.S)
RV32UM_SRCS  := $(wildcard $(ISA_DIR)/rv32um/*.S)

# ベース名（例: add, addi, mul, …）
RV32UI_TESTS := $(notdir $(basename $(RV32UI_SRCS)))
RV32UM_TESTS := $(notdir $(basename $(RV32UM_SRCS)))

# ELF / HEX ターゲット
RV32UI_ELFS  := $(patsubst %,$(OUT_DIR)/rv32ui-p-%,$(RV32UI_TESTS))
RV32UM_ELFS  := $(patsubst %,$(OUT_DIR)/rv32um-p-%,$(RV32UM_TESTS))
RV32UI_HEXS  := $(patsubst %,$(HEX_DIR)/rv32ui-p-%.hex,$(RV32UI_TESTS))
RV32UM_HEXS  := $(patsubst %,$(HEX_DIR)/rv32um-p-%.hex,$(RV32UM_TESTS))

# ── デフォルトターゲット ───────────────────────────────────────────────────────
.PHONY: all rv32ui rv32um clean list check-tools check-submodule allall

allall: check-tools check-submodule rv32ui rv32um
	@echo ""
	@echo "=== Build complete ==="
	@echo "Hex files written to: $(HEX_DIR)"
	@ls $(HEX_DIR)/*.hex 2>/dev/null | wc -l | xargs -I{} echo "{} test(s) ready"

all: rv32ui rv32um
	@echo ""
	@echo "=== Build complete ==="
	@echo "Hex files written to: $(HEX_DIR)"
	@ls $(HEX_DIR)/*.hex 2>/dev/null | wc -l | xargs -I{} echo "{} test(s) ready"

rv32ui: $(RV32UI_HEXS)
rv32um: $(RV32UM_HEXS)

# ── サブモジュール確認 ────────────────────────────────────────────────────────
check-submodule:
	@if [ ! -f "$(ISA_DIR)/rv32ui/add.S" ]; then \
	  echo "ERROR: riscv-tests submodule not initialized."; \
	  echo "Run: git submodule update --init --recursive"; \
	  exit 1; \
	fi
	@if [ ! -f "$(ISA_DIR)/macros/scalar/test.h" ]; then \
	  echo "ERROR: riscv-test-env (nested submodule) not initialized."; \
	  echo "Run: git submodule update --init --recursive"; \
	  exit 1; \
	fi

# ── ツールチェーン確認 ────────────────────────────────────────────────────────
check-tools:
	@which $(RISCV_GCC) > /dev/null 2>&1 || \
	  (echo "ERROR: $(RISCV_GCC) not found. Install riscv64-unknown-elf-gcc." && exit 1)
	@which $(PYTHON) > /dev/null 2>&1 || \
	  (echo "ERROR: python3 not found." && exit 1)

# ── ディレクトリ作成 ─────────────────────────────────────────────────────────
$(OUT_DIR) $(HEX_DIR):
	mkdir -p $@

# ── rv32ui ELF ビルドルール ───────────────────────────────────────────────────
$(OUT_DIR)/rv32ui-p-%: $(ISA_DIR)/rv32ui/%.S | $(OUT_DIR)
	$(RISCV_GCC) $(ARCH_RV32I) $(GCC_OPTS) \
	  -I$(ENV_DIR) \
	  -I$(MACROS_DIR) \
	  -T$(ENV_DIR)/link.ld \
	  $< -o $@
	@echo "[rv32ui] built $(@F)"

# ── rv32um ELF ビルドルール ───────────────────────────────────────────────────
$(OUT_DIR)/rv32um-p-%: $(ISA_DIR)/rv32um/%.S | $(OUT_DIR)
	$(RISCV_GCC) $(ARCH_RV32IM) $(GCC_OPTS) \
	  -I$(ENV_DIR) \
	  -I$(MACROS_DIR) \
	  -T$(ENV_DIR)/link.ld \
	  $< -o $@
	@echo "[rv32um] built $(@F)"

# ── ELF → hex 変換ルール ─────────────────────────────────────────────────────
$(HEX_DIR)/%.hex: $(OUT_DIR)/% | $(HEX_DIR)
	$(PYTHON) $(SCRIPTS_DIR)/elf2hex.py $< $@
	@echo "[hex]    generated $(@F)"

# ── ディスアセンブル（デバッグ用） ────────────────────────────────────────────
$(OUT_DIR)/%.dump: $(OUT_DIR)/%
	$(RISCV_OBJDUMP) -d $< > $@

# ── 掃除 ──────────────────────────────────────────────────────────────────────
clean:
	rm -rf $(OUT_DIR) $(HEX_DIR)
	@echo "Cleaned."

# ── テスト一覧 ────────────────────────────────────────────────────────────────
list:
	@echo "=== rv32ui tests ($(words $(RV32UI_TESTS))) ==="
	@echo $(RV32UI_TESTS) | tr ' ' '\n' | sort | column
	@echo ""
	@echo "=== rv32um tests ($(words $(RV32UM_TESTS))) ==="
	@echo $(RV32UM_TESTS) | tr ' ' '\n' | sort | column
