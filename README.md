# tile-riscv

タイル状に並べた RV32IM コアのアレイ。隣接コア間でレジスタ値を直接転送する
カスタム命令 (`TILE_SEND` / `TILE_RECV`) を追加。

## ディレクトリ構造

```
tile-riscv/
├── build.sbt
├── .gitmodules                   ← riscv-tests を submodule として登録
├── riscv-tests/                  ← git submodule (riscv-software-src/riscv-tests)
│   └── env/                     ← nested submodule (riscv/riscv-test-env)
│
├── src/
│   ├── main/scala/tileriscv/
│   │   ├── TileRiscV.scala       ← メイン設計（RV32I + タイル通信）
│   │   ├── TileRiscV_M.scala     ← RV32M 乗除算拡張パッチ
│   │   └── TileRiscVSim.scala    ← シミュレーション用コア
│   └── test/scala/tileriscv/
│       └── RiscVTestHarness.scala ← riscv-tests 自動実行ハーネス
│
└── tests/
    ├── Makefile                  ← submodule → hex ビルドシステム
    ├── env/
    │   ├── riscv_test.h          ← カスタムテスト環境（CSR 不要）
    │   └── link.ld               ← リンカスクリプト（0x0 ベース）
    ├── scripts/
    │   └── elf2hex.py            ← ELF → $readmemh hex 変換
    ├── build/                    ← ELF 出力（git ignore）
    └── hex/                      ← .hex 出力（git ignore）
```

## セットアップ

### 1. リポジトリのクローン

```bash
git clone https://github.com/yourname/tile-riscv
cd tile-riscv

# submodule を初期化（riscv-tests + riscv-test-env）
git submodule update --init --recursive
```

### 2. ツールチェーンのインストール

```bash
# Ubuntu / Debian
sudo apt-get install gcc-riscv64-unknown-elf binutils-riscv64-unknown-elf

# macOS (Homebrew)
brew install riscv-gnu-toolchain

# 確認
riscv64-unknown-elf-gcc --version
```

### 3. Chisel / SBT

```bash
# JDK 11+ が必要
java --version

# SBT は https://www.scala-sbt.org からインストール
sbt --version
```

## テストの実行

### Step 1: riscv-tests から hex を生成

```bash
# rv32ui (RV32I 整数命令テスト) + rv32um (乗除算テスト) をビルド
make -C tests

# 生成されるファイル例
tests/hex/rv32ui-p-add.hex
tests/hex/rv32ui-p-addi.hex
...
tests/hex/rv32um-p-mul.hex
tests/hex/rv32um-p-div.hex
...

# テスト一覧を確認
make -C tests list
```

### Step 2: ChiselTest で実行

```bash
# 全テスト
sbt test

# RV32I テストのみ
sbt "testOnly tileriscv.RV32UITests"

# RV32M テストのみ
sbt "testOnly tileriscv.RV32UMTests"

# 特定のテスト（add 命令のみ）
sbt "testOnly tileriscv.RV32UITests -- -z add"
```

### Step 3: SystemVerilog を生成

```bash
sbt run
# → generated/TileArray.sv が出力される
```

## カスタム命令

RISC-V の CUSTOM-0 opcode (`0x0B`) を使用。

| 命令 | エンコーディング | 動作 |
|------|----------------|------|
| `TILE_SEND dir, rs1` | funct7[0]=1, funct3=dir | 自コアの出力レジスタ[dir] ← rs1 |
| `TILE_RECV rd, dir`  | funct7[0]=0, funct3=dir | rd ← 隣接コアの出力レジスタ[dir] |

方向: `0=NORTH`, `1=SOUTH`, `2=EAST`, `3=WEST`

## テスト環境の仕組み

標準の `riscv-tests/env/p/` は CSR 命令を多用するため、
本プロジェクトでは `tests/env/` にある独自のミニマル環境を使用します。

```
判定プロトコル（ecall halt 後に gp レジスタを確認）
  gp == 1                → PASS
  gp == (testnum<<1) | 1 → FAIL（testnum が失敗したテストケース番号）
```

## submodule の管理

```bash
# submodule の更新
git submodule update --remote riscv-tests

# 特定のコミットに固定（推奨）
cd riscv-tests
git checkout <commit-hash>
cd ..
git add riscv-tests
git commit -m "chore: pin riscv-tests to <commit-hash>"
```
