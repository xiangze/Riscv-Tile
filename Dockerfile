# =============================================================================
#  Dockerfile  ―  tile-riscv 開発・テスト環境
#
#  含まれるもの:
#    - OpenJDK 21           (Chisel / SBT に必要)
#    - SBT 1.10.x           (Scala ビルドツール)
#    - firtool 1.75.0       (Chisel 6 → SystemVerilog 変換)
#    - riscv64-unknown-elf  (bare-metal RISC-V クロスコンパイラ)
#    - Python 3             (elf2hex.py スクリプト)
#    - git                  (submodule 操作)
#
#  ビルド:
#    docker build -t tile-riscv .
#
#  使い方:
#    docker run --rm -it -v $(pwd):/work tile-riscv bash
#    docker run --rm -v $(pwd):/work tile-riscv make -C tests
#    docker run --rm -v $(pwd):/work tile-riscv sbt test
# =============================================================================

FROM ubuntu:24.04

# ── ビルド引数（バージョン固定用） ───────────────────────────────────────────
ARG FIRTOOL_VERSION=1.75.0
ARG SBT_VERSION=1.10.7
ARG DEBIAN_FRONTEND=noninteractive

LABEL maintainer="tile-riscv"
LABEL description="Chisel6 + RISC-V cross toolchain + riscv-tests build environment"

# =============================================================================
#  1. 基本パッケージ + Java + RISC-V ツールチェーン
# =============================================================================

RUN apt-get update && apt-get install -y --no-install-recommends \
    # ── ビルド基盤 ──────────────────────────────────────────────────────────
    curl \
    wget \
    git \
    make \
    ca-certificates \
    gnupg \
    # ── Java 21 (Chisel/SBT) ─────────────────────────────────────────────────
    openjdk-21-jdk-headless \
    # ── RISC-V bare-metal ツールチェーン ─────────────────────────────────────
    gcc-riscv64-unknown-elf \
    binutils-riscv64-unknown-elf \
    # ── Python 3（elf2hex.py） ────────────────────────────────────────────────
    python3 \
    python3-pip \
    # ── デバッグ・便利ツール ──────────────────────────────────────────────────
    file \
    xxd \
    && rm -rf /var/lib/apt/lists/*

# =============================================================================
#  2. SBT（Scala ビルドツール）
# =============================================================================

RUN curl -fsSL "https://github.com/sbt/sbt/releases/download/v${SBT_VERSION}/sbt-${SBT_VERSION}.tgz" \
    | tar -xz -C /usr/local \
    && ln -s /usr/local/sbt/bin/sbt /usr/local/bin/sbt

# =============================================================================
#  3. firtool（Chisel 6 が内部的に使用する MLIR ベース Verilog コンパイラ）
#
#  注: Chisel 6 は firtool を自動ダウンロードしようとするが、
#      コンテナ内では事前インストールしておく方が再現性が高い。
# =============================================================================

RUN ARCH=$(uname -m) && \
    case "$ARCH" in \
      x86_64)  FIRTOOL_ARCH=X64 ;; \
      aarch64) FIRTOOL_ARCH=ARM64 ;; \
      *) echo "Unsupported arch: $ARCH" && exit 1 ;; \
    esac && \
    wget -q "https://github.com/llvm/circt/releases/download/firtool-${FIRTOOL_VERSION}/firrtl-bin-linux-${FIRTOOL_ARCH}.tar.gz" \
    -O /tmp/firtool.tar.gz && \
    tar -xz -C /usr/local/bin -f /tmp/firtool.tar.gz \
        --strip-components=1 \
        "firtool-${FIRTOOL_VERSION}/bin/firtool" && \
    rm /tmp/firtool.tar.gz && \
    firtool --version

# =============================================================================
#  4. SBT キャッシュのウォームアップ
#     （最初の sbt 起動を高速化するため、Chisel 依存関係を事前解決）
# =============================================================================

WORKDIR /tmp/sbt-warmup

# 最小限の build.sbt だけで依存解決を実行
RUN cat > build.sbt << 'EOF'
ThisBuild / scalaVersion := "2.13.14"
val chiselVersion = "6.5.0"
lazy val root = (project in file(".")).settings(
  addCompilerPlugin("org.chipsalliance" % "chisel-plugin" % chiselVersion cross CrossVersion.full),
  libraryDependencies ++= Seq(
    "org.chipsalliance" %% "chisel"     % chiselVersion,
    "edu.berkeley.cs"   %% "chiseltest" % "6.0.0" % Test,
  ),
)
EOF

RUN mkdir -p project src/main/scala && \
    echo 'object Warmup extends App { println("ok") }' > src/main/scala/Warmup.scala && \
    sbt compile && \
    cd / && rm -rf /tmp/sbt-warmup

# =============================================================================
#  5. 作業ディレクトリ
# =============================================================================

WORKDIR /work

# ── ヘルスチェック ─────────────────────────────────────────────────────────
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
  CMD riscv64-unknown-elf-gcc --version && java -version && firtool --version

# ── デフォルトコマンド ─────────────────────────────────────────────────────
CMD ["bash"]
