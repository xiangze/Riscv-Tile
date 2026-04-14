# =============================================================================
#  Dockerfile  ―  tile-riscv 開発・テスト環境
#
#  含まれるもの:
#    - OpenJDK 21           (Chisel / SBT に必要)
#    - SBT 1.10.x           (Scala ビルドツール)
#    - firtool              (SBT warmup 時に Chisel が自動ダウンロード・キャッシュ)
#    - riscv64-unknown-elf  (bare-metal RISC-V クロスコンパイラ)
#    - Python 3             (elf2hex.py スクリプト)
#    - git                  (submodule 操作)
#
#  firtool について:
#    Chisel 6 は sbt compile 時に対応バージョンの firtool を
#    ~/.cache/coursier/... に自動ダウンロードして使用する。
#    手動インストールは不要（ファイル名がバージョンにより変わるため不安定）。
#    SBT warmup ステップで事前取得し、Docker レイヤーにキャッシュする。
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
ARG SBT_VERSION=1.10.7
ARG DEBIAN_FRONTEND=noninteractive

LABEL maintainer="tile-riscv"
LABEL description="Chisel6 + RISC-V cross toolchain + riscv-tests build environment"

# =============================================================================
#  1. 基本パッケージ + Java + RISC-V ツールチェーン
# =============================================================================

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    wget \
    git \
    make \
    ca-certificates \
    gnupg \
    openjdk-21-jdk-headless \
    gcc-riscv64-unknown-elf \
    binutils-riscv64-unknown-elf \
    python3 \
    python3-pip \
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
#  3. SBT キャッシュのウォームアップ
#
#  ここで sbt compile を実行することで:
#    - Chisel / ChiselTest の jar をダウンロード・キャッシュ
#    - Chisel が対応する firtool を ~/.cache/coursier に自動ダウンロード
#
#  firtool を手動インストールしない理由:
#    GitHub の CIRCT リリースはファイル名がバージョンにより変化する。
#      v1.75.0 以前: firrtl-bin-linux-x64.tar.gz
#      v1.76.0 以降: circt-full-shared-linux-x64.tar.gz
#    Chisel 組み込みのダウンローダーに任せる方が確実。
#
#  ウォームアップ用ファイルを COPY して使う（ヒアドキュメントは使わない）:
#    RUN cat > build.sbt << 'EOF' ... の形式は Docker のデフォルトパーサーが
#    "ThisBuild" などを Dockerfile 命令と誤認してエラーになるため。
# =============================================================================

WORKDIR /tmp/sbt-warmup

COPY docker/sbt-warmup/build.sbt                    ./build.sbt
COPY docker/sbt-warmup/src/main/scala/Warmup.scala  ./src/main/scala/Warmup.scala

RUN mkdir -p project && \
    sbt compile && \
    cd / && rm -rf /tmp/sbt-warmup

# =============================================================================
#  4. 作業ディレクトリ
# =============================================================================

WORKDIR /work

# ── ヘルスチェック ─────────────────────────────────────────────────────────
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
  CMD riscv64-unknown-elf-gcc --version && java -version

# ── デフォルトコマンド ─────────────────────────────────────────────────────
CMD ["bash"]
