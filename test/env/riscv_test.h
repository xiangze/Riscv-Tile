// =============================================================================
//  tests/env/riscv_test.h
//  TileRiscV 専用ミニマルテスト環境
//
//  標準 env/p の代替。CSR / 特権命令を一切使わない。
//
//  判定プロトコル（ecall halt 後に gp レジスタを確認）
//    gp == 1                → PASS
//    gp == (testnum<<1) | 1 → FAIL（testnum が失敗したテストケース番号）
// =============================================================================

#ifndef _ENV_TILESIM_H
#define _ENV_TILESIM_H

// ── ISA バリアント宣言（no-op init） ─────────────────────────────────────────
#define RVTEST_RV64U   .macro init; .endm
#define RVTEST_RV64UF  .macro init; .endm
#define RVTEST_RV64UV  .macro init; .endm
#define RVTEST_RV32U   .macro init; .endm
#define RVTEST_RV32UF  .macro init; .endm
#define RVTEST_RV32UV  .macro init; .endm
#define RVTEST_RV64M   .macro init; .endm
#define RVTEST_RV32M   .macro init; .endm

// ── コードセクション開始 ─────────────────────────────────────────────────────
// link.ld が _start を 0x0 に配置する
#define RVTEST_CODE_BEGIN                                               \
        .section .text.init;                                            \
        .align  4;                                                      \
        .globl  _start;                                                 \
_start:                                                                 \
        li gp, 0;                    /* TESTNUM = 0 */                  \
        li sp, 0x00010000;           /* スタックポインタ初期化 */

// ── コードセクション終端（到達したら無限ループ） ──────────────────────────────
#define RVTEST_CODE_END                                                 \
        unimp

// ── PASS: gp=1 で ecall（コアが halt） ───────────────────────────────────────
#define RVTEST_PASS                                                     \
        fence;                                                          \
        li  gp, 1;                                                      \
        ecall

// ── FAIL: gp=(testnum<<1)|1 で ecall ─────────────────────────────────────────
#define TESTNUM gp
#define RVTEST_FAIL                                                     \
        fence;                                                          \
1:      beqz TESTNUM, 1b;                                               \
        sll  TESTNUM, TESTNUM, 1;                                       \
        or   TESTNUM, TESTNUM, 1;                                       \
        ecall

// ── XLEN マスク ───────────────────────────────────────────────────────────────
#define MASK_XLEN(x) ((x) & 0xffffffff)

// ── データセクション ──────────────────────────────────────────────────────────
#define EXTRA_DATA

#define RVTEST_DATA_BEGIN                                               \
        EXTRA_DATA                                                      \
        .pushsection .tohost,"aw",@progbits;                            \
        .align 6; .global tohost;                                       \
tohost: .dword 0;                                                       \
        .align 6; .global fromhost;                                     \
fromhost: .dword 0;                                                     \
        .popsection;                                                    \
        .align 4; .global begin_signature; begin_signature:

#define RVTEST_DATA_END                                                 \
        .align 4; .global end_signature; end_signature:

#endif // _ENV_TILESIM_H
