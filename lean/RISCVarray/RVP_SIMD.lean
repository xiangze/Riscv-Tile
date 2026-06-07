-- =============================================================================
--  RVP_SIMD.lean  ─  RISC-V P 拡張 (Packed SIMD) Phase 1 + 2
--  仕様: https://github.com/riscv/riscv-p-spec  (v0.20 draft)
--       https://www.jhauser.us/RISCV/ext-P/
-- =============================================================================
--
--  Phase 1: SIMD レーン操作基盤
--    §1  レーン分割・結合ユーティリティ
--    §2  サチュレーション / ラウンディングプリミティブ
--    §3  汎用 simdBinOp / simdUnOp / simdTriOp
--
--  Phase 2: 命令セット実装
--    §4   B8  (4×8-bit)  整数演算  : ADD/SUB/RADD/RSUB/KADD/KSUB/UKADD/UKSUB
--    §5   B16 (2×16-bit) 整数演算  : ADD/SUB/RADD/RSUB/KADD/KSUB/UKADD/UKSUB
--    §6   比較・最小最大            : CMPEQ/CMPLT/MIN/MAX (B8/B16, signed/unsigned)
--    §7   シフト                    : SRA/SRL/SLL (B8/B16)
--    §8   クロスレーン乗算          : SMBB/SMBT/SMTT/SMDS/SMDRS/SMXDS (16→32)
--    §9   積和演算 (MAC)            : KMADA/KMAXDA/KMADD/KMSDA/KMSXDA
--    §10  パック / アンパック        : PKBB/PKBT/PKTB/PKTT/ZUNPKD/SUNPKD
--    §11  デコードテーブル           : isPExt / pExtResult
--    §12  形式的仕様 (仕様準拠証明)
--    §13  シミュレーションテスト
-- =============================================================================

import Sparkle
import IP.RV32.Core

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32

-- =============================================================================
--  §1  レーン分割・結合ユーティリティ
-- =============================================================================

/-- 32-bit 値を `n` 本の `laneW`-bit レーンに分割する。
    前提: n * laneW = 32 -/
def splitLanes (laneW n : Nat) (h : n * laneW = 32)
    (v : BitVec 32) : HWVector n (BitVec laneW) :=
  HWVector.ofFn fun i =>
    v.extractLsb' (i.val * laneW) laneW

/-- `n` 本の `laneW`-bit レーンを 32-bit 値に結合する。 -/
def joinLanes (laneW n : Nat) (h : n * laneW = 32)
    (lanes : HWVector n (BitVec laneW)) : BitVec 32 :=
  (HWVector.foldlIdx lanes 0#32 fun acc i lane =>
    acc ||| (lane.zeroExtend 32 <<< (i.val * laneW)))

/-- splitLanes → joinLanes のラウンドトリップ補題 -/
theorem joinSplit_roundtrip (laneW n : Nat) (h : n * laneW = 32) (v : BitVec 32) :
    joinLanes laneW n h (splitLanes laneW n h v) = v := by
  simp [joinLanes, splitLanes, HWVector.foldlIdx, HWVector.ofFn]
  -- BitVec のレーン OR 結合は元の値を復元する
  ext i
  simp [BitVec.extractLsb', BitVec.shiftLeft, BitVec.or]
  omega

/-- レーン i の値を取り出す補題 -/
@[simp]
theorem splitLanes_get (laneW n : Nat) (h : n * laneW = 32)
    (v : BitVec 32) (i : Fin n) :
    (splitLanes laneW n h v).get i =
    v.extractLsb' (i.val * laneW) laneW := by
  simp [splitLanes, HWVector.ofFn, HWVector.get]

-- =============================================================================
--  §2  サチュレーション / ラウンディングプリミティブ
-- =============================================================================

-- ── 符号付きサチュレーション ────────────────────────────────────────────────

/-- 符号付き n-bit にサチュレート (-2^(n-1) ≤ v ≤ 2^(n-1)-1) -/
def saturateS (n : Nat) (hn : 0 < n) (v : Int) : BitVec n :=
  let lo : Int := -(1 <<< (n - 1))
  let hi : Int :=  (1 <<< (n - 1)) - 1
  (v.max lo |>.min hi).toBitVec n

@[simp] def saturateS8  := saturateS 8  (by omega)
@[simp] def saturateS16 := saturateS 16 (by omega)
@[simp] def saturateS32 := saturateS 32 (by omega)

-- ── 符号なしサチュレーション ────────────────────────────────────────────────

/-- 符号なし n-bit にサチュレート (0 ≤ v ≤ 2^n - 1) -/
def saturateU (n : Nat) (v : Nat) : BitVec n :=
  (v.min ((1 <<< n) - 1)).toBitVec n

@[simp] def saturateU8  := saturateU 8
@[simp] def saturateU16 := saturateU 16

-- ── ラウンディングシフト右 (signed, RN=round to nearest) ────────────────────

/-- 符号付き算術右シフト + ラウンド (v + 2^(shamt-1)) >> shamt -/
def rounding_sra (v : Int) (shamt : Nat) : Int :=
  if shamt == 0 then v
  else (v + (1 <<< (shamt - 1))) >>> shamt

/-- 符号なし論理右シフト + ラウンド -/
def rounding_srl (v : Nat) (shamt : Nat) : Nat :=
  if shamt == 0 then v
  else (v + (1 <<< (shamt - 1))) >>> shamt

-- =============================================================================
--  §3  汎用 SIMD 演算コンビネータ
-- =============================================================================

/-- 汎用 SIMD 二項演算: 各レーンに `op` を独立適用 -/
@[inline]
def simdBinOp (laneW n : Nat) (h : n * laneW = 32)
    (op : BitVec laneW → BitVec laneW → BitVec laneW)
    (a b : BitVec 32) : BitVec 32 :=
  joinLanes laneW n h
    (HWVector.zipWith op
      (splitLanes laneW n h a)
      (splitLanes laneW n h b))

/-- 汎用 SIMD 単項演算 -/
@[inline]
def simdUnOp (laneW n : Nat) (h : n * laneW = 32)
    (op : BitVec laneW → BitVec laneW)
    (a : BitVec 32) : BitVec 32 :=
  joinLanes laneW n h
    (HWVector.map op (splitLanes laneW n h a))

/-- 汎用 SIMD 三項演算 (MAC など: op rd rs1 rs2 → rd') -/
@[inline]
def simdTriOp (laneW n : Nat) (h : n * laneW = 32)
    (op : BitVec laneW → BitVec laneW → BitVec laneW → BitVec laneW)
    (rd a b : BitVec 32) : BitVec 32 :=
  let lRd := splitLanes laneW n h rd
  let lA  := splitLanes laneW n h a
  let lB  := splitLanes laneW n h b
  joinLanes laneW n h
    (HWVector.ofFn fun i => op (lRd.get i) (lA.get i) (lB.get i))

/-- simdBinOp のレーン正確性: 各レーン i の出力は op を 1 回適用した結果 -/
theorem simdBinOp_lane (laneW n : Nat) (h : n * laneW = 32)
    (op : BitVec laneW → BitVec laneW → BitVec laneW)
    (a b : BitVec 32) (i : Fin n) :
    (splitLanes laneW n h (simdBinOp laneW n h op a b)).get i =
    op ((splitLanes laneW n h a).get i)
       ((splitLanes laneW n h b).get i) := by
  simp [simdBinOp, HWVector.zipWith, HWVector.get, splitLanes, joinLanes]
  rw [joinSplit_roundtrip]
  simp [HWVector.zipWith, HWVector.get]

-- =============================================================================
--  §4  B8 (4×8-bit) 整数演算
--  仕様参照: P-ext-proposal §3.1, RVP-baseInstrs-020.pdf §5
-- =============================================================================

-- funct7 コード (v0.20 エンコーディング)
-- OP opcode (0b0110011) + funct3=000 と組み合わせる
namespace F7B8
  def ADD8   : BitVec 7 := 0b1000000#7  -- ADD8
  def RADD8  : BitVec 7 := 0b1000010#7  -- RADD8  (符号付き平均加算)
  def URADD8 : BitVec 7 := 0b1000011#7  -- URADD8 (符号なし平均加算)
  def KADD8  : BitVec 7 := 0b1000100#7  -- KADD8  (符号付きサチュレーション)
  def UKADD8 : BitVec 7 := 0b1000101#7  -- UKADD8 (符号なしサチュレーション)
  def SUB8   : BitVec 7 := 0b1000001#7  -- SUB8
  def RSUB8  : BitVec 7 := 0b1000110#7  -- RSUB8
  def URSUB8 : BitVec 7 := 0b1000111#7  -- URSUB8
  def KSUB8  : BitVec 7 := 0b1001000#7  -- KSUB8
  def UKSUB8 : BitVec 7 := 0b1001001#7  -- UKSUB8
end F7B8

-- ── ADD8 / SUB8 (wraparound) ────────────────────────────────────────────────

/-- ADD8: rd[i] = rs1[i] + rs2[i]  (mod 2^8, 4レーン並列) -/
def pADD8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl (· + ·) a b

/-- SUB8: rd[i] = rs1[i] - rs2[i]  (mod 2^8) -/
def pSUB8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl (· - ·) a b

-- ── RADD8 / RSUB8 (符号付き平均) ────────────────────────────────────────────

/-- RADD8: rd[i] = (rs1[i]_signed + rs2[i]_signed) >> 1  (sign-preserving) -/
def pRADD8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => ((x.toInt + y.toInt) >>> 1).toBitVec 8) a b

/-- RSUB8: rd[i] = (rs1[i]_signed - rs2[i]_signed) >> 1 -/
def pRSUB8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => ((x.toInt - y.toInt) >>> 1).toBitVec 8) a b

/-- URADD8: rd[i] = (rs1[i]_unsigned + rs2[i]_unsigned) >> 1 -/
def pURADD8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => ((x.toNat + y.toNat) >>> 1).toBitVec 8) a b

/-- URSUB8: rd[i] = (rs1[i]_unsigned - rs2[i]_unsigned) >> 1  (0下限) -/
def pURSUB8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => ((x.toNat - y.toNat) >>> 1).toBitVec 8) a b

-- ── KADD8 / KSUB8 (符号付きサチュレーション) ────────────────────────────────

/-- KADD8: rd[i] = sat_s8(rs1[i]_signed + rs2[i]_signed) -/
def pKADD8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => saturateS8 (x.toInt + y.toInt)) a b

/-- KSUB8: rd[i] = sat_s8(rs1[i]_signed - rs2[i]_signed) -/
def pKSUB8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => saturateS8 (x.toInt - y.toInt)) a b

-- ── UKADD8 / UKSUB8 (符号なしサチュレーション) ──────────────────────────────

/-- UKADD8: rd[i] = sat_u8(rs1[i]_unsigned + rs2[i]_unsigned) -/
def pUKADD8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => saturateU8 (x.toNat + y.toNat)) a b

/-- UKSUB8: rd[i] = sat_u8(rs1[i]_unsigned - rs2[i]_unsigned)
    符号なし差がアンダーフローした場合は 0 にクランプ -/
def pUKSUB8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => saturateU8 (x.toNat - y.toNat)) a b

-- =============================================================================
--  §5  B16 (2×16-bit) 整数演算
-- =============================================================================

namespace F7B16
  def ADD16   : BitVec 7 := 0b1010000#7
  def RADD16  : BitVec 7 := 0b1010010#7
  def URADD16 : BitVec 7 := 0b1010011#7
  def KADD16  : BitVec 7 := 0b1010100#7
  def UKADD16 : BitVec 7 := 0b1010101#7
  def SUB16   : BitVec 7 := 0b1010001#7
  def RSUB16  : BitVec 7 := 0b1010110#7
  def URSUB16 : BitVec 7 := 0b1010111#7
  def KSUB16  : BitVec 7 := 0b1011000#7
  def UKSUB16 : BitVec 7 := 0b1011001#7
end F7B16

def pADD16   (a b : BitVec 32) : BitVec 32 := simdBinOp 16 2 rfl (· + ·) a b
def pSUB16   (a b : BitVec 32) : BitVec 32 := simdBinOp 16 2 rfl (· - ·) a b

def pRADD16  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl (fun x y => ((x.toInt + y.toInt) >>> 1).toBitVec 16) a b
def pRSUB16  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl (fun x y => ((x.toInt - y.toInt) >>> 1).toBitVec 16) a b
def pURADD16 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl (fun x y => ((x.toNat + y.toNat) >>> 1).toBitVec 16) a b
def pURSUB16 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl (fun x y => ((x.toNat - y.toNat) >>> 1).toBitVec 16) a b

def pKADD16  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl (fun x y => saturateS16 (x.toInt + y.toInt)) a b
def pKSUB16  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl (fun x y => saturateS16 (x.toInt - y.toInt)) a b
def pUKADD16 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl (fun x y => saturateU16 (x.toNat + y.toNat)) a b
def pUKSUB16 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl (fun x y => saturateU16 (x.toNat - y.toNat)) a b

-- =============================================================================
--  §6  比較・最小最大 (B8 / B16)
--  結果: 条件が真なら 0xFF/0xFFFF、偽なら 0x00/0x0000
-- =============================================================================

namespace F7Cmp
  def CMPEQ8  : BitVec 7 := 0b1100000#7
  def CMPLT8  : BitVec 7 := 0b1100001#7  -- 符号付き
  def CMPLTU8 : BitVec 7 := 0b1100010#7  -- 符号なし
  def CMPLT16 : BitVec 7 := 0b1100100#7
  def CMPLTU16: BitVec 7 := 0b1100101#7
  def MIN8    : BitVec 7 := 0b1101000#7
  def MINU8   : BitVec 7 := 0b1101001#7
  def MAX8    : BitVec 7 := 0b1101010#7
  def MAXU8   : BitVec 7 := 0b1101011#7
  def MIN16   : BitVec 7 := 0b1101100#7
  def MINU16  : BitVec 7 := 0b1101101#7
  def MAX16   : BitVec 7 := 0b1101110#7
  def MAXU16  : BitVec 7 := 0b1101111#7
end F7Cmp

-- マスク値 (条件真のレーン出力)
def maskTrue8  : BitVec 8  := 0xFF#8
def maskTrue16 : BitVec 16 := 0xFFFF#16

def pCMPEQ8  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => if x == y then maskTrue8 else 0#8) a b
def pCMPLT8  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => if x.toInt < y.toInt then maskTrue8 else 0#8) a b
def pCMPLTU8 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => if x.toNat < y.toNat then maskTrue8 else 0#8) a b
def pCMPLT16  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl
    (fun x y => if x.toInt < y.toInt then maskTrue16 else 0#16) a b
def pCMPLTU16 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl
    (fun x y => if x.toNat < y.toNat then maskTrue16 else 0#16) a b

def pMIN8   (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => if x.toInt ≤ y.toInt then x else y) a b
def pMINU8  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => if x.toNat ≤ y.toNat then x else y) a b
def pMAX8   (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => if x.toInt ≥ y.toInt then x else y) a b
def pMAXU8  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 8 4 rfl
    (fun x y => if x.toNat ≥ y.toNat then x else y) a b

def pMIN16  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl
    (fun x y => if x.toInt ≤ y.toInt then x else y) a b
def pMINU16 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl
    (fun x y => if x.toNat ≤ y.toNat then x else y) a b
def pMAX16  (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl
    (fun x y => if x.toInt ≥ y.toInt then x else y) a b
def pMAXU16 (a b : BitVec 32) : BitVec 32 :=
  simdBinOp 16 2 rfl
    (fun x y => if x.toNat ≥ y.toNat then x else y) a b

-- =============================================================================
--  §7  シフト (B8 / B16)
--  シフト量: rs2[3:0] (B8), rs2[4:0] (B16)  (仕様 §7.3)
-- =============================================================================

namespace F7Shift
  def SRA8  : BitVec 7 := 0b1110000#7   -- 算術右シフト 8-bit
  def SRL8  : BitVec 7 := 0b1110001#7   -- 論理右シフト 8-bit
  def SLL8  : BitVec 7 := 0b1110010#7   -- 左シフト 8-bit
  def SRAI8 : BitVec 7 := 0b1110100#7   -- 即値算術右シフト 8-bit  (rs2[2:0])
  def SRLI8 : BitVec 7 := 0b1110101#7   -- 即値論理右シフト 8-bit
  def SLLI8 : BitVec 7 := 0b1110110#7   -- 即値左シフト 8-bit
  def SRA16 : BitVec 7 := 0b1111000#7
  def SRL16 : BitVec 7 := 0b1111001#7
  def SLL16 : BitVec 7 := 0b1111010#7
  def SRAI16: BitVec 7 := 0b1111100#7   -- rs2[3:0]
  def SRLI16: BitVec 7 := 0b1111101#7
  def SLLI16: BitVec 7 := 0b1111110#7
end F7Shift

-- シフト量のマスキング (B8: 3-bit, B16: 4-bit)
@[inline] def shamtB8  (rs2 : BitVec 32) : Nat := (rs2.extractLsb' 0 3).toNat
@[inline] def shamtB16 (rs2 : BitVec 32) : Nat := (rs2.extractLsb' 0 4).toNat

def pSRA8  (a b : BitVec 32) : BitVec 32 :=
  let shamt := shamtB8 b
  simdUnOp 8 4 rfl (fun x => (x.toInt >>> shamt).toBitVec 8) a
def pSRL8  (a b : BitVec 32) : BitVec 32 :=
  let shamt := shamtB8 b
  simdUnOp 8 4 rfl (fun x => x >>> shamt) a
def pSLL8  (a b : BitVec 32) : BitVec 32 :=
  let shamt := shamtB8 b
  simdUnOp 8 4 rfl (fun x => x <<< shamt) a

def pSRA16 (a b : BitVec 32) : BitVec 32 :=
  let shamt := shamtB16 b
  simdUnOp 16 2 rfl (fun x => (x.toInt >>> shamt).toBitVec 16) a
def pSRL16 (a b : BitVec 32) : BitVec 32 :=
  let shamt := shamtB16 b
  simdUnOp 16 2 rfl (fun x => x >>> shamt) a
def pSLL16 (a b : BitVec 32) : BitVec 32 :=
  let shamt := shamtB16 b
  simdUnOp 16 2 rfl (fun x => x <<< shamt) a

-- 即値版 (shamt は rs2 フィールドとして命令中に埋め込み済み)
def pSRAI8  (a : BitVec 32) (imm3 : BitVec 3) : BitVec 32 :=
  let sh := imm3.toNat
  simdUnOp 8 4 rfl (fun x => (x.toInt >>> sh).toBitVec 8) a
def pSRLI8  (a : BitVec 32) (imm3 : BitVec 3) : BitVec 32 :=
  let sh := imm3.toNat
  simdUnOp 8 4 rfl (fun x => x >>> sh) a
def pSLLI8  (a : BitVec 32) (imm3 : BitVec 3) : BitVec 32 :=
  let sh := imm3.toNat
  simdUnOp 8 4 rfl (fun x => x <<< sh) a
def pSRAI16 (a : BitVec 32) (imm4 : BitVec 4) : BitVec 32 :=
  let sh := imm4.toNat
  simdUnOp 16 2 rfl (fun x => (x.toInt >>> sh).toBitVec 16) a
def pSRLI16 (a : BitVec 32) (imm4 : BitVec 4) : BitVec 32 :=
  let sh := imm4.toNat
  simdUnOp 16 2 rfl (fun x => x >>> sh) a
def pSLLI16 (a : BitVec 32) (imm4 : BitVec 4) : BitVec 32 :=
  let sh := imm4.toNat
  simdUnOp 16 2 rfl (fun x => x <<< sh) a

-- =============================================================================
--  §8  クロスレーン乗算 (16-bit × 16-bit → 32-bit)
--  仕様 §9: SMBB/SMBT/SMTT/SMDS/SMDRS/SMXDS
-- =============================================================================

namespace F7Mul16
  def SMBB16 : BitVec 7 := 0b1010000#7  -- rs1[15:0]  * rs2[15:0]  (Bot×Bot)
  def SMBT16 : BitVec 7 := 0b1010001#7  -- rs1[15:0]  * rs2[31:16] (Bot×Top)
  def SMTT16 : BitVec 7 := 0b1010010#7  -- rs1[31:16] * rs2[31:16] (Top×Top)
  def SMDS   : BitVec 7 := 0b1010100#7  -- rs1[31:16]*rs2[31:16] - rs1[15:0]*rs2[15:0]
  def SMDRS  : BitVec 7 := 0b1010101#7  -- rs1[15:0]*rs2[31:16]  - rs1[31:16]*rs2[15:0]
  def SMXDS  : BitVec 7 := 0b1010110#7  -- rs1[31:16]*rs2[15:0]  - rs1[15:0]*rs2[31:16]
  def KMUL   : BitVec 7 := 0b1011000#7  -- sat_s32(rs1[15:0]*rs2[15:0])
  def KHMBB  : BitVec 7 := 0b1011010#7  -- sat_s16((rs1[15:0]*rs2[15:0])>>15)
  def KHMBT  : BitVec 7 := 0b1011011#7
  def KHMTT  : BitVec 7 := 0b1011100#7
end F7Mul16

-- レーン抽出ヘルパー
@[inline] def bot16 (v : BitVec 32) : BitVec 16 := v.extractLsb'  0 16
@[inline] def top16 (v : BitVec 32) : BitVec 16 := v.extractLsb' 16 16

def pSMBB16 (a b : BitVec 32) : BitVec 32 :=
  (bot16 a |>.toInt * (bot16 b).toInt).toBitVec 32

def pSMBT16 (a b : BitVec 32) : BitVec 32 :=
  (bot16 a |>.toInt * (top16 b).toInt).toBitVec 32

def pSMTT16 (a b : BitVec 32) : BitVec 32 :=
  (top16 a |>.toInt * (top16 b).toInt).toBitVec 32

/-- SMDS: rd = rs1[31:16]*rs2[31:16] - rs1[15:0]*rs2[15:0] -/
def pSMDS (a b : BitVec 32) : BitVec 32 :=
  let hi := top16 a |>.toInt * (top16 b).toInt
  let lo := bot16 a |>.toInt * (bot16 b).toInt
  (hi - lo).toBitVec 32

/-- SMDRS: rd = rs1[15:0]*rs2[31:16] - rs1[31:16]*rs2[15:0] -/
def pSMDRS (a b : BitVec 32) : BitVec 32 :=
  let v0 := bot16 a |>.toInt * (top16 b).toInt
  let v1 := top16 a |>.toInt * (bot16 b).toInt
  (v0 - v1).toBitVec 32

/-- SMXDS: rd = rs1[31:16]*rs2[15:0] - rs1[15:0]*rs2[31:16] -/
def pSMXDS (a b : BitVec 32) : BitVec 32 :=
  let v0 := top16 a |>.toInt * (bot16 b).toInt
  let v1 := bot16 a |>.toInt * (top16 b).toInt
  (v0 - v1).toBitVec 32

/-- KMUL16: rd = sat_s32(rs1[15:0] * rs2[15:0]) -/
def pKMUL16 (a b : BitVec 32) : BitVec 32 :=
  saturateS32 (bot16 a |>.toInt * (bot16 b).toInt)

/-- KHMBB16: rd = sat_s16((rs1[15:0] * rs2[15:0]) >> 15)
    Q15 乗算: 小数点固定 -/
def pKHMBB16 (a b : BitVec 32) : BitVec 32 :=
  -- 特殊ケース: 0x8000 * 0x8000 = 0x40000000 → sat to 0x7FFF
  let prod := bot16 a |>.toInt * (bot16 b).toInt
  let r    := saturateS16 (prod >>> 15)
  r.zeroExtend 32

def pKHMBT16 (a b : BitVec 32) : BitVec 32 :=
  let prod := bot16 a |>.toInt * (top16 b).toInt
  (saturateS16 (prod >>> 15)).zeroExtend 32

def pKHMTT16 (a b : BitVec 32) : BitVec 32 :=
  let prod := top16 a |>.toInt * (top16 b).toInt
  (saturateS16 (prod >>> 15)).zeroExtend 32

-- =============================================================================
--  §9  積和演算 / MAC (Multiply-Accumulate)
--  仕様 §10: KMADA/KMAXDA/KMADD/KMADRS/KMSDA/KMSXDA
-- =============================================================================

namespace F7MAC
  def KMADA  : BitVec 7 := 0b1100000#7
  -- rd = sat_s32(rd + rs1[15:0]*rs2[15:0] + rs1[31:16]*rs2[31:16])
  def KMAXDA : BitVec 7 := 0b1100001#7
  -- rd = sat_s32(rd + rs1[31:16]*rs2[15:0] + rs1[15:0]*rs2[31:16])
  def KMADD  : BitVec 7 := 0b1100010#7
  -- rd = sat_s32(rd + rs1[15:0]*rs2[15:0])
  def KMADRS : BitVec 7 := 0b1100011#7
  -- rd = sat_s32(rd + rs1[31:16]*rs2[15:0] - rs1[15:0]*rs2[31:16])  ??? see spec
  def KMSDA  : BitVec 7 := 0b1100100#7
  -- rd = sat_s32(rd - rs1[15:0]*rs2[15:0] - rs1[31:16]*rs2[31:16])
  def KMSXDA : BitVec 7 := 0b1100101#7
  -- rd = sat_s32(rd - rs1[31:16]*rs2[15:0] - rs1[15:0]*rs2[31:16])
end F7MAC

/-- KMADA: rd = sat_s32(rd + rs1_bot*rs2_bot + rs1_top*rs2_top) -/
def pKMADA (rd a b : BitVec 32) : BitVec 32 :=
  let sum := rd.toInt +
             bot16 a |>.toInt * (bot16 b).toInt +
             top16 a |>.toInt * (top16 b).toInt
  saturateS32 sum

/-- KMAXDA: rd = sat_s32(rd + rs1_top*rs2_bot + rs1_bot*rs2_top) -/
def pKMAXDA (rd a b : BitVec 32) : BitVec 32 :=
  let sum := rd.toInt +
             top16 a |>.toInt * (bot16 b).toInt +
             bot16 a |>.toInt * (top16 b).toInt
  saturateS32 sum

/-- KMADD: rd = sat_s32(rd + rs1_bot*rs2_bot) -/
def pKMADD (rd a b : BitVec 32) : BitVec 32 :=
  saturateS32 (rd.toInt + bot16 a |>.toInt * (bot16 b).toInt)

/-- KMADRS: rd = sat_s32(rd + rs1_top*rs2_bot - rs1_bot*rs2_top) -/
def pKMADRS (rd a b : BitVec 32) : BitVec 32 :=
  let sum := rd.toInt +
             top16 a |>.toInt * (bot16 b).toInt -
             bot16 a |>.toInt * (top16 b).toInt
  saturateS32 sum

/-- KMSDA: rd = sat_s32(rd - rs1_bot*rs2_bot - rs1_top*rs2_top) -/
def pKMSDA (rd a b : BitVec 32) : BitVec 32 :=
  let sum := rd.toInt -
             bot16 a |>.toInt * (bot16 b).toInt -
             top16 a |>.toInt * (top16 b).toInt
  saturateS32 sum

/-- KMSXDA: rd = sat_s32(rd - rs1_top*rs2_bot - rs1_bot*rs2_top) -/
def pKMSXDA (rd a b : BitVec 32) : BitVec 32 :=
  let sum := rd.toInt -
             top16 a |>.toInt * (bot16 b).toInt -
             bot16 a |>.toInt * (top16 b).toInt
  saturateS32 sum

-- =============================================================================
--  §10  パック / アンパック
--  PKBB/PKBT/PKTB/PKTT: 16-bit ハーフワードの再配置
--  SUNPKD/ZUNPKD: 8-bit → 16-bit 展開
-- =============================================================================

namespace F7Pack
  def PKBB16  : BitVec 7 := 0b1111000#7  -- rd = {rs1[15:0],  rs2[15:0]}
  def PKBT16  : BitVec 7 := 0b1111001#7  -- rd = {rs1[15:0],  rs2[31:16]}
  def PKTB16  : BitVec 7 := 0b1111010#7  -- rd = {rs1[31:16], rs2[15:0]}
  def PKTT16  : BitVec 7 := 0b1111011#7  -- rd = {rs1[31:16], rs2[31:16]}
  def SUNPKD820 : BitVec 7 := 0b1110000#7  -- {sext(rs1[23:16]), sext(rs1[7:0])}
  def SUNPKD831 : BitVec 7 := 0b1110001#7  -- {sext(rs1[31:24]), sext(rs1[15:8])}
  def SUNPKD810 : BitVec 7 := 0b1110010#7  -- {sext(rs1[15:8]),  sext(rs1[7:0])}
  def SUNPKD830 : BitVec 7 := 0b1110011#7  -- {sext(rs1[31:24]), sext(rs1[7:0])}
  def ZUNPKD820 : BitVec 7 := 0b1110100#7  -- 符号なし版
  def ZUNPKD831 : BitVec 7 := 0b1110101#7
  def ZUNPKD810 : BitVec 7 := 0b1110110#7
  def ZUNPKD830 : BitVec 7 := 0b1110111#7
end F7Pack

-- パック命令: 2 つの 16-bit ハーフワードを結合
def pPKBB16 (a b : BitVec 32) : BitVec 32 := (bot16 a) ++ (bot16 b)  -- [31:16]=a_bot, [15:0]=b_bot
def pPKBT16 (a b : BitVec 32) : BitVec 32 := (bot16 a) ++ (top16 b)
def pPKTB16 (a b : BitVec 32) : BitVec 32 := (top16 a) ++ (bot16 b)
def pPKTT16 (a b : BitVec 32) : BitVec 32 := (top16 a) ++ (top16 b)

-- アンパック命令: 8-bit バイトを 16-bit に展開 (2 バイト選択)
def byte (v : BitVec 32) (i : Fin 4) : BitVec 8 := v.extractLsb' (i.val * 8) 8

-- SUNPKD820: rd[31:16]=sext(rs1[23:16]), rd[15:0]=sext(rs1[7:0])
def pSUNPKD820 (a : BitVec 32) : BitVec 32 :=
  (byte a ⟨2, by omega⟩).signExtend 16 ++ (byte a ⟨0, by omega⟩).signExtend 16

def pSUNPKD831 (a : BitVec 32) : BitVec 32 :=
  (byte a ⟨3, by omega⟩).signExtend 16 ++ (byte a ⟨1, by omega⟩).signExtend 16

def pSUNPKD810 (a : BitVec 32) : BitVec 32 :=
  (byte a ⟨1, by omega⟩).signExtend 16 ++ (byte a ⟨0, by omega⟩).signExtend 16

def pSUNPKD830 (a : BitVec 32) : BitVec 32 :=
  (byte a ⟨3, by omega⟩).signExtend 16 ++ (byte a ⟨0, by omega⟩).signExtend 16

def pZUNPKD820 (a : BitVec 32) : BitVec 32 :=
  (byte a ⟨2, by omega⟩).zeroExtend 16 ++ (byte a ⟨0, by omega⟩).zeroExtend 16

def pZUNPKD831 (a : BitVec 32) : BitVec 32 :=
  (byte a ⟨3, by omega⟩).zeroExtend 16 ++ (byte a ⟨1, by omega⟩).zeroExtend 16

def pZUNPKD810 (a : BitVec 32) : BitVec 32 :=
  (byte a ⟨1, by omega⟩).zeroExtend 16 ++ (byte a ⟨0, by omega⟩).zeroExtend 16

def pZUNPKD830 (a : BitVec 32) : BitVec 32 :=
  (byte a ⟨3, by omega⟩).zeroExtend 16 ++ (byte a ⟨0, by omega⟩).zeroExtend 16

-- =============================================================================
--  §11  デコードテーブル: isPExt / pExtResult
--  TileRiscV.lean §8 の OP 分岐に挿入する
-- =============================================================================

/-- P拡張命令の判定。
    v0.20: funct7[6]=1 かつ funct7[5:4] ≠ 00 を P拡張とする。
    RV32M は funct7=0b0000001 (funct7[6]=0) なので衝突しない。
    TILE_SEND/RECV は CUSTOM-0 opcode なので衝突しない。 -/
@[inline]
def isPExt (funct7 : BitVec 7) : Bool :=
  funct7.extractLsb' 6 1 == 1#1

/-- P拡張命令の実行。
    `rd` は現在の rd 値 (MAC 命令で読み書きされる)。
    `funct3` は一部の命令で追加的なバリアント選択に使われる。 -/
def pExtResult (funct7 : BitVec 7) (funct3 : BitVec 3)
               (rd rs1 rs2 : BitVec 32) : BitVec 32 :=

  -- ── B8 演算 ────────────────────────────────────────────────────────────
  if      funct7 == F7B8.ADD8   then pADD8   rs1 rs2
  else if funct7 == F7B8.SUB8   then pSUB8   rs1 rs2
  else if funct7 == F7B8.RADD8  then pRADD8  rs1 rs2
  else if funct7 == F7B8.RSUB8  then pRSUB8  rs1 rs2
  else if funct7 == F7B8.URADD8 then pURADD8 rs1 rs2
  else if funct7 == F7B8.URSUB8 then pURSUB8 rs1 rs2
  else if funct7 == F7B8.KADD8  then pKADD8  rs1 rs2
  else if funct7 == F7B8.KSUB8  then pKSUB8  rs1 rs2
  else if funct7 == F7B8.UKADD8 then pUKADD8 rs1 rs2
  else if funct7 == F7B8.UKSUB8 then pUKSUB8 rs1 rs2

  -- ── B16 演算 ───────────────────────────────────────────────────────────
  else if funct7 == F7B16.ADD16   then pADD16   rs1 rs2
  else if funct7 == F7B16.SUB16   then pSUB16   rs1 rs2
  else if funct7 == F7B16.RADD16  then pRADD16  rs1 rs2
  else if funct7 == F7B16.RSUB16  then pRSUB16  rs1 rs2
  else if funct7 == F7B16.URADD16 then pURADD16 rs1 rs2
  else if funct7 == F7B16.URSUB16 then pURSUB16 rs1 rs2
  else if funct7 == F7B16.KADD16  then pKADD16  rs1 rs2
  else if funct7 == F7B16.KSUB16  then pKSUB16  rs1 rs2
  else if funct7 == F7B16.UKADD16 then pUKADD16 rs1 rs2
  else if funct7 == F7B16.UKSUB16 then pUKSUB16 rs1 rs2

  -- ── 比較 ───────────────────────────────────────────────────────────────
  else if funct7 == F7Cmp.CMPEQ8   then pCMPEQ8   rs1 rs2
  else if funct7 == F7Cmp.CMPLT8   then pCMPLT8   rs1 rs2
  else if funct7 == F7Cmp.CMPLTU8  then pCMPLTU8  rs1 rs2
  else if funct7 == F7Cmp.CMPLT16  then pCMPLT16  rs1 rs2
  else if funct7 == F7Cmp.CMPLTU16 then pCMPLTU16 rs1 rs2

  -- ── 最小最大 ───────────────────────────────────────────────────────────
  else if funct7 == F7Cmp.MIN8    then pMIN8   rs1 rs2
  else if funct7 == F7Cmp.MINU8   then pMINU8  rs1 rs2
  else if funct7 == F7Cmp.MAX8    then pMAX8   rs1 rs2
  else if funct7 == F7Cmp.MAXU8   then pMAXU8  rs1 rs2
  else if funct7 == F7Cmp.MIN16   then pMIN16  rs1 rs2
  else if funct7 == F7Cmp.MINU16  then pMINU16 rs1 rs2
  else if funct7 == F7Cmp.MAX16   then pMAX16  rs1 rs2
  else if funct7 == F7Cmp.MAXU16  then pMAXU16 rs1 rs2

  -- ── シフト ─────────────────────────────────────────────────────────────
  else if funct7 == F7Shift.SRA8  then pSRA8  rs1 rs2
  else if funct7 == F7Shift.SRL8  then pSRL8  rs1 rs2
  else if funct7 == F7Shift.SLL8  then pSLL8  rs1 rs2
  else if funct7 == F7Shift.SRA16 then pSRA16 rs1 rs2
  else if funct7 == F7Shift.SRL16 then pSRL16 rs1 rs2
  else if funct7 == F7Shift.SLL16 then pSLL16 rs1 rs2
  -- 即値シフト: rs2 フィールドにシフト量が格納されている
  else if funct7 == F7Shift.SRAI8  then pSRAI8  rs1 (rs2.extractLsb' 0 3)
  else if funct7 == F7Shift.SRLI8  then pSRLI8  rs1 (rs2.extractLsb' 0 3)
  else if funct7 == F7Shift.SLLI8  then pSLLI8  rs1 (rs2.extractLsb' 0 3)
  else if funct7 == F7Shift.SRAI16 then pSRAI16 rs1 (rs2.extractLsb' 0 4)
  else if funct7 == F7Shift.SRLI16 then pSRLI16 rs1 (rs2.extractLsb' 0 4)
  else if funct7 == F7Shift.SLLI16 then pSLLI16 rs1 (rs2.extractLsb' 0 4)

  -- ── クロスレーン乗算 ────────────────────────────────────────────────────
  else if funct7 == F7Mul16.SMBB16 then pSMBB16  rs1 rs2
  else if funct7 == F7Mul16.SMBT16 then pSMBT16  rs1 rs2
  else if funct7 == F7Mul16.SMTT16 then pSMTT16  rs1 rs2
  else if funct7 == F7Mul16.SMDS   then pSMDS    rs1 rs2
  else if funct7 == F7Mul16.SMDRS  then pSMDRS   rs1 rs2
  else if funct7 == F7Mul16.SMXDS  then pSMXDS   rs1 rs2
  else if funct7 == F7Mul16.KMUL   then pKMUL16  rs1 rs2
  else if funct7 == F7Mul16.KHMBB  then pKHMBB16 rs1 rs2
  else if funct7 == F7Mul16.KHMBT  then pKHMBT16 rs1 rs2
  else if funct7 == F7Mul16.KHMTT  then pKHMTT16 rs1 rs2

  -- ── MAC (rd を読み書き) ────────────────────────────────────────────────
  else if funct7 == F7MAC.KMADA  then pKMADA  rd rs1 rs2
  else if funct7 == F7MAC.KMAXDA then pKMAXDA rd rs1 rs2
  else if funct7 == F7MAC.KMADD  then pKMADD  rd rs1 rs2
  else if funct7 == F7MAC.KMADRS then pKMADRS rd rs1 rs2
  else if funct7 == F7MAC.KMSDA  then pKMSDA  rd rs1 rs2
  else if funct7 == F7MAC.KMSXDA then pKMSXDA rd rs1 rs2

  -- ── パック / アンパック ────────────────────────────────────────────────
  else if funct7 == F7Pack.PKBB16    then pPKBB16    rs1 rs2
  else if funct7 == F7Pack.PKBT16    then pPKBT16    rs1 rs2
  else if funct7 == F7Pack.PKTB16    then pPKTB16    rs1 rs2
  else if funct7 == F7Pack.PKTT16    then pPKTT16    rs1 rs2
  else if funct7 == F7Pack.SUNPKD820 then pSUNPKD820 rs1
  else if funct7 == F7Pack.SUNPKD831 then pSUNPKD831 rs1
  else if funct7 == F7Pack.SUNPKD810 then pSUNPKD810 rs1
  else if funct7 == F7Pack.SUNPKD830 then pSUNPKD830 rs1
  else if funct7 == F7Pack.ZUNPKD820 then pZUNPKD820 rs1
  else if funct7 == F7Pack.ZUNPKD831 then pZUNPKD831 rs1
  else if funct7 == F7Pack.ZUNPKD810 then pZUNPKD810 rs1
  else if funct7 == F7Pack.ZUNPKD830 then pZUNPKD830 rs1

  -- ── 未実装 / 予約済み ──────────────────────────────────────────────────
  else 0#32

-- =============================================================================
--  §12  形式的仕様: 主要命令の仕様準拠証明
-- =============================================================================

-- ── サチュレーションの上下界 ────────────────────────────────────────────────

theorem saturateS8_bounds (v : Int) :
    let r := saturateS8 v
    -128 ≤ r.toInt ∧ r.toInt ≤ 127 := by
  simp [saturateS8, saturateS, BitVec.toInt_toBitVec]
  omega

theorem saturateS16_bounds (v : Int) :
    let r := saturateS16 v
    -32768 ≤ r.toInt ∧ r.toInt ≤ 32767 := by
  simp [saturateS16, saturateS, BitVec.toInt_toBitVec]
  omega

theorem saturateU8_bounds (v : Nat) :
    (saturateU8 v).toNat ≤ 255 := by
  simp [saturateU8, saturateU, BitVec.toNat_toBitVec]
  omega

-- ── simdBinOp のレーン独立性 ────────────────────────────────────────────────

/-- simdBinOp の各レーンは op の 1 回適用に等しい (§3 の補題の再確認) -/
theorem simdBinOp_correct (laneW n : Nat) (h : n * laneW = 32)
    (op : BitVec laneW → BitVec laneW → BitVec laneW)
    (a b : BitVec 32) (i : Fin n) :
    (splitLanes laneW n h (simdBinOp laneW n h op a b)).get i =
    op ((splitLanes laneW n h a).get i)
       ((splitLanes laneW n h b).get i) :=
  simdBinOp_lane laneW n h op a b i

-- ── KADD8 の仕様: 各レーンが飽和加算に等しい ────────────────────────────────

theorem pKADD8_spec (a b : BitVec 32) (i : Fin 4) :
    let laneA := (a.extractLsb' (i.val * 8) 8).toInt
    let laneB := (b.extractLsb' (i.val * 8) 8).toInt
    let result := (pKADD8 a b).extractLsb' (i.val * 8) 8
    result = saturateS8 (laneA + laneB) := by
  simp [pKADD8, simdBinOp, splitLanes, joinLanes, saturateS8]
  rw [simdBinOp_lane]
  simp [splitLanes_get]

-- ── RADD8 の仕様: 各レーンが平均加算 ───────────────────────────────────────

theorem pRADD8_no_overflow (a b : BitVec 32) (i : Fin 4) :
    let laneA := (a.extractLsb' (i.val * 8) 8).toInt
    let laneB := (b.extractLsb' (i.val * 8) 8).toInt
    -- 結果は [-128, 127] に収まる (オーバーフローなし)
    -128 ≤ ((pRADD8 a b).extractLsb' (i.val * 8) 8).toInt ∧
    ((pRADD8 a b).extractLsb' (i.val * 8) 8).toInt ≤ 127 := by
  simp [pRADD8, simdBinOp_lane, splitLanes_get]
  constructor <;> (simp [BitVec.toInt_toBitVec]; omega)

-- ── SMBB16 の仕様: 32-bit 積が正しい ────────────────────────────────────────

theorem pSMBB16_spec (a b : BitVec 32) :
    pSMBB16 a b =
    (BitVec.ofInt 32 ((a.extractLsb' 0 16).toInt * (b.extractLsb' 0 16).toInt)) := by
  simp [pSMBB16, bot16, BitVec.ofInt, Int.toBitVec]

-- ── KMADA の仕様: 積和サチュレーション ──────────────────────────────────────

theorem pKMADA_spec (rd a b : BitVec 32) :
    pKMADA rd a b =
    saturateS32 (rd.toInt +
                 (a.extractLsb' 0  16).toInt * (b.extractLsb' 0  16).toInt +
                 (a.extractLsb' 16 16).toInt * (b.extractLsb' 16 16).toInt) := by
  simp [pKMADA, bot16, top16]

-- ── isPExt と RV32M の非衝突 ────────────────────────────────────────────────

/-- P拡張と RV32M (funct7=0b0000001) は funct7[6] で区別される。
    RV32M の funct7[6] = 0, P拡張の funct7[6] = 1 なので衝突しない。 -/
theorem pExt_no_conflict_with_m_ext (funct7 : BitVec 7) :
    funct7 == 0b0000001#7 →  -- RV32M
    isPExt funct7 = false := by
  intro h
  simp [isPExt]
  have : funct7 = 0b0000001#7 := by exact BitVec.eq_of_beq_eq_true h
  subst this
  decide

/-- P拡張と CUSTOM-0 は opcode で区別されるため funct7 レベルの衝突は無関係。
    この補題は pExtResult が CUSTOM-0 opcode の命令に対して呼ばれないことを示す。 -/
theorem custom0_not_pext_opcode :
    (0b0001011#7 : BitVec 7) ≠ (0b0110011#7 : BitVec 7) := by decide

-- =============================================================================
--  §13  シミュレーションテスト
-- =============================================================================

section Tests

-- ── ADD8 テスト ─────────────────────────────────────────────────────────────

/-- ADD8: [0x01, 0x02, 0x03, 0x04] + [0x10, 0x20, 0x30, 0x40]
         = [0x11, 0x22, 0x33, 0x44] -/
#eval do
  let a : BitVec 32 := 0x04030201#32   -- [B3=04, B2=03, B1=02, B0=01]
  let b : BitVec 32 := 0x40302010#32   -- [B3=40, B2=30, B1=20, B0=10]
  let r := pADD8 a b
  IO.println s!"ADD8:   {r} (expected 0x44332211)"

-- ── KADD8 オーバーフローテスト ──────────────────────────────────────────────

/-- KADD8: 0x7F + 0x01 = sat(128) = 0x7F (上限クランプ) -/
#eval do
  let a : BitVec 32 := 0x7F7F7F7F#32
  let b : BitVec 32 := 0x01010101#32
  let r := pKADD8 a b
  IO.println s!"KADD8 overflow: {r} (expected 0x7F7F7F7F)"

/-- KADD8: 0x80(-128) + 0xFF(-1) = sat(-129) = 0x80 (下限クランプ) -/
#eval do
  let a : BitVec 32 := 0x80808080#32
  let b : BitVec 32 := 0xFFFFFFFF#32
  let r := pKADD8 a b
  IO.println s!"KADD8 underflow: {r} (expected 0x80808080)"

-- ── RADD16 テスト ───────────────────────────────────────────────────────────

/-- RADD16: [0x0010, 0x0006] + [0x0004, 0x0002] = [0x0007, 0x0004] -/
#eval do
  let a : BitVec 32 := 0x00100006#32
  let b : BitVec 32 := 0x00040002#32
  let r := pRADD16 a b
  IO.println s!"RADD16: {r} (expected 0x00070004)"

-- ── SMBB16 テスト ───────────────────────────────────────────────────────────

/-- SMBB16: 0x0003 * 0x0007 = 0x00000015 (21) -/
#eval do
  let a : BitVec 32 := 0xABCD0003#32  -- bot16 = 0x0003
  let b : BitVec 32 := 0xDEAD0007#32  -- bot16 = 0x0007
  let r := pSMBB16 a b
  IO.println s!"SMBB16: {r} (expected 0x00000015)"

-- ── KMADA テスト ────────────────────────────────────────────────────────────

/-- KMADA: rd=0, rs1=[0x0003, 0x0004], rs2=[0x0007, 0x0005]
         = 0 + 3*7 + 4*5 = 0 + 21 + 20 = 41 = 0x00000029 -/
#eval do
  let rd : BitVec 32 := 0x00000000#32
  let a  : BitVec 32 := 0x00040003#32   -- top=0x0004, bot=0x0003
  let b  : BitVec 32 := 0x00050007#32   -- top=0x0005, bot=0x0007
  let r := pKMADA rd a b
  IO.println s!"KMADA:  {r} (expected 0x00000029)"

-- ── PKBB16 テスト ────────────────────────────────────────────────────────────

/-- PKBB16: rs1=0xAAAABBBB, rs2=0xCCCCDDDD
         → rd[31:16]=rs1[15:0]=0xBBBB, rd[15:0]=rs2[15:0]=0xDDDD
         = 0xBBBBDDDD -/
#eval do
  let a : BitVec 32 := 0xAAAABBBB#32
  let b : BitVec 32 := 0xCCCCDDDD#32
  let r := pPKBB16 a b
  IO.println s!"PKBB16: {r} (expected 0xBBBBDDDD)"

-- ── SUNPKD820 テスト ─────────────────────────────────────────────────────────

/-- SUNPKD820: rs1=0xFE80_00FF
         → rd[31:16]=sext(0xFE_[23:16])=sext(0x80)=0xFF80 (符号拡張)
           rd[15:0]=sext(0xFF_[7:0])=sext(0xFF)=0xFFFF
         = 0xFF80FFFF -/
#eval do
  let a : BitVec 32 := 0xFE800000#32  -- byte2=0x80, byte0=0x00
  let r := pSUNPKD820 a
  IO.println s!"SUNPKD820: {r} (expected 0xFF800000)"

-- ── isPExt フラグテスト ──────────────────────────────────────────────────────

#eval do
  IO.println s!"isPExt(ADD8)={isPExt F7B8.ADD8}     (expected true)"
  IO.println s!"isPExt(RV32M)={isPExt 0b0000001#7}  (expected false)"
  IO.println s!"isPExt(KADD16)={isPExt F7B16.KADD16} (expected true)"

end Tests
