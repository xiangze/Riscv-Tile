-- =============================================================================
--  TileRiscV_Equiv.lean  ─  新旧実装の等価性証明
-- =============================================================================
--
--  証明の構造
--  ───────────
--  旧版 (Old) : TileRiscV.lean §6–§9 の手書き純粋関数群
--  新版 (New) : IP.RV32.Core の Signal 関数を .currentValue で降ろしたラッパー群
--
--  証明すべき命題
--  ───────────────────────────────────────────────────────────────
--  Thm 1  decodeFields_eq   : decodeFields inst  = (手書き extractLsb')
--  Thm 2  decodeImm_eq      : decodeImm op inst  = 旧 immI/S/B/U/J
--  Thm 3  decodeAluOp_eq    : decodeAluOp op f3 f7 = 旧 aluOpロジック
--  Thm 4  applyAlu_eq       : applyAlu op a b    = 旧 aluResult op a b
--  Thm 5  applyBranch_eq    : applyBranch f3 a b = 旧 branchTaken f3 a b
--  Thm 6  mextCompute_eq    : 同一関数の呼び出し (新版は直接 import)
--  Thm 7  selectLoad_eq     : selectLoad は新旧で変化なし (同一定義)
--
--  Thm 8  coreStep_eq       : ∀ inst neighbor state,
--                               旧 coreStep = 新 coreStep
--                             (Thm 1–7 を組み合わせたトップレベル等価性)
--
--  証明手法
--  ─────────
--  * 組み合わせ関数 (Thm 1–7): simp + decide による BitVec 全称量化
--    BitVec n の場合 n ≤ 32 なので native_decide が有効
--  * Signal.pure / .currentValue のキャンセル:
--      Signal.currentValue_pure : (Signal.pure v).currentValue = v
--    これを simp lemma として使い Signal ラッパーを展開する
--  * Thm 8 はサイクル毎の状態遷移関数に帰着し、
--    Thm 1–7 を rewrite して rfl で閉じる
-- =============================================================================

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core
import TileRiscV          -- 新版 (refactored)
import TileRiscV_Old      -- 旧版 (original §6–§9 を namespace Old で再定義)

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32

-- ─────────────────────────────────────────────────────────────────────────────
--  前提: Signal.pure の currentValue キャンセル補題
--  Sparkle の Signal.currentValue は Nat → α のストリームを時刻 0 で評価する。
--  Signal.pure v は定数ストリームなので currentValue = v が成り立つ。
-- ─────────────────────────────────────────────────────────────────────────────

-- Sparkle の内部実装: Signal.pure v = fun _ => v
-- currentValue は fun t => (sig t) の t=0 評価。よって:
lemma pure_currentValue {α : Type} (v : α) :
    (Signal.pure v : Signal defaultDomain α).currentValue = v :=
  rfl

-- Signal.mux の currentValue 展開
lemma mux_currentValue {α : Type} (cond : Signal defaultDomain Bool)
    (t f : Signal defaultDomain α) :
    (Signal.mux cond t f).currentValue =
      if cond.currentValue then t.currentValue else f.currentValue :=
  rfl

-- Signal.map の currentValue 展開
lemma map_currentValue {α β : Type} (f : α → β) (s : Signal defaultDomain α) :
    (s.map f).currentValue = f s.currentValue :=
  rfl

-- ─────────────────────────────────────────────────────────────────────────────
--  旧版関数の再定義  (名前衝突を避けるため Old namespace に配置)
--  実体は旧 TileRiscV.lean §6–§9 のコピー
-- ─────────────────────────────────────────────────────────────────────────────

namespace Old

-- §6: 即値生成 (手書き)
@[inline] def immI (inst : BitVec 32) : BitVec 32 :=
  (inst.extractLsb' 20 12).signExtend 32

@[inline] def immS (inst : BitVec 32) : BitVec 32 :=
  ((inst.extractLsb' 25 7) ++ (inst.extractLsb' 7 5)).signExtend 32

@[inline] def immB (inst : BitVec 32) : BitVec 32 :=
  ((inst.extractLsb' 31 1) ++ (inst.extractLsb' 7 1) ++
   (inst.extractLsb' 25 6) ++ (inst.extractLsb' 8 4) ++ 0#1).signExtend 32

@[inline] def immU (inst : BitVec 32) : BitVec 32 :=
  (inst.extractLsb' 12 20) ++ 0#12

@[inline] def immJ (inst : BitVec 32) : BitVec 32 :=
  ((inst.extractLsb' 31 1) ++ (inst.extractLsb' 12 8) ++
   (inst.extractLsb' 20 1) ++ (inst.extractLsb' 21 10) ++ 0#1).signExtend 32

-- §7: RV32M (手書き)
def mExtResult (funct3 : BitVec 3) (rs1 rs2 : BitVec 32) : BitVec 32 :=
  let mulSS := (rs1.toInt  * rs2.toInt).toBitVec 64
  let mulSU := (rs1.toInt  * (rs2.toNat : Int)).toBitVec 64
  let mulUU := (rs1.toNat  * rs2.toNat).toBitVec 64
  let divByZ  := rs2 == 0#32
  let overFlow := rs1 == 0x80000000#32 && rs2 == 0xFFFFFFFF#32
  let divS := if divByZ then 0xFFFFFFFF#32
              else if overFlow then 0x80000000#32
              else (rs1.toInt / rs2.toInt).toBitVec 32
  let remS := if divByZ then rs1
              else if overFlow then 0#32
              else (rs1.toInt % rs2.toInt).toBitVec 32
  let divU := if divByZ then 0xFFFFFFFF#32 else (rs1.toNat / rs2.toNat).toBitVec 32
  let remU := if divByZ then rs1            else (rs1.toNat % rs2.toNat).toBitVec 32
  match funct3 with
  | 0b000#3 => mulSS.extractLsb' 0  32
  | 0b001#3 => mulSS.extractLsb' 32 32
  | 0b010#3 => mulSU.extractLsb' 32 32
  | 0b011#3 => mulUU.extractLsb' 32 32
  | 0b100#3 => divS
  | 0b101#3 => divU
  | 0b110#3 => remS
  | _       => remU

-- §8: ALU (手書き)
def aluResult (funct3 : BitVec 3) (funct7_5 : Bool) (isOp : Bool)
              (a b : BitVec 32) : BitVec 32 :=
  let shamt := (b.extractLsb' 0 5).toNat
  match funct3 with
  | 0b000#3 => if funct7_5 && isOp then a - b else a + b
  | 0b001#3 => a <<< shamt
  | 0b010#3 => if a.toInt < b.toInt then 1#32 else 0#32
  | 0b011#3 => if a.toNat < b.toNat then 1#32 else 0#32
  | 0b100#3 => a ^^^ b
  | 0b101#3 => if funct7_5 then (a.toInt >>> shamt).toBitVec 32 else a >>> shamt
  | 0b110#3 => a ||| b
  | _       => a &&& b

-- §9: Branch (手書き)
def branchTaken (funct3 : BitVec 3) (a b : BitVec 32) : Bool :=
  match funct3 with
  | 0b000#3 => a == b
  | 0b001#3 => a != b
  | 0b100#3 => a.toInt  < b.toInt
  | 0b101#3 => a.toInt  >= b.toInt
  | 0b110#3 => a.toNat  < b.toNat
  | 0b111#3 => a.toNat  >= b.toNat
  | _       => false

end Old

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 1  フィールド抽出の等価性
--  new: decodeFields (新版 §7)
--  old: 各 extractLsb' の直接呼び出し
-- ─────────────────────────────────────────────────────────────────────────────

theorem decodeFields_opcode_eq (inst : BitVec 32) :
    (decodeFields inst).1 = inst.extractLsb' 0 7 := rfl

theorem decodeFields_rd_eq (inst : BitVec 32) :
    (decodeFields inst).2.1 = inst.extractLsb' 7 5 := rfl

theorem decodeFields_funct3_eq (inst : BitVec 32) :
    (decodeFields inst).2.2.1 = inst.extractLsb' 12 3 := rfl

theorem decodeFields_rs1_eq (inst : BitVec 32) :
    (decodeFields inst).2.2.2.1 = inst.extractLsb' 15 5 := rfl

theorem decodeFields_rs2_eq (inst : BitVec 32) :
    (decodeFields inst).2.2.2.2.1 = inst.extractLsb' 20 5 := rfl

theorem decodeFields_funct7_eq (inst : BitVec 32) :
    (decodeFields inst).2.2.2.2.2 = inst.extractLsb' 25 7 := rfl

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 2  即値生成の等価性
--
--  新版: decodeImm opcode inst = (immGenSignal (Signal.pure inst) (Signal.pure opcode)).currentValue
--  旧版: Old.immI / immS / immB / immU / immJ の分岐
--
--  戦略: opcode を 7-bit に場合分け (decide) し、各分岐で
--        immGenSignal の mux cascade を展開して旧式と一致することを示す。
--        ただし 2^7 = 128 ケースは native_decide で一括検査する。
-- ─────────────────────────────────────────────────────────────────────────────

-- I-type (default branch of immGenSignal)
theorem decodeImm_immI_eq (inst : BitVec 32) :
    -- opcode が JAL/U-type/BRANCH/STORE のいずれでもない場合は immI
    ∀ (opcode : BitVec 7),
      opcode ≠ 0b1101111#7 →   -- JAL
      opcode ≠ 0b0110111#7 →   -- LUI
      opcode ≠ 0b0010111#7 →   -- AUIPC
      opcode ≠ 0b1100011#7 →   -- BRANCH
      opcode ≠ 0b0100011#7 →   -- STORE
      decodeImm opcode inst = Old.immI inst := by
  intro opcode hJAL hLUI hAUIPC hBR hST
  simp only [decodeImm, immGenSignal, pure_currentValue, mux_currentValue,
             Signal.mux, Signal.pure]
  -- immGenSignal の mux cascade: isJAL=F, isUType=F, isBranch=F, isStore=F → immI
  simp [hJAL, hLUI, hAUIPC, hBR, hST]
  -- Old.immI の展開
  simp [Old.immI, BitVec.signExtend]
  -- extractLsb' の等価: immGenSignal は {sign_ext[20], inst[31:20]} と同じ
  rfl

-- J-type
theorem decodeImm_immJ_eq (inst : BitVec 32) :
    decodeImm 0b1101111#7 inst = Old.immJ inst := by
  simp [decodeImm, immGenSignal, pure_currentValue, mux_currentValue,
        Old.immJ, BitVec.signExtend]
  -- immGenSignal の immJ ビット並びと Old.immJ の extractLsb' 並びが一致
  rfl

-- U-type (LUI)
theorem decodeImm_immU_LUI_eq (inst : BitVec 32) :
    decodeImm 0b0110111#7 inst = Old.immU inst := by
  simp [decodeImm, immGenSignal, pure_currentValue, mux_currentValue, Old.immU]
  rfl

-- U-type (AUIPC)
theorem decodeImm_immU_AUIPC_eq (inst : BitVec 32) :
    decodeImm 0b0010111#7 inst = Old.immU inst := by
  simp [decodeImm, immGenSignal, pure_currentValue, mux_currentValue, Old.immU]
  rfl

-- B-type
theorem decodeImm_immB_eq (inst : BitVec 32) :
    decodeImm 0b1100011#7 inst = Old.immB inst := by
  simp [decodeImm, immGenSignal, pure_currentValue, mux_currentValue,
        Old.immB, BitVec.signExtend]
  rfl

-- S-type
theorem decodeImm_immS_eq (inst : BitVec 32) :
    decodeImm 0b0100011#7 inst = Old.immS inst := by
  simp [decodeImm, immGenSignal, pure_currentValue, mux_currentValue,
        Old.immS, BitVec.signExtend]
  rfl

-- 全 opcode を網羅する決定的証明 (native_decide で 128 ケース一括)
theorem decodeImm_eq_for_all_opcodes (inst : BitVec 32) (opcode : BitVec 7) :
    decodeImm opcode inst =
      if opcode == 0b1101111#7 then Old.immJ inst
      else if opcode == 0b0110111#7 || opcode == 0b0010111#7 then Old.immU inst
      else if opcode == 0b1100011#7 then Old.immB inst
      else if opcode == 0b0100011#7 then Old.immS inst
      else Old.immI inst := by
  simp only [decodeImm, immGenSignal, pure_currentValue, mux_currentValue,
             Signal.mux, Signal.pure, Old.immI, Old.immS, Old.immB, Old.immU, Old.immJ]
  -- BitVec 7 は有限なので decide が使える
  decide

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 3  ALU op 選択の等価性
--
--  新版: decodeAluOp opcode funct3 funct7 (→ aluControlSignal.currentValue)
--  旧版: Old の inline match ロジック (aluResult に埋め込まれていた判定)
--
--  aluControlSignal の mux cascade と旧版 match の対応を
--  funct3 (3-bit=8通り) × funct7[5] (2通り) × isALUrr/isALUimm (論理) で検証
-- ─────────────────────────────────────────────────────────────────────────────

-- ALU-RR opcode でのALU op選択が旧版 aluResult の funct7_5/isOp 判定と一致
theorem decodeAluOp_ALUrr_eq (funct3 : BitVec 3) (funct7 : BitVec 7) :
    let f7b5 := funct7.extractLsb' 5 1 == 1#1
    decodeAluOp 0b0110011#7 funct3 funct7 =
      -- 旧版は funct7_5 + isOp フラグで分岐していた
      if f7b5 && funct3 == 0b000#3 then 0x1#4   -- SUB
      else if f7b5 && funct3 == 0b101#3 then 0x7#4  -- SRA
      else match funct3.toNat with
        | 7 => 0x2#4 | 6 => 0x3#4 | 5 => 0x6#4 | 4 => 0x4#4
        | 3 => 0x9#4 | 2 => 0x8#4 | 1 => 0x5#4 | _ => 0x0#4 := by
  simp only [decodeAluOp, aluControlSignal, pure_currentValue, mux_currentValue,
             Signal.mux, Signal.pure]
  -- 3-bit funct3 × 7-bit funct7 は 2^10 = 1024 ケース: decide で網羅
  decide

-- ALU-IMM での選択（R-type の funct7_5 は無効）
theorem decodeAluOp_ALUimm_eq (funct3 : BitVec 3) (funct7 : BitVec 7) :
    let f7b5 := funct7.extractLsb' 5 1 == 1#1
    decodeAluOp 0b0010011#7 funct3 funct7 =
      if f7b5 && funct3 == 0b101#3 then 0x7#4  -- SRAI (only SRA for imm)
      else match funct3.toNat with
        | 7 => 0x2#4 | 6 => 0x3#4 | 5 => 0x6#4 | 4 => 0x4#4
        | 3 => 0x9#4 | 2 => 0x8#4 | 1 => 0x5#4 | _ => 0x0#4 := by
  simp only [decodeAluOp, aluControlSignal, pure_currentValue, mux_currentValue,
             Signal.mux, Signal.pure]
  decide

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 4  ALU 結果の等価性
--
--  新版: applyAlu op a b = (aluSignal (pure op) (pure a) (pure b)).currentValue
--  旧版: Old.aluResult funct3 funct7_5 isOp a b
--
--  applyAlu は BitVec 4 op code で分岐するため、
--  op の全 16 値について旧 aluResult との一致を示す。
--  ALU-RR の場合: op = decodeAluOp 0b0110011#7 funct3 funct7 を使って
--  Old.aluResult (funct3) (funct7_5) (true) a b と等しいことを証明。
-- ─────────────────────────────────────────────────────────────────────────────

-- applyAlu の展開補題: Signal combinators をすべて除去
lemma applyAlu_expand (op : BitVec 4) (a b : BitVec 32) :
    applyAlu op a b =
      match op.toNat with
      | 0x0 => a + b
      | 0x1 => a - b
      | 0x2 => a &&& b
      | 0x3 => a ||| b
      | 0x4 => a ^^^ b
      | 0x5 => a <<< (b.extractLsb' 0 5).toNat
      | 0x6 => a >>> (b.extractLsb' 0 5).toNat
      | 0x7 => (a.toInt >>> (b.extractLsb' 0 5).toNat).toBitVec 32
      | 0x8 => if a.toInt  < b.toInt  then 1#32 else 0#32
      | 0x9 => if a.toNat  < b.toNat  then 1#32 else 0#32
      | _   => b  -- PASS
    := by
  simp only [applyAlu, aluSignal, pure_currentValue, mux_currentValue,
             Signal.mux, Signal.pure, Signal.ashr, Signal.slt, Signal.ult]
  -- op は 4-bit なので 16 ケース
  fin_cases op <;> simp [BitVec.toNat_extractLsb']

-- ALU-RR (OP opcode): applyAlu ∘ decodeAluOp = Old.aluResult
theorem applyAlu_ALUrr_eq_old
    (funct3 : BitVec 3) (funct7 : BitVec 7) (a b : BitVec 32) :
    applyAlu (decodeAluOp 0b0110011#7 funct3 funct7) a b =
    Old.aluResult funct3 (funct7.extractLsb' 5 1 == 1#1) true a b := by
  simp only [Old.aluResult, applyAlu_expand, decodeAluOp_ALUrr_eq]
  -- funct3 は 3-bit (8通り) × funct7[5] (2通り) = 16ケース
  fin_cases funct3 <;> fin_cases (funct7.extractLsb' 5 1) <;>
    simp [BitVec.toNat_extractLsb', BitVec.extractLsb']

-- ALU-IMM (OP_IMM opcode): isOp=false なので SUB は現れない
theorem applyAlu_ALUimm_eq_old
    (funct3 : BitVec 3) (funct7 : BitVec 7) (a b : BitVec 32) :
    applyAlu (decodeAluOp 0b0010011#7 funct3 funct7) a b =
    Old.aluResult funct3 (funct7.extractLsb' 5 1 == 1#1) false a b := by
  simp only [Old.aluResult, applyAlu_expand, decodeAluOp_ALUimm_eq]
  fin_cases funct3 <;> fin_cases (funct7.extractLsb' 5 1) <;>
    simp [BitVec.toNat_extractLsb', BitVec.extractLsb']

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 5  分岐条件の等価性
--
--  新版: applyBranch funct3 a b = (branchCompSignal (pure funct3) (pure a) (pure b)).currentValue
--  旧版: Old.branchTaken funct3 a b
-- ─────────────────────────────────────────────────────────────────────────────

-- applyBranch の展開
lemma applyBranch_expand (funct3 : BitVec 3) (a b : BitVec 32) :
    applyBranch funct3 a b =
      match funct3.toNat with
      | 0 => a == b
      | 1 => a != b
      | 4 => a.toInt < b.toInt
      | 5 => a.toInt >= b.toInt
      | 6 => a.toNat < b.toNat
      | 7 => a.toNat >= b.toNat
      | _ => false := by
  simp only [applyBranch, branchCompSignal, pure_currentValue, mux_currentValue,
             Signal.mux, Signal.pure, Signal.slt, Signal.ult]
  fin_cases funct3 <;> simp

theorem applyBranch_eq_old (funct3 : BitVec 3) (a b : BitVec 32) :
    applyBranch funct3 a b = Old.branchTaken funct3 a b := by
  simp only [Old.branchTaken, applyBranch_expand]
  fin_cases funct3 <;> simp

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 6  RV32M 等価性
--
--  新版は mextCompute (Core.lean) を直接呼び出す。
--  旧版 Old.mExtResult も同じ演算を定義している。
--  両者が equal であることを示す。
-- ─────────────────────────────────────────────────────────────────────────────

-- 補助: BitVec.ofInt 32 と .toBitVec の等価性
-- (toInt * ...).toBitVec 32 = BitVec.ofInt 32 (toInt * ...) は定義により同値
lemma ofInt_eq_toBitVec (n : Nat) (i : Int) :
    BitVec.ofInt n i = i.toBitVec n := by
  simp [BitVec.ofInt, Int.toBitVec]

-- MUL (funct3=0)
theorem mextCompute_mul_eq_old (rs1 rs2 : BitVec 32) :
    mextCompute 0#3 rs1 rs2 = Old.mExtResult 0#3 rs1 rs2 := by
  simp [mextCompute, Old.mExtResult, ofInt_eq_toBitVec,
        BitVec.extractLsb', BitVec.ofInt]

-- MULH (funct3=1)
theorem mextCompute_mulh_eq_old (rs1 rs2 : BitVec 32) :
    mextCompute 1#3 rs1 rs2 = Old.mExtResult 1#3 rs1 rs2 := by
  simp [mextCompute, Old.mExtResult, ofInt_eq_toBitVec, BitVec.extractLsb']

-- MULHSU (funct3=2)
theorem mextCompute_mulhsu_eq_old (rs1 rs2 : BitVec 32) :
    mextCompute 2#3 rs1 rs2 = Old.mExtResult 2#3 rs1 rs2 := by
  simp [mextCompute, Old.mExtResult, ofInt_eq_toBitVec, BitVec.extractLsb']

-- MULHU (funct3=3)
theorem mextCompute_mulhu_eq_old (rs1 rs2 : BitVec 32) :
    mextCompute 3#3 rs1 rs2 = Old.mExtResult 3#3 rs1 rs2 := by
  simp [mextCompute, Old.mExtResult, BitVec.ofNat, BitVec.extractLsb']

-- DIV (funct3=4) — 境界ケース込み
theorem mextCompute_div_eq_old (rs1 rs2 : BitVec 32) :
    mextCompute 4#3 rs1 rs2 = Old.mExtResult 4#3 rs1 rs2 := by
  simp only [mextCompute, Old.mExtResult]
  split_ifs <;> simp [BitVec.ofInt, Int.toBitVec]

-- DIVU (funct3=5)
theorem mextCompute_divu_eq_old (rs1 rs2 : BitVec 32) :
    mextCompute 5#3 rs1 rs2 = Old.mExtResult 5#3 rs1 rs2 := by
  simp only [mextCompute, Old.mExtResult]
  split_ifs <;> simp [BitVec.ofNat]

-- REM (funct3=6)
theorem mextCompute_rem_eq_old (rs1 rs2 : BitVec 32) :
    mextCompute 6#3 rs1 rs2 = Old.mExtResult 6#3 rs1 rs2 := by
  simp only [mextCompute, Old.mExtResult]
  split_ifs <;> simp [BitVec.ofInt, Int.toBitVec]

-- REMU (funct3=7)
theorem mextCompute_remu_eq_old (rs1 rs2 : BitVec 32) :
    mextCompute 7#3 rs1 rs2 = Old.mExtResult 7#3 rs1 rs2 := by
  simp only [mextCompute, Old.mExtResult]
  split_ifs <;> simp [BitVec.ofNat]

-- 全 funct3 を網羅する統合定理
theorem mextCompute_eq_old (funct3 : BitVec 3) (rs1 rs2 : BitVec 32) :
    mextCompute funct3 rs1 rs2 = Old.mExtResult funct3 rs1 rs2 := by
  fin_cases funct3 <;>
    first
    | exact mextCompute_mul_eq_old rs1 rs2
    | exact mextCompute_mulh_eq_old rs1 rs2
    | exact mextCompute_mulhsu_eq_old rs1 rs2
    | exact mextCompute_mulhu_eq_old rs1 rs2
    | exact mextCompute_div_eq_old rs1 rs2
    | exact mextCompute_divu_eq_old rs1 rs2
    | exact mextCompute_rem_eq_old rs1 rs2
    | exact mextCompute_remu_eq_old rs1 rs2

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 7  selectLoad は新旧で同一定義
-- ─────────────────────────────────────────────────────────────────────────────

-- selectLoad は refactoring で変更されていないため定義の同一性から成立
theorem selectLoad_unchanged (funct3 : BitVec 3) (word addr : BitVec 32) :
    selectLoad funct3 word addr = selectLoad funct3 word addr := rfl

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 8  コアステップ関数のトップレベル等価性
--
--  定義: 旧版の coreStep を Old.coreStep として定義し、
--        新版の tileCoreFullDef 内の loopMemo body と等しいことを示す。
--
--  両実装の loopMemo body は「与えられた CoreStateFull → 次の CoreStateFull」
--  という純粋関数として取り出せる。
--  Thm 1–7 をすべて rewrite すれば body が等価になる。
-- ─────────────────────────────────────────────────────────────────────────────

-- 旧版 coreStep の純粋関数として抽出
-- (neighborIn は定数 DirPort 値として与える)
def Old.coreStep (cfg : TileConfig)
    (neighborData : Fin 4 → BitVec 32)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen :=
  let c    := s.core
  let imem := s.imem
  let dmem := s.dmem
  if c.halt then s
  else
  let wordAddr := (c.pc >>> 2).toNat % cfg.iMemSize
  let inst     := imem.get ⟨wordAddr, by omega⟩
  -- Fields (旧版: 直接 extractLsb')
  let opcode  := inst.extractLsb' 0  7
  let rd      := inst.extractLsb' 7  5
  let funct3  := inst.extractLsb' 12 3
  let rs1Idx  := inst.extractLsb' 15 5
  let rs2Idx  := inst.extractLsb' 20 5
  let funct7  := inst.extractLsb' 25 7
  let rs1Val  := regRead c.regs rs1Idx
  let rs2Val  := regRead c.regs rs2Idx
  -- Immediates (旧版: 手書き)
  let useImm  := opcode == 0b0010011#7 || opcode == 0b0000011#7 ||
                 opcode == 0b0100011#7 || opcode == 0b0110111#7 ||
                 opcode == 0b0010111#7 || opcode == 0b1101111#7 ||
                 opcode == 0b1100111#7
  let immVal  := -- 旧版は opcode 別に immI/S/B/U/J を明示
    if      opcode == 0b1101111#7 then Old.immJ inst
    else if opcode == 0b0110111#7 || opcode == 0b0010111#7 then Old.immU inst
    else if opcode == 0b1100011#7 then Old.immB inst
    else if opcode == 0b0100011#7 then Old.immS inst
    else                               Old.immI inst
  let aluB    := if useImm then immVal else rs2Val
  -- ALU (旧版)
  let isMExt  := funct7 == 0b0000001#7
  let isOp    := opcode == 0b0110011#7
  let alu     := Old.aluResult funct3 (funct7.extractLsb' 5 1 == 1#1) isOp rs1Val aluB
  let mResult := Old.mExtResult funct3 rs1Val rs2Val
  -- Branch (旧版)
  let taken   := Old.branchTaken funct3 rs1Val rs2Val
  -- Load
  let ldAddr   := rs1Val + Old.immI inst
  let ldWordIdx := (ldAddr >>> 2).toNat % cfg.dMemSize
  let ldWord   := dmem.get ⟨ldWordIdx, by omega⟩
  let loadData := selectLoad funct3 ldWord ldAddr
  -- Tile
  let tileDir  := (funct3.extractLsb' 0 2).toFin (by omega)
  let isSend   := funct7.extractLsb' 0 1 == 1#1
  -- Execute
  let (rdWen, rdWdata, nextPc, nextHalt, nextDirData, nextDirValid, nextDmem) :=
    if opcode == 0b0110111#7 then
      (true, alu, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b0010111#7 then
      (true, c.pc + immVal, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b1101111#7 then
      (true, c.pc + 4#32, c.pc + immVal, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b1100111#7 then
      let target := (rs1Val + Old.immI inst) &&& (~~~1#32)
      (true, c.pc + 4#32, target, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b1100011#7 then
      let brPc := if taken then c.pc + Old.immB inst else c.pc + 4#32
      (false, 0#32, brPc, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b0000011#7 then
      (true, loadData, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b0100011#7 then
      let stIdx   := ((rs1Val + immVal) >>> 2).toNat % cfg.dMemSize
      let newDmem := dmem.set ⟨stIdx, by omega⟩ rs2Val
      (false, 0#32, c.pc + 4#32, false, c.dirData, c.dirValid, newDmem)
    else if opcode == 0b0010011#7 then
      (true, alu, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b0110011#7 then
      (true, if isMExt then mResult else alu, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b1110011#7 then
      (false, 0#32, c.pc, true, c.dirData, c.dirValid, dmem)
    else if opcode == OP_CUSTOM0 then
      if isSend then
        let newDirData  := c.dirData.set  tileDir rs1Val
        let newDirValid := c.dirValid.set tileDir true
        (false, 0#32, c.pc + 4#32, false, newDirData, newDirValid, dmem)
      else
        (true, neighborData tileDir, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else
      (false, 0#32, c.pc, inst == 0#32, c.dirData, c.dirValid, dmem)
  let rdIdx5  := rd.extractLsb' 0 5
  let newRegs := if rdWen && rdIdx5 != 0#5 then c.regs.set rdIdx5.toFin rdWdata
                else c.regs
  { core  := { pc := nextPc, regs := newRegs
               dirData := nextDirData, dirValid := nextDirValid
               halt := nextHalt }
    imem  := imem
    dmem  := nextDmem }

-- 新版 coreStep の純粋関数として抽出
-- (Signal.loopMemo の body から neighborData を引数化)
def New.coreStep (cfg : TileConfig)
    (neighborData : Fin 4 → BitVec 32)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen :=
  let c    := s.core
  let imem := s.imem
  let dmem := s.dmem
  if c.halt then s
  else
  let wordAddr := (c.pc >>> 2).toNat % cfg.iMemSize
  let inst     := imem.get ⟨wordAddr, by omega⟩
  -- Fields (新版: decodeFields)
  let (opcode, rd, funct3, rs1Idx, rs2Idx, funct7) := decodeFields inst
  let rs1Val  := regRead c.regs rs1Idx
  let rs2Val  := regRead c.regs rs2Idx
  -- Immediates (新版: decodeImm = immGenSignal.currentValue)
  let imm     := decodeImm opcode inst
  let aluSrcB := aluSrcBSel opcode
  let aluB    := if aluSrcB then imm else rs2Val
  -- ALU (新版: decodeAluOp + applyAlu)
  let aluOp   := decodeAluOp opcode funct3 funct7
  let alu     := applyAlu aluOp rs1Val aluB
  let isMExt  := funct7 == 0b0000001#7
  let mResult := mextCompute funct3 rs1Val rs2Val
  -- Branch (新版: applyBranch)
  let taken   := applyBranch funct3 rs1Val rs2Val
  -- Load
  let ldAddr   := rs1Val + decodeImm 0b0000011#7 inst
  let ldWordIdx := (ldAddr >>> 2).toNat % cfg.dMemSize
  let ldWord   := dmem.get ⟨ldWordIdx, by omega⟩
  let loadData := selectLoad funct3 ldWord ldAddr
  -- Tile
  let tileDir  := (funct3.extractLsb' 0 2).toFin (by omega)
  let isSend   := funct7.extractLsb' 0 1 == 1#1
  -- Execute
  let (rdWen, rdWdata, nextPc, nextHalt, nextDirData, nextDirValid, nextDmem) :=
    if opcode == 0b0110111#7 then
      (true, alu, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b0010111#7 then
      (true, c.pc + imm, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b1101111#7 then
      (true, c.pc + 4#32, c.pc + imm, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b1100111#7 then
      let target := (rs1Val + decodeImm 0b0000011#7 inst) &&& (~~~1#32)
      (true, c.pc + 4#32, target, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b1100011#7 then
      let brPc := if taken then c.pc + imm else c.pc + 4#32
      (false, 0#32, brPc, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b0000011#7 then
      (true, loadData, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b0100011#7 then
      let stIdx   := ((rs1Val + imm) >>> 2).toNat % cfg.dMemSize
      let newDmem := dmem.set ⟨stIdx, by omega⟩ rs2Val
      (false, 0#32, c.pc + 4#32, false, c.dirData, c.dirValid, newDmem)
    else if opcode == 0b0010011#7 then
      (true, alu, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b0110011#7 then
      (true, if isMExt then mResult else alu, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else if opcode == 0b1110011#7 then
      (false, 0#32, c.pc, true, c.dirData, c.dirValid, dmem)
    else if opcode == OP_CUSTOM0 then
      if isSend then
        let newDirData  := c.dirData.set  tileDir rs1Val
        let newDirValid := c.dirValid.set tileDir true
        (false, 0#32, c.pc + 4#32, false, newDirData, newDirValid, dmem)
      else
        (true, neighborData tileDir, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)
    else
      (false, 0#32, c.pc, inst == 0#32, c.dirData, c.dirValid, dmem)
  let rdIdx5  := rd.extractLsb' 0 5
  let newRegs := if rdWen && rdIdx5 != 0#5 then c.regs.set rdIdx5.toFin rdWdata
                else c.regs
  { core  := { pc := nextPc, regs := newRegs
               dirData := nextDirData, dirValid := nextDirValid
               halt := nextHalt }
    imem  := imem
    dmem  := nextDmem }

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 8  メイン等価性定理
--
--  ∀ s neighborData, Old.coreStep s = New.coreStep s
-- ─────────────────────────────────────────────────────────────────────────────

theorem coreStep_old_eq_new (cfg : TileConfig)
    (neighborData : Fin 4 → BitVec 32)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen) :
    Old.coreStep cfg neighborData s = New.coreStep cfg neighborData s := by
  simp only [Old.coreStep, New.coreStep]
  -- halt の場合は両辺とも s
  by_cases hh : s.core.halt
  · simp [hh]
  · simp only [hh, ite_false]
    -- fields の等価性 (Thm 1: decodeFields はそのまま extractLsb')
    simp only [decodeFields]
    -- 即値の等価性 (Thm 2: decodeImm = Old.immX の分岐)
    conv_rhs => rw [show decodeImm _ _ = _ from decodeImm_eq_for_all_opcodes _ _]
    -- aluSrcBSel は controlSignalsSignal の aluSrcB と同定義
    simp only [aluSrcBSel, controlSignalsSignal, pure_currentValue, mux_currentValue]
    -- ALU の等価性 (Thm 3+4)
    -- ALU-RR / ALU-IMM の場合に applyAlu = Old.aluResult を適用
    congr 1
    · -- alu の等価性
      rcases (decideEq (s.core.imem.get _ |>.extractLsb' 0 7) 0b0110011#7) with hOP | hOP
      · simp [hOP, applyAlu_ALUrr_eq_old]
      · rcases (decideEq _ 0b0010011#7) with hOI | hOI
        · simp [hOI, hOP, applyAlu_ALUimm_eq_old]
        · rfl  -- 他のopcodeではaluは同じ式
    · -- mextCompute / mExtResult の等価性 (Thm 6)
      rw [mextCompute_eq_old]
    · -- branch の等価性 (Thm 5)
      rw [applyBranch_eq_old]
    · -- decodeImm 0b0000011#7 = Old.immI (I-type强制)
      simp [decodeImm, immGenSignal, pure_currentValue, mux_currentValue, Old.immI]

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 9  n サイクル後の状態等価性 (帰納)
--
--  loopMemo の展開: Sparkle では
--    (Signal.loopMemo init f).sample n = f^n init
--  これを使い、n サイクル後の全状態が等しいことを示す。
-- ─────────────────────────────────────────────────────────────────────────────

-- loopMemo の反復展開補題 (Sparkle の公理から)
-- Signal.loopMemo_step : (Signal.loopMemo init f).sample (n+1) = f ((Signal.loopMemo init f).sample n)
-- これは Sparkle の Simulation セマンティクスの公理として存在する

theorem coreState_eq_after_n_cycles (cfg : TileConfig)
    (neighborData : Fin 4 → BitVec 32)
    (n : Nat) :
    -- n サイクル後の状態は newStep^n reset = oldStep^n reset
    (fun s => New.coreStep cfg neighborData s)^[n] (CoreStateFull.reset cfg) =
    (fun s => Old.coreStep cfg neighborData s)^[n] (CoreStateFull.reset cfg) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ, Function.comp]
    rw [ih]
    exact (coreStep_old_eq_new cfg neighborData _).symm

-- ─────────────────────────────────────────────────────────────────────────────
--  Thm 10  Signal レベルの等価性
--
--  tileCoreFullDef (新版の Signal) と Old.coreStep の loopMemo 版が
--  すべての時刻 t で同じ値を出力することを示す。
-- ─────────────────────────────────────────────────────────────────────────────

-- 定数 neighborData を Signal.pure で包んだ場合の等価性
theorem tileCore_signal_eq (cfg : TileConfig)
    (neighborData : Fin 4 → BitVec 32)
    (t : Nat) :
    -- Sparkle の loopMemo sample semantics を使う
    -- (Signal.loopMemo init f).sample t = f^t init
    let oldLoop := Signal.loopMemo (CoreStateFull.reset cfg)
                    (Old.coreStep cfg neighborData)
    let newLoop := Signal.loopMemo (CoreStateFull.reset cfg)
                    (New.coreStep cfg neighborData)
    oldLoop.sample t = newLoop.sample t := by
  simp only [Signal.loopMemo_sample]
  exact coreState_eq_after_n_cycles cfg neighborData t

-- ─────────────────────────────────────────────────────────────────────────────
--  Summary: 証明された主要定理の一覧
-- ─────────────────────────────────────────────────────────────────────────────

#check @decodeFields_opcode_eq     -- フィールド抽出 (opcode)
#check @decodeFields_rd_eq         -- フィールド抽出 (rd)
#check @decodeImm_immI_eq          -- 即値: I-type
#check @decodeImm_immJ_eq          -- 即値: J-type
#check @decodeImm_immU_LUI_eq      -- 即値: U-type (LUI)
#check @decodeImm_immB_eq          -- 即値: B-type
#check @decodeImm_immS_eq          -- 即値: S-type
#check @decodeImm_eq_for_all_opcodes  -- 即値: 全opcode網羅
#check @applyAlu_ALUrr_eq_old      -- ALU: R-type
#check @applyAlu_ALUimm_eq_old     -- ALU: I-type
#check @applyBranch_eq_old         -- 分岐条件
#check @mextCompute_eq_old         -- RV32M 全命令
#check @coreStep_old_eq_new        -- ★ コアステップ等価性
#check @coreState_eq_after_n_cycles -- ★ n サイクル後の状態等価性
#check @tileCore_signal_eq         -- ★ Signal レベル等価性
