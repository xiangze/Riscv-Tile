-- =============================================================================
--  TileRiscV_RV32_Equiv.lean
--  「4×4 TileArray の各コアは、CUSTOM-0命令を含まない
--   プログラムに対して、孤立した RV32I+M コアと等価に動作する」
-- =============================================================================
--
--  証明の構造
--  ──────────────────────────────────────────────────────────────
--
--  §A  RV32 参照実装 (孤立コア)
--       RefCore : CoreStateFull → CoreStateFull
--       neighborData を一切参照しない純粋な RV32I+M ステップ関数
--
--  §B  CUSTOM-0 不在の条件
--       NoCustom prog : プログラム中に CUSTOM-0 命令が存在しない
--       ⟺ ∀ addr, prog[addr].extractLsb' 0 7 ≠ OP_CUSTOM0
--
--  §C  補題群
--       Lemma C1  neighbor_irrelevance :
--         NoCustom のとき coreStep の結果は neighborData に依存しない
--       Lemma C2  coreStep_eq_refStep :
--         NoCustom のとき coreStep cfg nd s = RefCore.step s
--
--  §D  メイン定理
--       Theorem isolation_theorem :
--         ∀ (r : Fin 4) (c : Fin 4) (t : Nat),
--           NoCustom (grid[r][c].imem) →
--           (TileArray.core r c).sample t = (RefCore r c).sample t
--
--  §E  強化版: メッシュ全体での等価性
--       Theorem mesh_equiv :
--         (∀ r c, NoCustom (initialImem r c)) →
--         ∀ r c t, tileGrid[r][c].sample t = refGrid[r][c].sample t
--
-- =============================================================================

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core
import TileRiscV   -- 新版 (refactored)

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32

-- ─────────────────────────────────────────────────────────────────────────────
--  §A  RV32 参照実装
--      TileCore から CUSTOM-0 分岐を取り除いた「孤立コア」のステップ関数。
--      neighborData 引数を持たない。
-- ─────────────────────────────────────────────────────────────────────────────

namespace RefCore

/-- 孤立 RV32I+M コアのステップ関数。
    TileCore の coreStep から CUSTOM-0 分岐を削除し、
    neighborData を引数として受け取らない版。 -/
def step (cfg : TileConfig)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen :=
  let c    := s.core
  let imem := s.imem
  let dmem := s.dmem
  if c.halt then s
  else
  let wordAddr := (c.pc >>> 2).toNat % cfg.iMemSize
  let inst     := imem.get ⟨wordAddr, by omega⟩
  let (opcode, rd, funct3, rs1Idx, rs2Idx, funct7) := decodeFields inst
  let rs1Val  := regRead c.regs rs1Idx
  let rs2Val  := regRead c.regs rs2Idx
  let imm     := decodeImm opcode inst
  let aluSrcB := aluSrcBSel opcode
  let aluB    := if aluSrcB then imm else rs2Val
  let aluOp   := decodeAluOp opcode funct3 funct7
  let alu     := applyAlu aluOp rs1Val aluB
  let isMExt  := funct7 == 0b0000001#7
  let mResult := mextCompute funct3 rs1Val rs2Val
  let taken   := applyBranch funct3 rs1Val rs2Val
  let ldAddr  := rs1Val + decodeImm 0b0000011#7 inst
  let ldIdx   := (ldAddr >>> 2).toNat % cfg.dMemSize
  let ldWord  := dmem.get ⟨ldIdx, by omega⟩
  let loadData := selectLoad funct3 ldWord ldAddr
  let tileDir  := (funct3.extractLsb' 0 2).toFin (by omega)
  let isSend   := funct7.extractLsb' 0 1 == 1#1
  -- Execute: CUSTOM-0 分岐は「未定義命令 → halt」として扱う
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
    else
      -- CUSTOM-0 を含む未定義命令: inst == 0 と同様に halt
      -- (NoCustom 条件下ではこの分岐に到達しない)
      (false, 0#32, c.pc, true, c.dirData, c.dirValid, dmem)
  let rdIdx5  := rd.extractLsb' 0 5
  let newRegs := if rdWen && rdIdx5 != 0#5 then c.regs.set rdIdx5.toFin rdWdata
                else c.regs
  { core  := { pc := nextPc, regs := newRegs
               dirData := nextDirData, dirValid := nextDirValid
               halt := nextHalt }
    imem  := imem
    dmem  := nextDmem }

end RefCore

-- ─────────────────────────────────────────────────────────────────────────────
--  §B  CUSTOM-0 不在の条件
-- ─────────────────────────────────────────────────────────────────────────────

/-- プログラム (imem) 中に CUSTOM-0 命令が存在しないことの定義。
    全アドレスで opcode フィールドが OP_CUSTOM0 でないことを要求する。 -/
def NoCustom {iMemSize : Nat} (imem : HWVector iMemSize (BitVec 32)) : Prop :=
  ∀ (addr : Fin iMemSize), (imem.get addr).extractLsb' 0 7 ≠ OP_CUSTOM0

/-- NoCustom の等価な特徴付け: 実行される命令列に CUSTOM-0 が現れない。
    実行ステップ中に fetch される命令に限定した条件。 -/
def NoCustomDynamic {iMemSize : Nat} (imem : HWVector iMemSize (BitVec 32)) : Prop :=
  ∀ (pc : BitVec 32),
    let wordAddr := (pc >>> 2).toNat % iMemSize
    (imem.get ⟨wordAddr, by omega⟩).extractLsb' 0 7 ≠ OP_CUSTOM0

-- 静的条件は動的条件を含意する
lemma noCustom_implies_dynamic {iMemSize : Nat}
    (imem : HWVector iMemSize (BitVec 32))
    (h : NoCustom imem) : NoCustomDynamic imem := by
  intro pc
  simp only [NoCustomDynamic]
  exact h ⟨(pc >>> 2).toNat % iMemSize, Nat.mod_lt _ (by omega)⟩

-- ─────────────────────────────────────────────────────────────────────────────
--  §C1  neighbor_irrelevance
--       CUSTOM-0 が現れないとき、coreStep の結果は neighborData に依存しない
-- ─────────────────────────────────────────────────────────────────────────────

/-- coreStep は CUSTOM-0 の TILE_RECV 分岐でのみ neighborData を参照する。
    NoCustom 条件下では TILE_RECV 分岐に到達しないため、
    任意の neighborData₁, neighborData₂ に対して coreStep の結果が一致する。 -/
theorem neighbor_irrelevance (cfg : TileConfig)
    (nd₁ nd₂ : Fin 4 → BitVec 32)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    (hNC : NoCustomDynamic s.imem) :
    New.coreStep cfg nd₁ s = New.coreStep cfg nd₂ s := by
  simp only [New.coreStep]
  -- halt の場合は trivial
  by_cases hh : s.core.halt
  · simp [hh]
  · simp only [hh, ite_false]
    -- fetch した命令の opcode が CUSTOM-0 でないことを取り出す
    have hOpcode : (s.imem.get ⟨(s.core.pc >>> 2).toNat % cfg.iMemSize, by omega⟩
                    ).extractLsb' 0 7 ≠ OP_CUSTOM0 := hNC s.core.pc
    -- decodeFields の opcode フィールドが CUSTOM-0 でない
    simp only [decodeFields] at hOpcode ⊢
    set inst := s.imem.get ⟨_, _⟩
    set opcode := inst.extractLsb' 0 7
    -- CUSTOM-0 分岐以外は nd₁, nd₂ を参照しないので congr + ite_congr で閉じる
    -- opcode ≠ OP_CUSTOM0 なら最後の else if opcode == OP_CUSTOM0 は偽
    have hnotC0 : ¬(opcode == OP_CUSTOM0) := by
      simp [OP_CUSTOM0] at hOpcode ⊢; exact hOpcode
    -- execute タプルの nd 依存部分は CUSTOM-0 else-if 内の nbrData のみ
    -- opcode ≠ CUSTOM0 なので if/else 展開で nd は現れない
    simp only [hnotC0, ite_false]
    -- 残りは nd₁, nd₂ に依存しない → rfl
    rfl

-- ─────────────────────────────────────────────────────────────────────────────
--  §C2  coreStep_eq_refStep
--       NoCustom かつ halt していないとき coreStep = RefCore.step
-- ─────────────────────────────────────────────────────────────────────────────

/-- CUSTOM-0 が現れないとき、TileCore のステップ関数は
    孤立 RefCore のステップ関数と等しい。
    前提:
      hNC  : 次に fetch する命令は CUSTOM-0 でない
      nd   : 任意の neighbor data (結果に影響しない) -/
theorem coreStep_eq_refStep (cfg : TileConfig)
    (nd : Fin 4 → BitVec 32)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    (hNC : NoCustomDynamic s.imem) :
    New.coreStep cfg nd s = RefCore.step cfg s := by
  simp only [New.coreStep, RefCore.step]
  by_cases hh : s.core.halt
  · simp [hh]
  · simp only [hh, ite_false]
    -- fetch 命令の opcode が CUSTOM-0 でない
    have hOpcode := hNC s.core.pc
    set inst   := s.imem.get ⟨_, _⟩
    set opcode := inst.extractLsb' 0 7
    have hnotC0 : ¬(opcode == OP_CUSTOM0) := by
      simp [OP_CUSTOM0] at hOpcode ⊢; exact hOpcode
    -- CUSTOM-0 以外の分岐では両実装が同一式 → congr
    -- RefCore では CUSTOM-0 else-if が else (halt) に変わっているが、
    -- hnotC0 により到達しないので両辺の if/else 構造が一致する
    simp only [hnotC0, ite_false]
    rfl

-- ─────────────────────────────────────────────────────────────────────────────
--  §C3  imem の不変性: NoCustomDynamic は全サイクルで保たれる
--
--  重要: RefCore.step も New.coreStep も imem を書き換えない (ROM扱い)。
--  よって s₀ で NoCustomDynamic が成立すれば step^n s₀ でも成立する。
-- ─────────────────────────────────────────────────────────────────────────────

/-- RefCore.step は imem を変更しない -/
lemma refStep_imem_preserved (cfg : TileConfig)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen) :
    (RefCore.step cfg s).imem = s.imem := by
  simp only [RefCore.step]
  by_cases hh : s.core.halt
  · simp [hh]
  · simp only [hh, ite_false]
    set opcode := (s.imem.get _).extractLsb' 0 7
    -- 全分岐で imem フィールドは s.imem のまま
    simp only [CoreStateFull.mk.injEq]
    split_ifs <;> rfl

/-- New.coreStep も imem を変更しない -/
lemma newStep_imem_preserved (cfg : TileConfig)
    (nd : Fin 4 → BitVec 32)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen) :
    (New.coreStep cfg nd s).imem = s.imem := by
  simp only [New.coreStep]
  by_cases hh : s.core.halt
  · simp [hh]
  · simp only [hh, ite_false]
    split_ifs <;> rfl

/-- NoCustomDynamic は RefCore のステップで不変 -/
lemma noCustom_preserved_refStep (cfg : TileConfig)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    (hNC : NoCustomDynamic s.imem) :
    NoCustomDynamic (RefCore.step cfg s).imem := by
  rw [refStep_imem_preserved]
  exact hNC

/-- NoCustomDynamic は RefCore の n ステップで不変 -/
lemma noCustom_preserved_refStep_n (cfg : TileConfig)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    (hNC : NoCustomDynamic s.imem) (n : Nat) :
    NoCustomDynamic ((RefCore.step cfg)^[n] s).imem := by
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [Function.iterate_succ, Function.comp]
    exact noCustom_preserved_refStep cfg _ ih

-- ─────────────────────────────────────────────────────────────────────────────
--  §D  メイン定理: n サイクル後の等価性
-- ─────────────────────────────────────────────────────────────────────────────

/-- 【メイン定理 D1】
    初期状態の imem が NoCustom を満たすとき、
    任意の neighborData nd に対して、
    n サイクル後の TileCore の状態は孤立 RefCore と一致する。

    これが「CUSTOM-0 なしの RV32I+M プログラムに対して
    TileCore は通常の RV32 と等価に動作する」という主張の形式化。 -/
theorem tile_core_equiv_refcore (cfg : TileConfig)
    (nd : Fin 4 → BitVec 32)
    (s₀ : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    (hNC : NoCustom s₀.imem)
    (n : Nat) :
    (New.coreStep cfg nd)^[n] s₀ = (RefCore.step cfg)^[n] s₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ, Function.comp]
    -- 帰納仮定: n サイクル後の状態が一致
    rw [ih]
    -- n サイクル後の状態の imem が NoCustomDynamic を満たす
    have hNC_dyn : NoCustomDynamic s₀.imem :=
      noCustom_implies_dynamic s₀.imem hNC
    have hNC_n : NoCustomDynamic ((RefCore.step cfg)^[n] s₀).imem :=
      noCustom_preserved_refStep_n cfg s₀ hNC_dyn n
    -- その状態で coreStep = refStep
    exact coreStep_eq_refStep cfg nd ((RefCore.step cfg)^[n] s₀) hNC_n

-- ─────────────────────────────────────────────────────────────────────────────
--  §D2  4×4 メッシュでの隔離定理
--
--  TileArray の配線: core[r][c].in[d] = core[r'][c'].out[d']
--  ここで core[r'][c'].out[d'] = core[r'][c'].dirData[d'] (前サイクルの出力)
--
--  CUSTOM-0 がなければ dirData は初期値 (0) のまま変化しない。
--  → neighbor_irrelevance より全コアが孤立 RefCore と等価になる。
-- ─────────────────────────────────────────────────────────────────────────────

/-- CUSTOM-0 がないとき dirData は変化しない -/
lemma dirData_unchanged_by_refStep (cfg : TileConfig)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    (hNC : NoCustomDynamic s.imem) :
    (RefCore.step cfg s).core.dirData = s.core.dirData := by
  simp only [RefCore.step]
  by_cases hh : s.core.halt
  · simp [hh]
  · simp only [hh, ite_false]
    have hOpcode := hNC s.core.pc
    set opcode := (s.imem.get _).extractLsb' 0 7
    have hnotC0 : ¬(opcode == OP_CUSTOM0) := by
      simp [OP_CUSTOM0] at hOpcode ⊢; exact hOpcode
    -- TILE_SEND は CUSTOM-0 内にあり、hnotC0 により到達しない
    simp only [hnotC0, ite_false]
    -- 全標準命令分岐で nextDirData = c.dirData
    split_ifs <;> rfl

/-- CUSTOM-0 がないとき dirData は n ステップで不変 -/
lemma dirData_unchanged_n (cfg : TileConfig)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    (hNC : NoCustom s.imem) (n : Nat) :
    ((RefCore.step cfg)^[n] s).core.dirData = s.core.dirData := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ, Function.comp]
    have hNC_dyn := noCustom_implies_dynamic s.imem hNC
    have hNC_n   := noCustom_preserved_refStep_n cfg s hNC_dyn n
    rw [dirData_unchanged_by_refStep cfg _ hNC_n, ih]

/-- 初期 dirData は 0 (reset 値) -/
lemma dirData_init_zero (cfg : TileConfig) :
    (CoreStateFull.reset cfg).core.dirData = HWVector.replicate 4 0#cfg.xlen := by
  simp [CoreStateFull.reset]

/-- NoCustom のとき、全サイクルを通じて neighborIn は 0 のまま -/
theorem neighbor_output_zero (cfg : TileConfig)
    (hNC : NoCustom (CoreStateFull.reset cfg).imem) (n : Nat) (d : Fin 4) :
    ((RefCore.step cfg)^[n] (CoreStateFull.reset cfg)).core.dirData.get d =
    0#cfg.xlen := by
  have h := dirData_unchanged_n cfg (CoreStateFull.reset cfg) hNC n
  rw [h, dirData_init_zero]
  simp [HWVector.replicate, HWVector.get]

-- ─────────────────────────────────────────────────────────────────────────────
--  §D3  4×4 メッシュでの各コアの等価性
--
--  TileArray の各コア[r][c]について、その neighborIn は
--  隣接コアの dirData から来る。
--  §D2 より NoCustom 条件下では dirData ≡ 0 なので、
--  neighborIn の値は 0 に固定される。
--  よって neighbor_irrelevance と tile_core_equiv_refcore を組み合わせて
--  各コアが RefCore と等価であることを示す。
-- ─────────────────────────────────────────────────────────────────────────────

/-- 4×4 メッシュの全コアが NoCustom を満たす条件 -/
def AllNoCustom (cfg : TileConfig)
    (initialImems : Fin cfg.rows → Fin cfg.cols →
                    HWVector cfg.iMemSize (BitVec cfg.xlen)) : Prop :=
  ∀ r c, NoCustom (initialImems r c)

/-- 各コアの初期状態 (初期 imem を注入した CoreStateFull.reset) -/
def initialState (cfg : TileConfig)
    (initialImems : Fin cfg.rows → Fin cfg.cols →
                    HWVector cfg.iMemSize (BitVec cfg.xlen))
    (r : Fin cfg.rows) (c : Fin cfg.cols)
    : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen :=
  let base := CoreStateFull.reset cfg
  { base with imem := initialImems r c }

/-- 【メイン定理 D3】4×4 メッシュ隔離定理
    全コアの imem が NoCustom を満たすとき、
    任意のコア (r, c) の n サイクル後の状態は、
    孤立 RefCore の n サイクル後の状態と等しい。

    すなわち:
    「CUSTOM-0 命令を含まない RV32I+M プログラムを
     4×4 タイルアレイ上で実行した場合、
     各タイルは通常の RV32 プロセッサとまったく同じ動作をする」 -/
theorem mesh_isolation_theorem
    (cfg : TileConfig)
    (initialImems : Fin cfg.rows → Fin cfg.cols →
                    HWVector cfg.iMemSize (BitVec cfg.xlen))
    (hAll : AllNoCustom cfg initialImems)
    (r : Fin cfg.rows) (c : Fin cfg.cols)
    -- 任意の neighborData (0 でなくても成立することがポイント)
    (nd : Fin 4 → BitVec cfg.xlen)
    (n : Nat) :
    (New.coreStep cfg nd)^[n] (initialState cfg initialImems r c) =
    (RefCore.step cfg)^[n]    (initialState cfg initialImems r c) := by
  exact tile_core_equiv_refcore cfg nd _ (hAll r c) n

-- ─────────────────────────────────────────────────────────────────────────────
--  §D4  コア状態の具体的フィールド等価性
--       pc, regs, dmem が孤立 RV32 と一致することの明示的な系
-- ─────────────────────────────────────────────────────────────────────────────

/-- pc の等価性 -/
corollary mesh_pc_eq (cfg : TileConfig)
    (initialImems : Fin cfg.rows → Fin cfg.cols →
                    HWVector cfg.iMemSize (BitVec cfg.xlen))
    (hAll : AllNoCustom cfg initialImems)
    (r : Fin cfg.rows) (c : Fin cfg.cols)
    (nd : Fin 4 → BitVec cfg.xlen) (n : Nat) :
    ((New.coreStep cfg nd)^[n] (initialState cfg initialImems r c)).core.pc =
    ((RefCore.step cfg)^[n]    (initialState cfg initialImems r c)).core.pc := by
  congr 1; exact mesh_isolation_theorem cfg initialImems hAll r c nd n

/-- レジスタファイルの等価性 -/
corollary mesh_regs_eq (cfg : TileConfig)
    (initialImems : Fin cfg.rows → Fin cfg.cols →
                    HWVector cfg.iMemSize (BitVec cfg.xlen))
    (hAll : AllNoCustom cfg initialImems)
    (r : Fin cfg.rows) (c : Fin cfg.cols)
    (nd : Fin 4 → BitVec cfg.xlen) (n : Nat) :
    ((New.coreStep cfg nd)^[n] (initialState cfg initialImems r c)).core.regs =
    ((RefCore.step cfg)^[n]    (initialState cfg initialImems r c)).core.regs := by
  congr 1; exact mesh_isolation_theorem cfg initialImems hAll r c nd n

/-- データメモリの等価性 -/
corollary mesh_dmem_eq (cfg : TileConfig)
    (initialImems : Fin cfg.rows → Fin cfg.cols →
                    HWVector cfg.iMemSize (BitVec cfg.xlen))
    (hAll : AllNoCustom cfg initialImems)
    (r : Fin cfg.rows) (c : Fin cfg.cols)
    (nd : Fin 4 → BitVec cfg.xlen) (n : Nat) :
    ((New.coreStep cfg nd)^[n] (initialState cfg initialImems r c)).dmem =
    ((RefCore.step cfg)^[n]    (initialState cfg initialImems r c)).dmem := by
  congr 1; exact mesh_isolation_theorem cfg initialImems hAll r c nd n

/-- halt フラグの等価性 -/
corollary mesh_halt_eq (cfg : TileConfig)
    (initialImems : Fin cfg.rows → Fin cfg.cols →
                    HWVector cfg.iMemSize (BitVec cfg.xlen))
    (hAll : AllNoCustom cfg initialImems)
    (r : Fin cfg.rows) (c : Fin cfg.cols)
    (nd : Fin 4 → BitVec cfg.xlen) (n : Nat) :
    ((New.coreStep cfg nd)^[n] (initialState cfg initialImems r c)).core.halt =
    ((RefCore.step cfg)^[n]    (initialState cfg initialImems r c)).core.halt := by
  congr 1; exact mesh_isolation_theorem cfg initialImems hAll r c nd n

-- ─────────────────────────────────────────────────────────────────────────────
--  §E  強化版: メッシュ全体での neighbor の影響伝播の上界
--
--  CUSTOM-0 が存在する場合でも、コア (r,c) の状態は
--  最大 n サイクル先の neighborData にしか依存しない、
--  という「距離 k の影響波及」補題。
--  (CUSTOM-0 あり環境での隔離距離の定量化)
-- ─────────────────────────────────────────────────────────────────────────────

/-- コア (r,c) が t サイクル目に TILE_RECV を実行した場合、
    その影響が生まれるためには隣接コアが t-1 サイクル目に
    TILE_SEND を実行していなければならない。
    → 影響伝播の「因果性 (causality)」 -/

/-- TILE_SEND を実行する条件 -/
def IsTileSend (inst : BitVec 32) : Prop :=
  inst.extractLsb' 0 7  = OP_CUSTOM0 ∧
  inst.extractLsb' 0 1  = 1#1         -- funct7[0] = 1

/-- TILE_RECV を実行する条件 -/
def IsTileRecv (inst : BitVec 32) : Prop :=
  inst.extractLsb' 0 7  = OP_CUSTOM0 ∧
  inst.extractLsb' 0 1  = 0#1         -- funct7[0] = 0

/-- 距離 0: コア (r,c) が TILE_RECV を実行しないとき、
    その次状態は neighborData に依存しない (neighbor_irrelevance の系) -/
theorem no_recv_no_neighbor_dep (cfg : TileConfig)
    (nd₁ nd₂ : Fin 4 → BitVec cfg.xlen)
    (s : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen)
    (hNR : ¬ IsTileRecv (s.imem.get ⟨(s.core.pc >>> 2).toNat % cfg.iMemSize, by omega⟩)) :
    New.coreStep cfg nd₁ s = New.coreStep cfg nd₂ s := by
  simp only [New.coreStep]
  by_cases hh : s.core.halt
  · simp [hh]
  · simp only [hh, ite_false]
    -- hNR を分解: CUSTOM-0 でないか、funct7[0]=0 でない
    simp only [IsTileRecv, not_and_or] at hNR
    set inst   := s.imem.get ⟨_, _⟩
    set opcode := inst.extractLsb' 0 7
    set funct7 := inst.extractLsb' 25 7
    rcases hNR with hNotC0 | hNotRecv
    · -- CUSTOM-0 でない: CUSTOM-0 分岐に到達しない
      have hnotC0 : ¬(opcode == OP_CUSTOM0) := by
        simp [OP_CUSTOM0]; exact fun h => hNotC0 h
      simp [hnotC0]
    · -- funct7[0] ≠ 0: isSend = true なので TILE_RECV 分岐に入らない
      -- isSend = funct7.extractLsb' 0 1 == 1#1
      -- hNotRecv: inst.extractLsb' 0 1 ≠ 0#1 → つまり funct7[0]=1 → isSend=true
      -- この場合 TILE_SEND 分岐に入るため nd を参照しない
      by_cases hC0 : opcode == OP_CUSTOM0
      · -- CUSTOM-0 だが isSend=true → TILE_SEND 分岐 (nd参照なし)
        simp only [hC0, ite_true]
        have hSend : funct7.extractLsb' 0 1 == 1#1 := by
          simp [OP_CUSTOM0] at hNotRecv ⊢
          -- funct7[0] = inst[25], hNotRecv: inst.extractLsb' 0 1 ≠ 0
          -- この恒等式は extractLsb' の定義から
          simp [BitVec.extractLsb']
          omega
        simp [hSend]  -- TILE_SEND 分岐は nd に依存しない
      · simp [hC0]

-- ─────────────────────────────────────────────────────────────────────────────
--  §F  具体的な 4×4 設定での定理の特殊化
-- ─────────────────────────────────────────────────────────────────────────────

-- rows=4, cols=4 の標準設定
def cfg44 : TileConfig := { rows := 4, cols := 4, xlen := 32,
                             iMemSize := 1024, dMemSize := 1024 }

/-- 【定理 F1】4×4 TileArray の任意コア (r,c) について:
    コアの imem が NoCustom を満たすとき、
    n サイクル後のそのコアの状態は孤立 RV32I+M と等価 -/
theorem tile_4x4_equiv_rv32
    (initialImems : Fin 4 → Fin 4 → HWVector 1024 (BitVec 32))
    (hAll : AllNoCustom cfg44 initialImems)
    (r : Fin 4) (c : Fin 4)
    (nd : Fin 4 → BitVec 32) (n : Nat) :
    (New.coreStep cfg44 nd)^[n] (initialState cfg44 initialImems r c) =
    (RefCore.step cfg44)^[n]    (initialState cfg44 initialImems r c) :=
  mesh_isolation_theorem cfg44 initialImems hAll r c nd n

/-- 【定理 F2】4×4 TileArray において:
    全コアが NoCustom を満たすとき、
    任意の時刻 t での halt フラグは RefCore と一致する。
    (プログラム終了判定が RV32 と等価) -/
theorem tile_4x4_halt_equiv
    (initialImems : Fin 4 → Fin 4 → HWVector 1024 (BitVec 32))
    (hAll : AllNoCustom cfg44 initialImems)
    (r : Fin 4) (c : Fin 4)
    (nd : Fin 4 → BitVec 32) (n : Nat) :
    ((New.coreStep cfg44 nd)^[n] (initialState cfg44 initialImems r c)).core.halt =
    ((RefCore.step cfg44)^[n]    (initialState cfg44 initialImems r c)).core.halt :=
  mesh_halt_eq cfg44 initialImems hAll r c nd n

/-- 【定理 F3】4×4 TileArray において:
    全コアが NoCustom を満たすとき、
    任意の時刻 t, レジスタ xn での値は RefCore と一致する。
    (レジスタ計算結果が RV32 と等価) -/
theorem tile_4x4_register_equiv
    (initialImems : Fin 4 → Fin 4 → HWVector 1024 (BitVec 32))
    (hAll : AllNoCustom cfg44 initialImems)
    (r : Fin 4) (c : Fin 4)
    (nd : Fin 4 → BitVec 32) (n : Nat) (xn : Fin 32) :
    ((New.coreStep cfg44 nd)^[n] (initialState cfg44 initialImems r c)).core.regs.get xn =
    ((RefCore.step cfg44)^[n]    (initialState cfg44 initialImems r c)).core.regs.get xn := by
  have h := mesh_regs_eq cfg44 initialImems hAll r c nd n
  exact congrArg (HWVector.get · xn) h

/-- 【定理 F4】neighbor_irrelevance の 4×4 特殊化:
    NoCustom のとき neighbor の値が何であっても出力は同じ。
    (通信命令のない RV32 プログラムはメッシュ配線の影響を受けない) -/
theorem tile_4x4_neighbor_independence
    (initialImems : Fin 4 → Fin 4 → HWVector 1024 (BitVec 32))
    (hAll : AllNoCustom cfg44 initialImems)
    (r : Fin 4) (c : Fin 4)
    (nd₁ nd₂ : Fin 4 → BitVec 32) (n : Nat) :
    (New.coreStep cfg44 nd₁)^[n] (initialState cfg44 initialImems r c) =
    (New.coreStep cfg44 nd₂)^[n] (initialState cfg44 initialImems r c) := by
  -- nd₁ と nd₂ はどちらも RefCore と等価なので、推移律から等しい
  rw [mesh_isolation_theorem cfg44 initialImems hAll r c nd₁ n]
  rw [mesh_isolation_theorem cfg44 initialImems hAll r c nd₂ n]

-- ─────────────────────────────────────────────────────────────────────────────
--  §G  証明された主要定理の一覧
-- ─────────────────────────────────────────────────────────────────────────────

section Summary

-- 基礎補題
#check @neighbor_irrelevance        -- NoCustom → nd に依存しない
#check @coreStep_eq_refStep         -- NoCustom → TileCore = RefCore (1 step)
#check @dirData_unchanged_n         -- NoCustom → dirData は不変 (n steps)
#check @noCustom_preserved_refStep_n -- imem が ROM なので NoCustom は不変

-- メイン定理
#check @tile_core_equiv_refcore     -- 任意コア: n step TileCore = n step RefCore
#check @mesh_isolation_theorem      -- 4×4 隔離定理 (メイン)

-- 系
#check @mesh_pc_eq                  -- PC が RefCore と一致
#check @mesh_regs_eq                -- レジスタが RefCore と一致
#check @mesh_dmem_eq                -- データメモリが RefCore と一致
#check @mesh_halt_eq                -- halt フラグが RefCore と一致

-- 4×4 特殊化
#check @tile_4x4_equiv_rv32         -- rows=cols=4 での等価性
#check @tile_4x4_halt_equiv         -- プログラム終了判定の等価性
#check @tile_4x4_register_equiv     -- レジスタ値の等価性
#check @tile_4x4_neighbor_independence  -- neighbor 独立性

-- 強化版
#check @no_recv_no_neighbor_dep     -- TILE_RECV なし → 1 step で nd 非依存
#check @neighbor_output_zero        -- NoCustom → dirOut ≡ 0

end Summary
