-- =============================================================================
--  TileRiscV.lean  ─  Tiled RISC-V Array in Sparkle HDL (Lean 4 Signal DSL)
-- =============================================================================
--
--  Original: TileRiscV.scala (Chisel 6, RV32I+M, 4×4 mesh)
--  Port:     Sparkle HDL  https://github.com/Verilean/sparkle
--
--  Refactored to import combinational components from IP.RV32.Core:
--
--   mextCompute        → pure-Lean RV32M div/rem/mul (replaces §7 mExtResult)
--   aluSignal          → Signal-level RV32I ALU      (replaces §8 aluResult)
--   branchCompSignal   → branch comparator            (replaces §9 branchTaken)
--   decoderFieldsSignal→ field extraction             (replaces §6 immI/S/B/U/J)
--   immGenSignal       → immediate generation
--   aluControlSignal   → ALU op selector
--   controlSignalsSignal→ all control bits from opcode
--
--  Custom Instructions  (CUSTOM-0, opcode = 0x0B)
--  ────────────────────────────────────────────────
--   TILE_RECV rd,  dir   funct7[0]=0  rd ← neighbor[dir].outReg
--   TILE_SEND dir, rs1   funct7[0]=1  outReg[dir] ← rs1
--   dir = funct3[1:0]  →  0=N 1=S 2=E 3=W
-- =============================================================================

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.Core   -- aluSignal, branchCompSignal, decoderFieldsSignal,
                      -- immGenSignal, aluControlSignal, controlSignalsSignal,
                      -- mextCompute, mulComputeSignal

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32  -- brings mextCompute, mulComputeSignal, aluSignal, …

-- ─────────────────────────────────────────────────────────────────────────────
--  §1  Configuration
-- ─────────────────────────────────────────────────────────────────────────────

structure TileConfig where
  rows     : Nat := 4
  cols     : Nat := 4
  xlen     : Nat := 32
  iMemSize : Nat := 1024
  dMemSize : Nat := 1024

-- ─────────────────────────────────────────────────────────────────────────────
--  §2  Direction indices
-- ─────────────────────────────────────────────────────────────────────────────

abbrev DirN : Fin 4 := ⟨0, by omega⟩
abbrev DirS : Fin 4 := ⟨1, by omega⟩
abbrev DirE : Fin 4 := ⟨2, by omega⟩
abbrev DirW : Fin 4 := ⟨3, by omega⟩

-- ─────────────────────────────────────────────────────────────────────────────
--  §3  CUSTOM-0 opcode only
--      All standard RV32 opcode literals are removed; they live inside the
--      imported Core.lean functions (aluControlSignal, controlSignalsSignal,
--      immGenSignal) and are not needed here anymore.
-- ─────────────────────────────────────────────────────────────────────────────

def OP_CUSTOM0 : BitVec 7 := 0b0001011#7

-- ─────────────────────────────────────────────────────────────────────────────
--  §4  Directional port bundle
-- ─────────────────────────────────────────────────────────────────────────────

structure DirPort (xlen : Nat) where
  valid : Bool
  data  : BitVec xlen

def DirPort.zero (xlen : Nat) : DirPort xlen := { valid := false, data := 0#xlen }

-- ─────────────────────────────────────────────────────────────────────────────
--  §5  Core state
-- ─────────────────────────────────────────────────────────────────────────────

structure CoreState (xlen : Nat) where
  pc       : BitVec xlen
  regs     : HWVector 32 (BitVec xlen)
  dirData  : HWVector 4  (BitVec xlen)
  dirValid : HWVector 4  Bool
  halt     : Bool

structure CoreStateFull (iMemSize dMemSize xlen : Nat) where
  core : CoreState xlen
  imem : HWVector iMemSize (BitVec xlen)
  dmem : HWVector dMemSize (BitVec xlen)

def CoreStateFull.reset (cfg : TileConfig) : CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen :=
  { core := { pc       := 0#cfg.xlen
              regs     := HWVector.replicate 32 0#cfg.xlen
              dirData  := HWVector.replicate 4  0#cfg.xlen
              dirValid := HWVector.replicate 4  false
              halt     := false }
    imem := HWVector.replicate cfg.iMemSize 0#cfg.xlen
    dmem := HWVector.replicate cfg.dMemSize 0#cfg.xlen }

-- ─────────────────────────────────────────────────────────────────────────────
--  §6  Minimal pure helpers  (not covered by Core.lean's Signal-level API)
-- ─────────────────────────────────────────────────────────────────────────────

-- x0 hardwiring — used inside loopMemo where we have BitVec, not Signal
@[inline] def regRead {xlen : Nat} (rf : HWVector 32 (BitVec xlen)) (idx : BitVec 5)
    : BitVec xlen :=
  if idx == 0#5 then 0#xlen else rf.get idx.toFin

-- Load-data byte/half-word selector — not provided by Core.lean
@[inline] def selectLoad (funct3 : BitVec 3) (word : BitVec 32) (addr : BitVec 32)
    : BitVec 32 :=
  let byteOff := (addr.extractLsb' 0 2).toNat * 8
  let halfOff := (addr.extractLsb' 1 1).toNat * 16
  let byte    := (word >>> byteOff).extractLsb' 0 8
  let half    := (word >>> halfOff).extractLsb' 0 16
  match funct3.toNat with
  | 0 => byte.signExtend 32   -- LB
  | 1 => half.signExtend 32   -- LH
  | 2 => word                  -- LW
  | 4 => byte.zeroExtend 32   -- LBU
  | _ => half.zeroExtend 32   -- LHU

-- ─────────────────────────────────────────────────────────────────────────────
--  §7  Pure wrappers around Core.lean combinational logic
--
--  Core.lean exposes Signal-level functions (operating on `Signal dom α`).
--  Inside Signal.loopMemo we have plain BitVec values.  The wrappers below
--  call Signal.pure to lift a single value, apply the Core.lean combinator,
--  then extract via `.currentValue` — the standard Sparkle pattern for using
--  Signal combinators on constants inside loopMemo.
--
--  This replaces the entire hand-written §6–§9 from the previous version:
--    immI/immS/immB/immU/immJ  →  immGenSignal  (via decodeImm)
--    aluResult                 →  aluSignal      (via applyAlu)
--    mExtResult                →  mextCompute    (direct call — already pure)
--    branchTaken               →  branchCompSignal (via applyBranch)
--    aluOp derivation          →  aluControlSignal (via decodeAluOp)
-- ─────────────────────────────────────────────────────────────────────────────

-- Field extraction — mirrors decoderFieldsSignal's BitVec.extractLsb' calls
@[inline] def decodeFields (inst : BitVec 32)
    : BitVec 7 × BitVec 5 × BitVec 3 × BitVec 5 × BitVec 5 × BitVec 7 :=
  ( inst.extractLsb' 0  7   -- opcode
  , inst.extractLsb' 7  5   -- rd
  , inst.extractLsb' 12 3   -- funct3
  , inst.extractLsb' 15 5   -- rs1
  , inst.extractLsb' 20 5   -- rs2
  , inst.extractLsb' 25 7 ) -- funct7

-- Immediate — delegates to immGenSignal applied to a constant Signal
@[inline] def decodeImm (opcode : BitVec 7) (inst : BitVec 32) : BitVec 32 :=
  (immGenSignal (Signal.pure inst) (Signal.pure opcode)).currentValue

-- ALU opcode — delegates to aluControlSignal applied to constant Signals
@[inline] def decodeAluOp (opcode : BitVec 7) (funct3 : BitVec 3) (funct7 : BitVec 7)
    : BitVec 4 :=
  (aluControlSignal (Signal.pure opcode)
                    (Signal.pure funct3)
                    (Signal.pure funct7)).currentValue

-- Integer ALU result — delegates to aluSignal applied to constant Signals
@[inline] def applyAlu (op : BitVec 4) (a b : BitVec 32) : BitVec 32 :=
  (aluSignal (Signal.pure op) (Signal.pure a) (Signal.pure b)).currentValue

-- Branch condition — delegates to branchCompSignal applied to constant Signals
@[inline] def applyBranch (funct3 : BitVec 3) (a b : BitVec 32) : Bool :=
  (branchCompSignal (Signal.pure funct3) (Signal.pure a) (Signal.pure b)).currentValue

-- ALU source-B selector — mirrors controlSignalsSignal's aluSrcB computation
@[inline] def aluSrcBSel (opcode : BitVec 7) : Bool :=
  let ctrl := (controlSignalsSignal (Signal.pure opcode)).currentValue
  -- aluSrcB is the first field of the nested pair returned by controlSignalsSignal
  -- type: ((Bool × (Bool × Bool)) × ((Bool × (Bool × Bool)) × (Bool × (Bool × Bool))))
  ctrl.1.1

-- ─────────────────────────────────────────────────────────────────────────────
--  §8  Full TileCore
-- ─────────────────────────────────────────────────────────────────────────────

def tileCoreFullDef {dom : DomainConfig} (cfg : TileConfig)
    (neighborIn : HWVector 4 (Signal dom (DirPort cfg.xlen)))
    : Signal dom (CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen) :=

  Signal.loopMemo (CoreStateFull.reset cfg) fun s =>

    let c    := s.core
    let imem := s.imem
    let dmem := s.dmem

    if c.halt then s
    else

    -- ── Fetch ──────────────────────────────────────────────────────────────
    let wordAddr := (c.pc >>> 2).toNat % cfg.iMemSize
    let inst     := imem.get ⟨wordAddr, by omega⟩

    -- ── Decode ─────────────────────────────────────────────────────────────
    --  All field extraction via decodeFields (≡ decoderFieldsSignal internals)
    let (opcode, rd, funct3, rs1Idx, rs2Idx, funct7) := decodeFields inst

    let rs1Val  := regRead c.regs rs1Idx
    let rs2Val  := regRead c.regs rs2Idx

    -- ── Immediate (immGenSignal) ─────────────────────────────────────────────
    let imm     := decodeImm opcode inst

    -- ── ALU (aluControlSignal + aluSignal) ──────────────────────────────────
    let aluSrcB := aluSrcBSel opcode                  -- controlSignalsSignal
    let aluB    := if aluSrcB then imm else rs2Val
    let aluOp   := decodeAluOp opcode funct3 funct7   -- aluControlSignal
    let alu     := applyAlu aluOp rs1Val aluB          -- aluSignal

    -- ── RV32M (mextCompute from Core.lean) ──────────────────────────────────
    let isMExt  := funct7 == 0b0000001#7
    let mResult := mextCompute funct3 rs1Val rs2Val

    -- ── Branch (branchCompSignal) ────────────────────────────────────────────
    let taken   := applyBranch funct3 rs1Val rs2Val

    -- ── Load ────────────────────────────────────────────────────────────────
    let ldAddr   := rs1Val + (decodeImm 0b0000011#7 inst)  -- force I-type imm
    let ldWordIdx := (ldAddr >>> 2).toNat % cfg.dMemSize
    let ldWord   := dmem.get ⟨ldWordIdx, by omega⟩
    let loadData := selectLoad funct3 ldWord ldAddr

    -- ── Tile instruction decode ─────────────────────────────────────────────
    let tileDir  := (funct3.extractLsb' 0 2).toFin (by omega)
    let isSend   := funct7.extractLsb' 0 1 == 1#1

    -- ── Execute + write-back ────────────────────────────────────────────────
    let (rdWen, rdWdata, nextPc, nextHalt, nextDirData, nextDirValid, nextDmem) :=

      if opcode == 0b0110111#7 then                  -- LUI
        (true, alu, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)

      else if opcode == 0b0010111#7 then             -- AUIPC
        (true, c.pc + imm, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)

      else if opcode == 0b1101111#7 then             -- JAL
        (true, c.pc + 4#32, c.pc + imm, false, c.dirData, c.dirValid, dmem)

      else if opcode == 0b1100111#7 then             -- JALR
        let target := (rs1Val + decodeImm 0b0000011#7 inst) &&& (~~~1#32)
        (true, c.pc + 4#32, target, false, c.dirData, c.dirValid, dmem)

      else if opcode == 0b1100011#7 then             -- BRANCH
        let brPc := if taken then c.pc + imm else c.pc + 4#32
        (false, 0#32, brPc, false, c.dirData, c.dirValid, dmem)

      else if opcode == 0b0000011#7 then             -- LOAD
        (true, loadData, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)

      else if opcode == 0b0100011#7 then             -- STORE
        let stIdx   := ((rs1Val + imm) >>> 2).toNat % cfg.dMemSize
        let newDmem := dmem.set ⟨stIdx, by omega⟩ rs2Val
        (false, 0#32, c.pc + 4#32, false, c.dirData, c.dirValid, newDmem)

      else if opcode == 0b0010011#7 then             -- ALU-IMM
        (true, alu, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)

      else if opcode == 0b0110011#7 then             -- ALU-RR (RV32I/M)
        (true, if isMExt then mResult else alu,
         c.pc + 4#32, false, c.dirData, c.dirValid, dmem)

      else if opcode == 0b1110011#7 then             -- SYSTEM → halt
        (false, 0#32, c.pc, true, c.dirData, c.dirValid, dmem)

      else if opcode == OP_CUSTOM0 then
        if isSend then
          -- TILE_SEND dir, rs1
          let newDirData  := c.dirData.set  tileDir rs1Val
          let newDirValid := c.dirValid.set tileDir true
          (false, 0#32, c.pc + 4#32, false, newDirData, newDirValid, dmem)
        else
          -- TILE_RECV rd, dir  ← neighbor's registered dirData (1-cycle latency)
          let nbrData := (neighborIn.get tileDir).currentValue.data
          (true, nbrData, c.pc + 4#32, false, c.dirData, c.dirValid, dmem)

      else
        (false, 0#32, c.pc, inst == 0#32, c.dirData, c.dirValid, dmem)

    -- ── Register file write (x0 hardwired 0) ────────────────────────────────
    let rdIdx5  := rd.extractLsb' 0 5
    let newRegs := if rdWen && rdIdx5 != 0#5 then c.regs.set rdIdx5.toFin rdWdata
                  else c.regs

    { core  := { pc := nextPc, regs := newRegs
                 dirData := nextDirData, dirValid := nextDirValid
                 halt := nextHalt }
      imem  := imem
      dmem  := nextDmem }

-- ─────────────────────────────────────────────────────────────────────────────
--  §9  TileArray  ─  N×M mesh wiring
-- ─────────────────────────────────────────────────────────────────────────────

abbrev CoreGrid (rows cols iMemSize dMemSize xlen : Nat) :=
  Array (Array (Signal defaultDomain (CoreStateFull iMemSize dMemSize xlen)))

def tileArray (cfg : TileConfig) : CoreGrid cfg.rows cfg.cols cfg.iMemSize cfg.dMemSize cfg.xlen :=
  let zeroDirPort : Signal defaultDomain (DirPort cfg.xlen) :=
    Signal.pure (DirPort.zero cfg.xlen)
  let dirOut (coreSig : Signal defaultDomain (CoreStateFull cfg.iMemSize cfg.dMemSize cfg.xlen))
             (dir : Fin 4) : Signal defaultDomain (DirPort cfg.xlen) :=
    coreSig <$> fun s => { valid := s.core.dirValid.get dir, data := s.core.dirData.get dir }
  let grid : Array (Array _) :=
    Array.ofFn (n := cfg.rows) fun r =>
    Array.ofFn (n := cfg.cols) fun c =>
      let nbrN := if r > 0            then dirOut (grid.get! (r-1) |>.get! c)  DirS else zeroDirPort
      let nbrS := if r + 1 < cfg.rows then dirOut (grid.get! (r+1) |>.get! c)  DirN else zeroDirPort
      let nbrE := if c + 1 < cfg.cols then dirOut (grid.get! r |>.get! (c+1))  DirW else zeroDirPort
      let nbrW := if c > 0            then dirOut (grid.get! r |>.get! (c-1))  DirE else zeroDirPort
      tileCoreFullDef cfg (HWVector.ofList [nbrN, nbrS, nbrE, nbrW])
  grid

-- ─────────────────────────────────────────────────────────────────────────────
--  §10  Synthesis entry point
-- ─────────────────────────────────────────────────────────────────────────────

def tileArrayTop : Signal defaultDomain (HWVector (4 * 4) Bool) :=
  let grid := tileArray { rows := 4, cols := 4, xlen := 32,
                          iMemSize := 1024, dMemSize := 1024 }
  let haltSignals : Array (Signal defaultDomain Bool) :=
    (Array.range 4).flatMap fun r =>
    (Array.range 4).map     fun c =>
      (grid.get! r |>.get! c) <$> fun s => s.core.halt
  Signal.mapN haltSignals (fun v => HWVector.ofArray v)

#synthesizeVerilog tileArrayTop

-- ─────────────────────────────────────────────────────────────────────────────
--  §11  Formal properties
-- ─────────────────────────────────────────────────────────────────────────────

-- x0 is always zero at reset
theorem x0_always_zero (cfg : TileConfig) :
    (CoreStateFull.reset cfg).core.regs.get ⟨0, by omega⟩ = 0#cfg.xlen := by
  simp [CoreStateFull.reset, HWVector.replicate, HWVector.get]

-- mextCompute (Core.lean) is called directly — no local re-implementation.
-- The following shows the MUL lower-32 contract matches the Core.lean docstring.
theorem mul_lower_32 (a b : BitVec 32) :
    mextCompute 0#3 a b = BitVec.ofInt 32 (a.toInt * b.toInt) := by
  simp [mextCompute]

-- ─────────────────────────────────────────────────────────────────────────────
--  §12  Simulation smoke-test
-- ─────────────────────────────────────────────────────────────────────────────

#eval do
  let cfg : TileConfig := { rows := 1, cols := 1, xlen := 32,
                             iMemSize := 1024, dMemSize := 1024 }
  let zeroDirPort : Signal defaultDomain (DirPort 32) := Signal.pure (DirPort.zero 32)
  let neighborIn  := HWVector.replicate 4 zeroDirPort
  let coreSig     := tileCoreFullDef cfg neighborIn
  let samples := (List.range 5).map fun t => (coreSig.sample t).core.halt
  IO.println s!"halt per cycle: {samples}"
