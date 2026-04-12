// =============================================================================
//  TileRiscV.scala  ―  Tiled RISC-V Array with Inter-core Register Transfer
// =============================================================================
//
//  Architecture Overview
//  ─────────────────────
//
//      col:  0       1       2       3
//  row 0: [Core]─E─[Core]─E─[Core]─E─[Core]
//            |       |       |       |
//            S       S       S       S
//            |       |       |       |
//  row 1: [Core]─E─[Core]─E─[Core]─E─[Core]
//            |       |       |       |
//            ...
//
//  Each core is a single-cycle RV32I implementation with two custom
//  instructions that transfer register values to/from adjacent cores.
//
//  Custom Instruction Encoding  (CUSTOM-0 opcode  0x0B)
//  ─────────────────────────────────────────────────────
//
//   31      25 24  20 19  15 14  12 11   7 6      0
//  ┌─────────┬──────┬──────┬──────┬──────┬────────┐
//  │ funct7  │ rs2  │ rs1  │funct3│  rd  │ opcode │
//  └─────────┴──────┴──────┴──────┴──────┴────────┘
//
//  TILE_RECV rd, dir          funct7[0]=0
//    rd ← neighbor[dir].out_reg
//
//  TILE_SEND dir, rs1         funct7[0]=1
//    this.out_reg[dir] ← rs1
//
//  dir = funct3[1:0]  →  0=NORTH  1=SOUTH  2=EAST  3=WEST
//
//  Communication Model
//  ───────────────────
//  Each core maintains four directional output registers (one per direction).
//  TILE_SEND writes rs1 into this core's output register for direction dir.
//  The neighboring core reads it via its own TILE_RECV in the next cycle
//  (one-cycle registered latency).  Edge cores see 0/invalid from outside.
//
// =============================================================================

package tilearrray

import chisel3._
import chisel3.util._

// ─────────────────────────────────────────────────────────────────────────────
//  Configuration
// ─────────────────────────────────────────────────────────────────────────────

case class TileConfig(
  rows:     Int = 4,
  cols:     Int = 4,
  xlen:     Int = 32,
  iMemSize: Int = 1024,   // instruction memory depth (words) per core
  dMemSize: Int = 1024    // data memory depth (words) per core
)

// ─────────────────────────────────────────────────────────────────────────────
//  Direction indices
// ─────────────────────────────────────────────────────────────────────────────

object Dir {
  val N = 0; val S = 1; val E = 2; val W = 3
}

// ─────────────────────────────────────────────────────────────────────────────
//  Standard RV32I opcodes + CUSTOM-0
// ─────────────────────────────────────────────────────────────────────────────

object Opcode {
  val LUI     = "b0110111".U(7.W)
  val AUIPC   = "b0010111".U(7.W)
  val JAL     = "b1101111".U(7.W)
  val JALR    = "b1100111".U(7.W)
  val BRANCH  = "b1100011".U(7.W)
  val LOAD    = "b0000011".U(7.W)
  val STORE   = "b0100011".U(7.W)
  val OP_IMM  = "b0010011".U(7.W)
  val OP      = "b0110011".U(7.W)
  val SYSTEM  = "b1110011".U(7.W)
  val CUSTOM0 = "b0001011".U(7.W)   // ← tile communication
}

// ─────────────────────────────────────────────────────────────────────────────
//  Inter-tile directional port (one direction, one side)
// ─────────────────────────────────────────────────────────────────────────────

class DirPort(xlen: Int) extends Bundle {
  val valid = Bool()
  val data  = UInt(xlen.W)
}

// ─────────────────────────────────────────────────────────────────────────────
//  Single RV32I Core with Tile Communication Extensions
// ─────────────────────────────────────────────────────────────────────────────

class TileCore(cfg: TileConfig) extends Module {
  val io = IO(new Bundle {
    /** This core's directional output registers, read by neighbors */
    val out    = Output(Vec(4, new DirPort(cfg.xlen)))
    /** Neighbor cores' directional output registers, read by this core */
    val in     = Input(Vec(4, new DirPort(cfg.xlen)))

    val halt   = Output(Bool())
    val dbgPc  = Output(UInt(cfg.xlen.W))
    val dbgReg = Output(Vec(32, UInt(cfg.xlen.W)))
  })

  val imem = Mem(cfg.iMemSize, UInt(cfg.xlen.W))
  val dmem = Mem(cfg.dMemSize, UInt(cfg.xlen.W))

  val regs    = RegInit(VecInit(Seq.fill(32)(0.U(cfg.xlen.W))))
  val pc      = RegInit(0.U(cfg.xlen.W))
  val haltReg = RegInit(false.B)

  // ── Directional output registers (written by TILE_SEND) ─────────────────────
  val dirData  = RegInit(VecInit(Seq.fill(4)(0.U(cfg.xlen.W))))
  val dirValid = RegInit(VecInit(Seq.fill(4)(false.B)))

  for (d <- 0 until 4) {
    io.out(d).data  := dirData(d)
    io.out(d).valid := dirValid(d)
  }

  // ── Instruction fetch (combinational) ───────────────────────────────────────
  val inst   = imem(pc >> 2)

  // ── Decode ──────────────────────────────────────────────────────────────────
  val opcode = inst(6, 0)
  val rd     = inst(11, 7)
  val funct3 = inst(14, 12)
  val rs1Idx = inst(19, 15)
  val rs2Idx = inst(24, 20)
  val funct7 = inst(31, 25)
  val rs1Val = Mux(rs1Idx === 0.U, 0.U(cfg.xlen.W), regs(rs1Idx))
  val rs2Val = Mux(rs2Idx === 0.U, 0.U(cfg.xlen.W), regs(rs2Idx))

  // ── Immediate generation ─────────────────────────────────────────────────────
  // I-type: sign-extend inst[31:20]
  val immI = Cat(Fill(20, inst(31)), inst(31, 20))
  // S-type: sign-extend {inst[31:25], inst[11:7]}
  val immS = Cat(Fill(20, inst(31)), inst(31, 25), inst(11, 7))
  // B-type: sign-extend {inst[31],inst[7],inst[30:25],inst[11:8], 0}
  val immB = Cat(Fill(19, inst(31)), inst(31), inst(7), inst(30, 25), inst(11, 8), 0.U(1.W))
  // U-type: inst[31:12] << 12
  val immU = Cat(inst(31, 12), 0.U(12.W))
  // J-type: sign-extend {inst[31],inst[19:12],inst[20],inst[30:21], 0}
  val immJ = Cat(Fill(11, inst(31)), inst(31), inst(19, 12), inst(20), inst(30, 21), 0.U(1.W))

  // ── ALU ─────────────────────────────────────────────────────────────────────
  // For register-immediate ops B is the sign-extended immediate; for R-type B is rs2
  val useImm = (opcode === Opcode.OP_IMM) || (opcode === Opcode.JALR) || (opcode === Opcode.LOAD)
  val aluA   = rs1Val
  val aluB   = Mux(useImm, immI, rs2Val)
  val shamt  = aluB(4, 0)

  val aluResult = Wire(UInt(cfg.xlen.W))
  aluResult := 0.U
  switch(funct3) {
    is("b000".U) {
      // ADD / SUB (SUB only for OP with funct7[5]=1)
      aluResult := Mux(funct7(5) && (opcode === Opcode.OP), aluA - aluB, aluA + aluB)
    }
    is("b001".U) { aluResult := aluA << shamt }
    is("b010".U) { aluResult := (aluA.asSInt < aluB.asSInt).asUInt }
    is("b011".U) { aluResult := (aluA < aluB).asUInt }
    is("b100".U) { aluResult := aluA ^ aluB }
    is("b101".U) {
      // SRL / SRA
      aluResult := Mux(funct7(5), (aluA.asSInt >> shamt).asUInt, aluA >> shamt)
    }
    is("b110".U) { aluResult := aluA | aluB }
    is("b111".U) { aluResult := aluA & aluB }
  }

  // ── Branch condition ─────────────────────────────────────────────────────────
  val brTaken = Wire(Bool())
  brTaken := false.B
  switch(funct3) {
    is("b000".U) { brTaken := rs1Val === rs2Val }            // BEQ
    is("b001".U) { brTaken := rs1Val =/= rs2Val }           // BNE
    is("b100".U) { brTaken := rs1Val.asSInt < rs2Val.asSInt }   // BLT
    is("b101".U) { brTaken := rs1Val.asSInt >= rs2Val.asSInt }  // BGE
    is("b110".U) { brTaken := rs1Val < rs2Val }             // BLTU
    is("b111".U) { brTaken := rs1Val >= rs2Val }            // BGEU
  }

  // ── Load ─────────────────────────────────────────────────────────────────────
  val ldAddr    = rs1Val + immI
  val ldWord    = dmem(ldAddr >> 2)
  val ldByte    = (ldWord >> Cat(ldAddr(1, 0), 0.U(3.W)))(7, 0)
  val ldHalf    = (ldWord >> Cat(ldAddr(1),   0.U(4.W)))(15, 0)

  val loadData = Wire(UInt(cfg.xlen.W))
  loadData := 0.U
  switch(funct3) {
    is("b000".U) { loadData := Cat(Fill(24, ldByte(7)), ldByte) }   // LB
    is("b001".U) { loadData := Cat(Fill(16, ldHalf(15)), ldHalf) }  // LH
    is("b010".U) { loadData := ldWord }                              // LW
    is("b100".U) { loadData := Cat(0.U(24.W), ldByte) }            // LBU
    is("b101".U) { loadData := Cat(0.U(16.W), ldHalf) }            // LHU
  }

  // ── Tile communication decode ────────────────────────────────────────────────
  // funct7[0]=0 → TILE_RECV rd, dir   (rd  ← neighbor output register)
  // funct7[0]=1 → TILE_SEND dir, rs1  (out_reg[dir] ← rs1)
  val tileDir  = funct3(1, 0)        // 2-bit direction selector
  val isTxSend = funct7(0)           // 1=SEND, 0=RECV

  // ── Execute + write-back ─────────────────────────────────────────────────────
  val nextPc  = Wire(UInt(cfg.xlen.W))
  val rdWen   = Wire(Bool())
  val rdWdata = Wire(UInt(cfg.xlen.W))

  nextPc  := pc + 4.U
  rdWen   := false.B
  rdWdata := 0.U

  when(!haltReg) {
    switch(opcode) {

      is(Opcode.LUI) {
        rdWen   := true.B
        rdWdata := immU
      }

      is(Opcode.AUIPC) {
        rdWen   := true.B
        rdWdata := pc + immU
      }

      is(Opcode.JAL) {
        rdWen   := true.B
        rdWdata := pc + 4.U
        nextPc  := pc + immJ         // two's complement addition handles sign
      }

      is(Opcode.JALR) {
        rdWen   := true.B
        rdWdata := pc + 4.U
        nextPc  := Cat((rs1Val + immI)(cfg.xlen - 1, 1), 0.U(1.W))  // clear bit 0
      }

      is(Opcode.BRANCH) {
        nextPc := Mux(brTaken, pc + immB, pc + 4.U)
      }

      is(Opcode.LOAD) {
        rdWen   := true.B
        rdWdata := loadData
      }

      is(Opcode.STORE) {
        // Simplified: word-granular write only.
        // Full byte/half support can be added with byte-enable masking.
        val stAddr = rs1Val + immS
        dmem.write(stAddr >> 2, rs2Val)
      }

      is(Opcode.OP_IMM, Opcode.OP) {
        rdWen   := true.B
        rdWdata := aluResult
      }

      is(Opcode.SYSTEM) {
        // ECALL (funct12=0x000) and EBREAK (funct12=0x001) both halt the core
        haltReg := true.B
      }

      // ── Tile communication instructions ─────────────────────────────────────
      is(Opcode.CUSTOM0) {
        when(isTxSend) {
          // TILE_SEND dir, rs1
          // → write rs1 into this core's directional output register
          dirData(tileDir)  := rs1Val
          dirValid(tileDir) := true.B
        }.otherwise {
          // TILE_RECV rd, dir
          // → read the neighbor's directional output register into rd
          rdWen   := true.B
          rdWdata := io.in(tileDir).data
        }
      }
    }

    // All-zeros instruction (reset vector not initialised) → treat as halt
    when(inst === 0.U) { haltReg := true.B }

    // Register file write (x0 is always 0)
    when(rdWen && rd =/= 0.U) {
      regs(rd) := rdWdata
    }
    pc := nextPc
  }

  io.halt   := haltReg
  io.dbgPc  := pc
  io.dbgReg := regs
}

// ─────────────────────────────────────────────────────────────────────────────
//  Tile Array  ─  NxM mesh of TileCores
// ─────────────────────────────────────────────────────────────────────────────

class TileArray(cfg: TileConfig) extends Module {
  val io = IO(new Bundle {
    val halt  = Output(Vec(cfg.rows, Vec(cfg.cols, Bool())))
    val dbgPc = Output(Vec(cfg.rows, Vec(cfg.cols, UInt(cfg.xlen.W))))
  })

  // ── Instantiate all cores ───────────────────────────────────────────────────
  val cores: Seq[Seq[TileCore]] =
    Seq.tabulate(cfg.rows, cfg.cols)((_, _) => Module(new TileCore(cfg)))

  // ── Wire the mesh ───────────────────────────────────────────────────────────
  for (r <- 0 until cfg.rows; c <- 0 until cfg.cols) {
    val core = cores(r)(c)
    io.halt(r)(c)  := core.io.halt
    io.dbgPc(r)(c) := core.io.dbgPc

    // Helper: connect an input direction or tie it to zero if at the boundary.
    def wire(dstDir: Int, src: Option[TileCore], srcDir: Int): Unit =
      src match {
        case Some(n) => core.io.in(dstDir) := n.io.out(srcDir)
        case None    =>
          core.io.in(dstDir).data  := 0.U
          core.io.in(dstDir).valid := false.B
      }

    // core[r][c].in[N] ← core[r-1][c].out[S]   (neighbor above sends South)
    wire(Dir.N, if (r > 0)            Some(cores(r - 1)(c)) else None, Dir.S)
    // core[r][c].in[S] ← core[r+1][c].out[N]   (neighbor below sends North)
    wire(Dir.S, if (r < cfg.rows - 1) Some(cores(r + 1)(c)) else None, Dir.N)
    // core[r][c].in[E] ← core[r][c+1].out[W]   (neighbor right sends West)
    wire(Dir.E, if (c < cfg.cols - 1) Some(cores(r)(c + 1)) else None, Dir.W)
    // core[r][c].in[W] ← core[r][c-1].out[E]   (neighbor left sends East)
    wire(Dir.W, if (c > 0)            Some(cores(r)(c - 1)) else None, Dir.E)
  }
}

// ─────────────────────────────────────────────────────────────────────────────
//  Verilog emission entry point
// ─────────────────────────────────────────────────────────────────────────────

object TileArrayMain extends App {
  val cfg = TileConfig(rows = 4, cols = 4, xlen = 32)
  (new circt.stage.ChiselStage).emitSystemVerilog(
    new TileArray(cfg),
    firtoolOpts = Array("-o", "generated/TileArray.sv")
  )
}
