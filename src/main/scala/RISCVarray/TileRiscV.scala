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
//  RV32M 命令 funct3 定数
// ─────────────────────────────────────────────────────────────────────────────
object Funct3M {
  val MUL    = "b000".U(3.W)   // rd = (rs1 * rs2)[31:0]          符号付き×符号付き下位
  val MULH   = "b001".U(3.W)   // rd = (rs1 * rs2)[63:32]         符号付き×符号付き上位
  val MULHSU = "b010".U(3.W)   // rd = (rs1 * rs2)[63:32]         符号付き×符号なし上位
  val MULHU  = "b011".U(3.W)   // rd = (rs1 * rs2)[63:32]         符号なし×符号なし上位
  val DIV    = "b100".U(3.W)   // rd = rs1 / rs2                  符号付き除算
  val DIVU   = "b101".U(3.W)   // rd = rs1 / rs2                  符号なし除算
  val REM    = "b110".U(3.W)   // rd = rs1 % rs2                  符号付き剰余
  val REMU   = "b111".U(3.W)   // rd = rs1 % rs2                  符号なし剰余
}
 
// ─────────────────────────────────────────────────────────────────────────────
//  M-extention oALU
// ─────────────────────────────────────────────────────────────────────────────
class MExtensionALU(xlen: Int = 32) extends Module {
  val io = IO(new Bundle {
    val funct3 = Input(UInt(3.W))
    val rs1    = Input(UInt(xlen.W))
    val rs2    = Input(UInt(xlen.W))
    val result = Output(UInt(xlen.W))
  })
  // UInt(32) * UInt(32) → UInt(64)
  val mulSS  = (io.rs1.asSInt * io.rs2.asSInt).asUInt  // signed × signed  64bit
  val mulSU  = (io.rs1.asSInt * io.rs2.asUInt).asUInt  // signed × unsigned 64bit  ※Chisel では asSInt * asUInt → SInt(65)
  val mulUU  = (io.rs1        * io.rs2)                // unsigned × unsigned 64bit
 
  // RV32M 仕様: 除算器の例外処理
  //   DIV/REM:  rs2==0 → DIV=-1, REM=rs1
  //   DIV:      rs1==-2^31 かつ rs2==-1 → オーバーフロー → DIV=-2^31, REM=0
  val rs1s   = io.rs1.asSInt
  val rs2s   = io.rs2.asSInt
  val divByZ = io.rs2 === 0.U
 
  // signed
  val overFlow  = (io.rs1 === "h80000000".U) && (io.rs2 === "hFFFFFFFF".U)
  val divS_raw  = (rs1s / rs2s).asUInt
  val remS_raw  = (rs1s % rs2s).asUInt
  val divS = MuxCase(divS_raw, Seq(
    divByZ  -> "hFFFFFFFF".U,        // -1
    overFlow-> "h80000000".U         // -2^31
  ))
  val remS = MuxCase(remS_raw, Seq(
    divByZ  -> io.rs1,
    overFlow-> 0.U
  ))

  // unsigned
  val divU = Mux(divByZ, "hFFFFFFFF".U, io.rs1 / io.rs2)
  val remU = Mux(divByZ, io.rs1,         io.rs1 % io.rs2)
 
  io.result := MuxCase(0.U, Seq(
    (io.funct3 === Funct3M.MUL)    -> mulSS(xlen - 1, 0),
    (io.funct3 === Funct3M.MULH)   -> mulSS(2 * xlen - 1, xlen),
    (io.funct3 === Funct3M.MULHSU) -> mulSU(2 * xlen - 1, xlen),
    (io.funct3 === Funct3M.MULHU)  -> mulUU(2 * xlen - 1, xlen),
    (io.funct3 === Funct3M.DIV)    -> divS,
    (io.funct3 === Funct3M.DIVU)   -> divU,
    (io.funct3 === Funct3M.REM)    -> remS,
    (io.funct3 === Funct3M.REMU)   -> remU
  ))
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
  val immI = Cat(Fill(20, inst(31)), inst(31, 20))  // I-type: sign-extend inst[31:20]
  val immS = Cat(Fill(20, inst(31)), inst(31, 25), inst(11, 7))// S-type: sign-extend {inst[31:25], inst[11:7]}
  val immB = Cat(Fill(19, inst(31)), inst(31), inst(7), inst(30, 25), inst(11, 8), 0.U(1.W))// B-type: sign-extend {inst[31],inst[7],inst[30:25],inst[11:8], 0}
  val immU = Cat(inst(31, 12), 0.U(12.W))  // U-type: inst[31:12] << 12
  val immJ = Cat(Fill(11, inst(31)), inst(31), inst(19, 12), inst(20), inst(30, 21), 0.U(1.W))// J-type: sign-extend {inst[31],inst[19:12],inst[20],inst[30:21], 0}

  // ── ALU ─────────────────────────────────────────────────────────────────────
  // For register-immediate ops B is the sign-extended immediate; for R-type B is rs2
  val useImm = (opcode === Opcode.OP_IMM) || (opcode === Opcode.JALR) || (opcode === Opcode.LOAD)
  val aluA   = rs1Val
  val aluB   = Mux(useImm, immI, rs2Val)
  val shamt  = aluB(4, 0)

  val aluResult = Wire(UInt(cfg.xlen.W))
  aluResult := 0.U
  switch(funct3) {
    is("b000".U) {aluResult := Mux(funct7(5) && (opcode === Opcode.OP), aluA - aluB, aluA + aluB)}
    is("b001".U) { aluResult := aluA << shamt }
    is("b010".U) { aluResult := (aluA.asSInt < aluB.asSInt).asUInt }
    is("b011".U) { aluResult := (aluA < aluB).asUInt }
    is("b100".U) { aluResult := aluA ^ aluB }
    is("b101".U) {aluResult := Mux(funct7(5), (aluA.asSInt >> shamt).asUInt, aluA >> shamt)}      // SRL / SRA
    is("b110".U) { aluResult := aluA | aluB }
    is("b111".U) { aluResult := aluA & aluB }
  }
  // ── M extention ALU ──────────────────────────────────────────────────────────
  val mAlu   = Module(new MExtensionALU(cfg.xlen))
  mAlu.io.funct3 := funct3
  mAlu.io.rs1    := rs1Val
  mAlu.io.rs2    := rs2Val
  val isMExt = funct7 === "b0000001".U
 
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
      is(Opcode.LUI)   { rdWen := true.B; rdWdata := immU }
      is(Opcode.AUIPC) { rdWen := true.B; rdWdata := pc + immU }
      is(Opcode.JAL)   { rdWen := true.B; rdWdata := pc + 4.U; nextPc := pc + immJ }
      is(Opcode.JALR)  { rdWen := true.B; rdWdata := pc + 4.U
                         nextPc := Cat((rs1Val + immI)(cfg.xlen - 1, 1), 0.U(1.W)) }
      is(Opcode.BRANCH){ nextPc := Mux(brTaken, pc + immB, pc + 4.U) }
      is(Opcode.LOAD)  { rdWen := true.B; rdWdata := loadData }
      is(Opcode.STORE) { dmem.write((rs1Val + immS) >> 2, rs2Val) }
      is(Opcode.OP_IMM){ rdWen := true.B; rdWdata := aluResult }
 
      // ── OP: RV32I (funct7≠0000001) または RV32M (funct7==0000001) ───────
      is(Opcode.OP) {
        rdWen   := true.B
        rdWdata := Mux(isMExt, mAlu.io.result, aluResult)       
      }
 
      is(Opcode.SYSTEM) { haltReg := true.B }
      // ── Tile communication instructions ─────────────────────────────────────
      is(Opcode.CUSTOM0) {
        when(isTxSend) {
          // TILE_SEND dir, rs1 → write rs1 into this core's directional output register
          dirData(tileDir)  := rs1Val
          dirValid(tileDir) := true.B
        }.otherwise {
          // TILE_RECV rd, dir → read the neighbor's directional output register into rd
          rdWen   := true.B
          rdWdata := io.in(tileDir).data
        }
      }
    }
    when(inst === 0.U) { haltReg := true.B }// All-zeros instruction (reset vector not initialised) → treat as halt
    when(rdWen && rd =/= 0.U) { regs(rd) := rdWdata }// Register file write (x0 is always 0)
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

  val cores: Seq[Seq[TileCore]] = Seq.tabulate(cfg.rows, cfg.cols)((_, _) => Module(new TileCore(cfg)))

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
  (new circt.stage.ChiselStage).emitSystemVerilog( new TileArray(cfg),firtoolOpts = Array("-o", "generated/TileArray.sv")  )
}
