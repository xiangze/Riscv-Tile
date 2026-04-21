// =============================================================================
//  src/main/scala/tileriscv/TileRiscVSim.scala
//
//  アーキテクチャ概要
//  ─────────────────────────────────────────────────────────────────────────────
//
//  ┌─────────────────────────────────────────────────┐
//  │  外部 IMEM（共有・単一）                          │
//  │  SyncReadMem[iMemWords x 32bit]                  │
//  └────────────────────┬────────────────────────────┘
//                       │ inst (32bit)
//                       ▼
//  ┌─────────────────────────────────────────────────┐
//  │  SharedDecoder（単一）                           │
//  │  フェッチ・デコード・PC管理・分岐判定             │
//  │  制御信号を全タイルに broadcast                  │
//  └──┬──────────────────────────────────────────────┘
//     │ DecodeBundle (broadcast)
//     ├──────────────────┬──────────────────┐ ...
//     ▼                  ▼                  ▼
//  ┌────────┐        ┌────────┐        ┌────────┐
//  │ Tile   │        │ Tile   │        │ Tile   │
//  │ [0][0] │        │ [0][1] │        │ [1][0] │
//  │        │        │        │        │        │
//  │ RegFile│        │ RegFile│        │ RegFile│  ← タイルごとに独立
//  │ ALU    │        │ ALU    │        │ ALU    │
//  └───┬────┘        └───┬────┘        └───┬────┘
//      │ ld/st req       │ ld/st req       │
//      ▼                 ▼                 ▼
//  ┌────────┐        ┌────────┐        ┌────────┐
//  │ DMEM   │        │ DMEM   │        │ DMEM   │  ← タイルごとに独立バンク
//  │ bank 0 │        │ bank 1 │        │ bank 2 │  （外部インスタンス）
//  └────────┘        └────────┘        └────────┘
//
//  設計方針:
//  - IMEM・DMEM はアレイ外部でインスタンス化し IO ポート経由でアクセス
//  - Decoder は単一。出力 DecodeBundle を全タイルに broadcast
//  - タイル間通信（TILE_SEND/TILE_RECV）は従来どおり方向別レジスタで実現
//  - ECALL で halt。gp==1 なら PASS
// =============================================================================

package tileriscv

import chisel3._
import chisel3.util._
import chisel3.util.experimental.loadMemoryFromFileInline

// ─────────────────────────────────────────────────────────────────────────────
//  設定
// ─────────────────────────────────────────────────────────────────────────────

case class SimConfig(
  rows:       Int = 4,
  cols:       Int = 4,
  xlen:       Int = 32,
  iMemWords:  Int = 16384,  // 命令メモリ語数（64KB）
  dMemWords:  Int = 4096,   // データメモリ語数（タイルごと、16KB）
  tohostAddr: Int = 0x1000  // PASS/FAIL 判定アドレス
)

// ─────────────────────────────────────────────────────────────────────────────
//  定数
// ─────────────────────────────────────────────────────────────────────────────

object SimDir { val N = 0; val S = 1; val E = 2; val W = 3 }

object SimOp {
  val LUI      = "b0110111".U(7.W)
  val AUIPC    = "b0010111".U(7.W)
  val JAL      = "b1101111".U(7.W)
  val JALR     = "b1100111".U(7.W)
  val BRANCH   = "b1100011".U(7.W)
  val LOAD     = "b0000011".U(7.W)
  val STORE    = "b0100011".U(7.W)
  val OP_IMM   = "b0010011".U(7.W)
  val OP       = "b0110011".U(7.W)
  val MISC_MEM = "b0001111".U(7.W)
  val SYSTEM   = "b1110011".U(7.W)
  val CUSTOM0  = "b0001011".U(7.W)
}

// ─────────────────────────────────────────────────────────────────────────────
//  タイル間通信ポート
// ─────────────────────────────────────────────────────────────────────────────

class DirPort(xlen: Int) extends Bundle {
  val valid = Bool()
  val data  = UInt(xlen.W)
}

// ─────────────────────────────────────────────────────────────────────────────
//  Decoder が全タイルに broadcast する制御バンドル
// ─────────────────────────────────────────────────────────────────────────────

class DecodeBundle(xlen: Int) extends Bundle {
  // ── 命令フィールド ──────────────────────────────────────────────────────────
  val inst    = UInt(xlen.W)
  val pc      = UInt(xlen.W)
  val opcode  = UInt(7.W)
  val rd      = UInt(5.W)
  val funct3  = UInt(3.W)
  val rs1Idx  = UInt(5.W)
  val rs2Idx  = UInt(5.W)
  val funct7  = UInt(7.W)
  val funct12 = UInt(12.W)
  // ── イミディエイト ──────────────────────────────────────────────────────────
  val immI    = UInt(xlen.W)
  val immS    = UInt(xlen.W)
  val immB    = UInt(xlen.W)
  val immU    = UInt(xlen.W)
  val immJ    = UInt(xlen.W)
  // ── デコード済みフラグ ──────────────────────────────────────────────────────
  val isMExt  = Bool()   // RV32M 命令（funct7==0000001）
  val isEcall = Bool()
  val isCSR   = Bool()
  val valid   = Bool()   // このサイクルの命令が有効か（halt 中は false）
}

// ─────────────────────────────────────────────────────────────────────────────
//  外部命令メモリ IO
// ─────────────────────────────────────────────────────────────────────────────

class IMemIO(xlen: Int, words: Int) extends Bundle {
  val addr = Input(UInt(log2Ceil(words).W))
  val data = Output(UInt(xlen.W))
}

// ─────────────────────────────────────────────────────────────────────────────
//  外部データメモリ IO（タイルごと）
// ─────────────────────────────────────────────────────────────────────────────

class DMemIO(xlen: Int) extends Bundle {
  val addr  = Input(UInt(xlen.W))    // バイトアドレス
  val wdata = Input(UInt(xlen.W))
  val wen   = Input(Bool())
  val rdata = Output(UInt(xlen.W))
}

// =============================================================================
//  外部命令メモリ（共有・単一）
// =============================================================================

class SharedIMem(cfg: SimConfig, hexFile: String = "") extends Module {
  val io = IO(new IMemIO(cfg.xlen, cfg.iMemWords))

  val mem = SyncReadMem(cfg.iMemWords, UInt(cfg.xlen.W))
  if (hexFile.nonEmpty) loadMemoryFromFileInline(mem, hexFile)

  io.data := mem.read(io.addr)
}

// =============================================================================
//  外部データメモリ（タイルごとに独立バンク）
// =============================================================================

class TileDMem(cfg: SimConfig) extends Module {
  val io = IO(new DMemIO(cfg.xlen))

  val mem = SyncReadMem(cfg.dMemWords, UInt(cfg.xlen.W))

  val wordAddr = io.addr >> 2
  when(io.wen) { mem.write(wordAddr, io.wdata) }
  io.rdata := mem.read(wordAddr)
}

// =============================================================================
//  SharedDecoder
//  ─────────────────────────────────────────────────────────────────────────────
//  単一の PC・フェッチ・デコードユニット。
//  すべてのタイルに同じ DecodeBundle を broadcast する。
//
//  分岐・ジャンプの解決:
//    タイル [0][0] の実行結果（brTaken, aluResult）を受け取って次の PC を決める。
//    他のタイルは同じ命令を同じオペランドで実行するため、
//    タイル [0][0] の結果を代表として使う。
// =============================================================================

class SharedDecoderIO(cfg: SimConfig) extends Bundle {
  // 命令メモリインタフェース
  val imem    = Flipped(new IMemIO(cfg.xlen, cfg.iMemWords))

  // タイル [0][0] からの分岐フィードバック
  val brTaken = Input(Bool())
  val aluOut  = Input(UInt(cfg.xlen.W))   // JALR のターゲット計算に使用

  // 全タイルへの broadcast
  val decode  = Output(new DecodeBundle(cfg.xlen))

  // halt 制御
  val haltIn  = Input(Bool())    // タイル [0][0] が halt したら止まる
}

class SharedDecoder(cfg: SimConfig) extends Module {
  val io = IO(new SharedDecoderIO(cfg))

  val pc      = RegInit(0.U(cfg.xlen.W))
  val haltReg = RegInit(false.B)

  // ── フェッチ ────────────────────────────────────────────────────────────────
  io.imem.addr := pc >> 2
  val inst = io.imem.data

  // ── デコード ────────────────────────────────────────────────────────────────
  val opcode  = inst(6, 0)
  val rd      = inst(11, 7)
  val funct3  = inst(14, 12)
  val rs1Idx  = inst(19, 15)
  val rs2Idx  = inst(24, 20)
  val funct7  = inst(31, 25)
  val funct12 = inst(31, 20)

  val immI = Cat(Fill(20, inst(31)), inst(31, 20))
  val immS = Cat(Fill(20, inst(31)), inst(31, 25), inst(11, 7))
  val immB = Cat(Fill(19, inst(31)), inst(31), inst(7), inst(30, 25), inst(11, 8), 0.U(1.W))
  val immU = Cat(inst(31, 12), 0.U(12.W))
  val immJ = Cat(Fill(11, inst(31)), inst(31), inst(19, 12), inst(20), inst(30, 21), 0.U(1.W))

  // ── 次 PC 計算 ───────────────────────────────────────────────────────────────
  val nextPc = Wire(UInt(cfg.xlen.W))
  nextPc := pc + 4.U

  when(!haltReg) {
    switch(opcode) {
      is(SimOp.JAL)    { nextPc := pc + immJ }
      is(SimOp.JALR)   { nextPc := Cat((io.aluOut + immI)(cfg.xlen - 1, 1), 0.U(1.W)) }
      is(SimOp.BRANCH) { nextPc := Mux(io.brTaken, pc + immB, pc + 4.U) }
    }
    when(io.haltIn) { haltReg := true.B }
    pc := nextPc
  }

  // ── broadcast 出力 ──────────────────────────────────────────────────────────
  io.decode.inst    := inst
  io.decode.pc      := pc
  io.decode.opcode  := opcode
  io.decode.rd      := rd
  io.decode.funct3  := funct3
  io.decode.rs1Idx  := rs1Idx
  io.decode.rs2Idx  := rs2Idx
  io.decode.funct7  := funct7
  io.decode.funct12 := funct12
  io.decode.immI    := immI
  io.decode.immS    := immS
  io.decode.immB    := immB
  io.decode.immU    := immU
  io.decode.immJ    := immJ
  io.decode.isMExt  := (funct7 === "b0000001".U)
  io.decode.isEcall := (funct3 === 0.U) && (funct12 === 0.U) && (opcode === SimOp.SYSTEM)
  io.decode.isCSR   := (funct3 =/= 0.U) && (opcode === SimOp.SYSTEM)
  io.decode.valid   := !haltReg
}

// =============================================================================
//  TileExecutionUnit
//  ─────────────────────────────────────────────────────────────────────────────
//  タイルごとの実行ユニット。
//  SharedDecoder から broadcast された DecodeBundle を受け取り、
//  独自のレジスタファイルで実行する。
//  データメモリは外部の TileDMem に IO でアクセスする。
// =============================================================================

class TileExecIO(cfg: SimConfig) extends Bundle {
  // Decoder からの broadcast
  val dec     = Input(new DecodeBundle(cfg.xlen))

  // 外部データメモリ
  val dmem    = Flipped(new DMemIO(cfg.xlen))

  // タイル間通信
  val tileOut = Output(Vec(4, new DirPort(cfg.xlen)))
  val tileIn  = Input(Vec(4, new DirPort(cfg.xlen)))

  // 分岐フィードバック（代表タイル [0][0] のみ Decoder が使用）
  val brTaken = Output(Bool())
  val aluOut  = Output(UInt(cfg.xlen.W))

  // 観測ポート
  val halt    = Output(Bool())
  val pass    = Output(Bool())
  val dbgReg  = Output(Vec(32, UInt(cfg.xlen.W)))
}

class TileExecutionUnit(cfg: SimConfig) extends Module {
  val io = IO(new TileExecIO(cfg))

  // ── レジスタファイル（このタイル専有） ────────────────────────────────────
  val regs    = RegInit(VecInit(Seq.fill(32)(0.U(cfg.xlen.W))))
  val haltReg = RegInit(false.B)
  val passReg = RegInit(false.B)

  // ── タイル間通信出力レジスタ ────────────────────────────────────────────────
  val dirData  = RegInit(VecInit(Seq.fill(4)(0.U(cfg.xlen.W))))
  val dirValid = RegInit(VecInit(Seq.fill(4)(false.B)))
  for (d <- 0 until 4) {
    io.tileOut(d).data  := dirData(d)
    io.tileOut(d).valid := dirValid(d)
  }

  // ── デコードバンドルを展開 ───────────────────────────────────────────────────
  val dec     = io.dec
  val rs1Val  = Mux(dec.rs1Idx === 0.U, 0.U, regs(dec.rs1Idx))
  val rs2Val  = Mux(dec.rs2Idx === 0.U, 0.U, regs(dec.rs2Idx))

  // ── 基本 ALU ────────────────────────────────────────────────────────────────
  val useImm  = (dec.opcode === SimOp.OP_IMM) || (dec.opcode === SimOp.JALR) ||
                (dec.opcode === SimOp.LOAD)
  val aluA    = rs1Val
  val aluB    = Mux(useImm, dec.immI, rs2Val)
  val shamt   = aluB(4, 0)

  val baseResult = Wire(UInt(cfg.xlen.W))
  baseResult := 0.U
  switch(dec.funct3) {
    is("b000".U) {
      baseResult := Mux(dec.funct7(5) && dec.opcode === SimOp.OP,
                        aluA - aluB, aluA + aluB)
    }
    is("b001".U) { baseResult := aluA << shamt }
    is("b010".U) { baseResult := (aluA.asSInt < aluB.asSInt).asUInt }
    is("b011".U) { baseResult := (aluA < aluB).asUInt }
    is("b100".U) { baseResult := aluA ^ aluB }
    is("b101".U) {
      baseResult := Mux(dec.funct7(5),
                        (aluA.asSInt >> shamt).asUInt,
                        aluA >> shamt)
    }
    is("b110".U) { baseResult := aluA | aluB }
    is("b111".U) { baseResult := aluA & aluB }
  }

  // ── RV32M ───────────────────────────────────────────────────────────────────
  val mulSS   = (rs1Val.asSInt * rs2Val.asSInt).asUInt
  val mulUU   = rs1Val * rs2Val
  val mulSU   = (rs1Val.asSInt * rs2Val.asUInt).asUInt
  val divByZ  = rs2Val === 0.U
  val overFlow = (rs1Val === "h80000000".U) && (rs2Val === "hFFFFFFFF".U)
  val divS    = MuxCase(((rs1Val.asSInt / rs2Val.asSInt)).asUInt,
                  Seq(divByZ -> "hFFFFFFFF".U, overFlow -> "h80000000".U))
  val remS    = MuxCase(((rs1Val.asSInt % rs2Val.asSInt)).asUInt,
                  Seq(divByZ -> rs1Val, overFlow -> 0.U))
  val divU    = Mux(divByZ, "hFFFFFFFF".U, rs1Val / rs2Val)
  val remU    = Mux(divByZ, rs1Val, rs1Val % rs2Val)

  val mResult = Wire(UInt(cfg.xlen.W))
  mResult := 0.U
  switch(dec.funct3) {
    is("b000".U) { mResult := mulSS(31, 0) }
    is("b001".U) { mResult := mulSS(63, 32) }
    is("b010".U) { mResult := mulSU(63, 32) }
    is("b011".U) { mResult := mulUU(63, 32) }
    is("b100".U) { mResult := divS }
    is("b101".U) { mResult := divU }
    is("b110".U) { mResult := remS }
    is("b111".U) { mResult := remU }
  }

  val aluResult = Mux(dec.isMExt && dec.opcode === SimOp.OP, mResult, baseResult)

  // ── 分岐条件 ────────────────────────────────────────────────────────────────
  val brTaken = Wire(Bool())
  brTaken := false.B
  switch(dec.funct3) {
    is("b000".U) { brTaken := rs1Val === rs2Val }
    is("b001".U) { brTaken := rs1Val =/= rs2Val }
    is("b100".U) { brTaken := rs1Val.asSInt < rs2Val.asSInt }
    is("b101".U) { brTaken := rs1Val.asSInt >= rs2Val.asSInt }
    is("b110".U) { brTaken := rs1Val < rs2Val }
    is("b111".U) { brTaken := rs1Val >= rs2Val }
  }
  io.brTaken := brTaken
  io.aluOut  := aluResult

  // ── データメモリ要求 ────────────────────────────────────────────────────────
  val ldAddr = rs1Val + dec.immI
  val stAddr = rs1Val + dec.immS

  io.dmem.addr  := Mux(dec.opcode === SimOp.STORE, stAddr, ldAddr)
  io.dmem.wdata := rs2Val
  io.dmem.wen   := dec.valid && !haltReg && (dec.opcode === SimOp.STORE)

  // ロード結果成形（funct3 に応じて符号拡張）
  val ldWord = io.dmem.rdata
  val ldByte = (ldWord >> Cat(ldAddr(1, 0), 0.U(3.W)))(7, 0)
  val ldHalf = (ldWord >> Cat(ldAddr(1), 0.U(4.W)))(15, 0)
  val loadData = Wire(UInt(cfg.xlen.W))
  loadData := 0.U
  switch(dec.funct3) {
    is("b000".U) { loadData := Cat(Fill(24, ldByte(7)), ldByte) }
    is("b001".U) { loadData := Cat(Fill(16, ldHalf(15)), ldHalf) }
    is("b010".U) { loadData := ldWord }
    is("b100".U) { loadData := Cat(0.U(24.W), ldByte) }
    is("b101".U) { loadData := Cat(0.U(16.W), ldHalf) }
  }

  // ── タイル通信デコード ──────────────────────────────────────────────────────
  val tileDir  = dec.funct3(1, 0)
  val isTxSend = dec.funct7(0)

  // ── ライトバック ────────────────────────────────────────────────────────────
  val rdWen   = Wire(Bool())
  val rdWdata = Wire(UInt(cfg.xlen.W))
  rdWen   := false.B
  rdWdata := 0.U

  when(dec.valid && !haltReg) {
    switch(dec.opcode) {
      is(SimOp.LUI)    { rdWen := true.B; rdWdata := dec.immU }
      is(SimOp.AUIPC)  { rdWen := true.B; rdWdata := dec.pc + dec.immU }
      is(SimOp.JAL)    { rdWen := true.B; rdWdata := dec.pc + 4.U }
      is(SimOp.JALR)   { rdWen := true.B; rdWdata := dec.pc + 4.U }
      is(SimOp.LOAD)   { rdWen := true.B; rdWdata := loadData }
      is(SimOp.OP_IMM, SimOp.OP) {
        rdWen   := true.B
        rdWdata := aluResult
      }
      is(SimOp.STORE) {
        // tohost への書き込みで halt 判定
        when(stAddr === cfg.tohostAddr.U) {
          haltReg := true.B
          passReg := (rs2Val === 1.U)
        }
      }
      is(SimOp.MISC_MEM) { /* FENCE: NOP */ }
      is(SimOp.SYSTEM) {
        when(dec.isEcall) {
          haltReg := true.B
          passReg := (regs(3) === 1.U)   // x3 = gp
        }.elsewhen(dec.isCSR) {
          // CSR: mhartid → 0, その他 → 0（no-op）
          rdWen   := true.B
          rdWdata := 0.U
        }
      }
      is(SimOp.CUSTOM0) {
        when(isTxSend) {
          dirData(tileDir)  := rs1Val
          dirValid(tileDir) := true.B
        }.otherwise {
          rdWen   := true.B
          rdWdata := io.tileIn(tileDir).data
        }
      }
    }

    when(dec.inst === 0.U) { haltReg := true.B }

    when(rdWen && dec.rd =/= 0.U) { regs(dec.rd) := rdWdata }
  }

  io.halt    := haltReg
  io.pass    := passReg
  io.dbgReg  := regs
}

// =============================================================================
//  SimTileArray  ─  トップレベル
//  ─────────────────────────────────────────────────────────────────────────────
//  ・SharedIMem: 外部命令メモリ（単一）
//  ・SharedDecoder: 単一フェッチ/デコードユニット
//  ・TileExecutionUnit × (rows × cols): 各タイルの実行ユニット
//  ・TileDMem × (rows × cols): 各タイルの外部データメモリ
// =============================================================================

class SimTileArray(cfg: SimConfig, iHexFile: String = "") extends Module {
  val io = IO(new Bundle {
    val halt    = Output(Vec(cfg.rows, Vec(cfg.cols, Bool())))
    val pass    = Output(Vec(cfg.rows, Vec(cfg.cols, Bool())))
    val allDone = Output(Bool())
    val allPass = Output(Bool())
    val dbgPc   = Output(UInt(cfg.xlen.W))
  })

  // ── 外部命令メモリ（共有・単一） ────────────────────────────────────────────
  val imem = Module(new SharedIMem(cfg, iHexFile))

  // ── タイル実行ユニット ──────────────────────────────────────────────────────
  val tiles: Seq[Seq[TileExecutionUnit]] =
    Seq.tabulate(cfg.rows, cfg.cols)((_, _) => Module(new TileExecutionUnit(cfg)))

  // ── 外部データメモリ（タイルごとに独立） ──────────────────────────────────
  val dmems: Seq[Seq[TileDMem]] =
    Seq.tabulate(cfg.rows, cfg.cols)((_, _) => Module(new TileDMem(cfg)))

  // ── タイル [0][0] の分岐結果を Decoder にフィードバック ──────────────────
  val decoder = Module(new SharedDecoder(cfg))
  decoder.io.imem    <> imem.io
  decoder.io.brTaken := tiles(0)(0).io.brTaken
  decoder.io.aluOut  := tiles(0)(0).io.aluOut
  decoder.io.haltIn  := tiles(0)(0).io.halt

  // ── 全タイルに decode broadcast + データメモリ接続 + タイル間配線 ────────
  for (r <- 0 until cfg.rows; c <- 0 until cfg.cols) {
    val tile = tiles(r)(c)
    val dm   = dmems(r)(c)

    // Decoder broadcast
    tile.io.dec  := decoder.io.decode

    // データメモリ
    dm.io.addr   := tile.io.dmem.addr
    dm.io.wdata  := tile.io.dmem.wdata
    dm.io.wen    := tile.io.dmem.wen
    tile.io.dmem.rdata := dm.io.rdata

    // 出力
    io.halt(r)(c) := tile.io.halt
    io.pass(r)(c) := tile.io.pass

    // タイル間通信メッシュ配線
    def wireTile(dstDir: Int, src: Option[TileExecutionUnit], srcDir: Int): Unit =
      src match {
        case Some(n) => tile.io.tileIn(dstDir) := n.io.tileOut(srcDir)
        case None    =>
          tile.io.tileIn(dstDir).data  := 0.U
          tile.io.tileIn(dstDir).valid := false.B
      }

    wireTile(SimDir.N, if (r > 0)            Some(tiles(r-1)(c)) else None, SimDir.S)
    wireTile(SimDir.S, if (r < cfg.rows - 1) Some(tiles(r+1)(c)) else None, SimDir.N)
    wireTile(SimDir.E, if (c < cfg.cols - 1) Some(tiles(r)(c+1)) else None, SimDir.W)
    wireTile(SimDir.W, if (c > 0)            Some(tiles(r)(c-1)) else None, SimDir.E)
  }

  val allTiles   = tiles.flatten
  io.allDone    := allTiles.map(_.io.halt).reduce(_ && _)
  io.allPass    := allTiles.map(_.io.pass).reduce(_ && _)
  io.dbgPc      := decoder.io.decode.pc
}

object TileArrayMain extends App {
  val cfg = TileConfig(rows = 4, cols = 4, xlen = 32)
  ChiselStage.emitSystemVerilogFile(
    new SimTileArray(cfg),
    args        = Array("--target-dir", "generated"),
    firtoolOpts = Array("--lowering-options=disallowLocalVariables,disallowPackedArrays" )
  )
}
