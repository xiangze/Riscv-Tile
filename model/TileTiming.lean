-- =============================================================================
--  TileTiming.lean  ─  Timing (cycle-count) model for the Tiled RISC-V mesh
-- =============================================================================
--
--  Companion to TileRiscV.lean (Sparkle HDL).  That file is a *functional*
--  single-cycle model: every cycle it recomputes pc / regs / dmem / dirData,
--  i.e. it produces VALUES.  This file is the dual: a *timing-only* model.
--  It answers "WHEN does each instruction issue / retire, and where does the
--  machine stall?" while computing NO datapath value.
--
--  What is modelled
--  ────────────────
--   • per-instruction fixed latency        (LatencyModel / exLatency)
--   • pipeline fill + drain                 (depth offset on retire)
--   • structural hazards                    (mul / div unit, single dmem port)
--   • control hazards                       (branch flush, jump redirect)
--   • data hazards w/ forwarding (optional) (regReadyAt scoreboard)
--   • on-chip-network (tile link) contention + 1-cycle SEND→RECV rendezvous
--   • 2-D and 3-D tiling                    (Coord.z, Dir.U / Dir.D)
--
--  What is deliberately NOT modelled
--  ─────────────────────────────────
--   • any BitVec arithmetic / ALU result / branch *direction* computation.
--     The input is the already-resolved dynamic instruction stream (a trace)
--     per core; "taken?" for a branch is a control-flow fact carried in the
--     trace, never derived from operand values.
--
--  Relation to the RTL clock
--  ─────────────────────────
--   The RTL lives in one synchronous domain (`defaultDomain`).  We mirror that
--   with a single global cycle counter advanced by `MeshSim.tick`; every core
--   is stepped in lock-step, exactly like the hardware.  A tile value SENT in
--   cycle t is visible to a RECV only from cycle t + tileLinkLat (≥1), which
--   reproduces the registered `dirData` hop of `tileArray`.
-- =============================================================================

namespace TileTiming

-- A version-stable "replicate" (avoids Array.mkArray vs Array.replicate churn).
private def arrReplicate {α : Type} (n : Nat) (v : α) : Array α :=
  (List.replicate n v).toArray

-- ─────────────────────────────────────────────────────────────────────────────
--  §1  Mesh geometry  (2-D when layers = 1, 3-D otherwise)
-- ─────────────────────────────────────────────────────────────────────────────

inductive Dir | N | S | E | W | U | D
  deriving Repr, DecidableEq, Inhabited

/-- Index used to address the per-directed-link fabric arrays. -/
def Dir.toIdx : Dir → Nat
  | .N => 0 | .S => 1 | .E => 2 | .W => 3 | .U => 4 | .D => 5

/-- `dir ^ 1` of the RTL: the register a neighbour reads is the opposite port. -/
def Dir.opposite : Dir → Dir
  | .N => .S | .S => .N | .E => .W | .W => .E | .U => .D | .D => .U

structure Coord where
  x : Nat
  y : Nat
  z : Nat := 0
  deriving Repr, DecidableEq, Inhabited

structure MeshConfig where
  cols   : Nat := 4    -- x extent
  rows   : Nat := 4    -- y extent
  layers : Nat := 1    -- z extent (1 ⇒ planar 2-D mesh)
  deriving Repr, Inhabited

/-- Bounded neighbour: `none` at a mesh edge (RTL wires `zeroDirPort` there). -/
def Coord.neighbor (cfg : MeshConfig) (c : Coord) : Dir → Option Coord
  | .N => if c.y = 0            then none else some { c with y := c.y - 1 }
  | .S => if c.y + 1 ≥ cfg.rows then none else some { c with y := c.y + 1 }
  | .E => if c.x + 1 ≥ cfg.cols then none else some { c with x := c.x + 1 }
  | .W => if c.x = 0            then none else some { c with x := c.x - 1 }
  | .U => if c.z + 1 ≥ cfg.layers then none else some { c with z := c.z + 1 }
  | .D => if c.z = 0            then none else some { c with z := c.z - 1 }

/-- Flat index of the directed link "core `c`'s output toward `d`". -/
def MeshConfig.linkIndex (cfg : MeshConfig) (c : Coord) (d : Dir) : Nat :=
  (((c.z * cfg.rows + c.y) * cfg.cols + c.x) * 6) + d.toIdx

def MeshConfig.numLinks (cfg : MeshConfig) : Nat :=
  cfg.cols * cfg.rows * cfg.layers * 6

def MeshConfig.allCoords (cfg : MeshConfig) : List Coord :=
  (List.range cfg.layers).flatMap fun z =>
  (List.range cfg.rows).flatMap   fun y =>
  (List.range cfg.cols).map       fun x => { x := x, y := y, z := z }

-- ─────────────────────────────────────────────────────────────────────────────
--  §2  Timing-relevant instruction abstraction  (NO operand values)
--
--  This is the projection of a decoded RV32IM + CUSTOM-0 instruction onto the
--  information the timing model needs.  `branch (taken := b)` records which way
--  control actually went (a trace fact), not a computed comparison.
-- ─────────────────────────────────────────────────────────────────────────────

inductive InstrClass
  | alu                    -- LUI / AUIPC / OP-IMM / OP (integer, 1-cycle EX)
  | mul                    -- RV32M  MUL/MULH/...
  | div                    -- RV32M  DIV/REM/...   (iterative)
  | load                   -- dmem read   (occupies the dmem port)
  | store                  -- dmem write  (occupies the dmem port)
  | branch (taken : Bool)  -- conditional branch; `taken` from the trace
  | jump                   -- JAL / JALR (always redirects the front-end)
  | tileSend (dir : Dir)   -- CUSTOM-0 TILE_SEND dir, rs1
  | tileRecv (dir : Dir)   -- CUSTOM-0 TILE_RECV rd , dir
  | system                 -- ECALL / EBREAK ⇒ halt
  | nop
  deriving Repr, Inhabited

/-- One dynamic instruction in a core's trace.  Register fields are *optional*
    and only used when data-hazard modelling is enabled; they are still just
    indices, never values. -/
structure TimedInstr where
  cls : InstrClass
  rd  : Option (Fin 32) := none
  rs1 : Option (Fin 32) := none
  rs2 : Option (Fin 32) := none
  deriving Repr, Inhabited

-- ─────────────────────────────────────────────────────────────────────────────
--  §3  Pipeline / latency parameters
-- ─────────────────────────────────────────────────────────────────────────────

structure PipelineModel where
  depth           : Nat  := 5     -- IF ID EX MEM WB; first retire after `depth`
  aluLat          : Nat  := 1
  mulLat          : Nat  := 3
  divLat          : Nat  := 34
  loadLat         : Nat  := 2     -- registered dmem read (≥1 ⇒ load-use bubble)
  storeLat        : Nat  := 1
  mulPipelined    : Bool := true  -- can a new MUL issue every cycle?
  divPipelined    : Bool := false -- iterative divider blocks following ops
  dmemBusy        : Nat  := 1     -- cycles the single dmem port is held / access
  tileLinkLat     : Nat  := 1     -- SEND→RECV registered hop latency (≥1)
  branchPenalty   : Nat  := 3     -- bubbles on a mispredicted taken branch
  jumpPenalty     : Nat  := 2     -- bubbles on an unconditional redirect
  predictNotTaken : Bool := true  -- static predictor; taken ⇒ branchPenalty
  blockingRecv    : Bool := true  -- RECV stalls until a fresh token is present
  modelDataHazard : Bool := true  -- honour rs/rd readiness (forwarding model)
  deriving Repr, Inhabited

def PipelineModel.exLatency (m : PipelineModel) : InstrClass → Nat
  | .alu        => m.aluLat
  | .mul        => m.mulLat
  | .div        => m.divLat
  | .load       => m.loadLat
  | .store      => m.storeLat
  | .branch _   => m.aluLat
  | .jump       => m.aluLat
  | .tileSend _ => 1
  | .tileRecv _ => 1
  | .system     => 1
  | .nop        => 1

def defaultModel : PipelineModel := {}
def planar2DModel : PipelineModel := { depth := 5 }
def deep3DModel  : PipelineModel := { depth := 7, tileLinkLat := 2, mulLat := 4 }

-- ─────────────────────────────────────────────────────────────────────────────
--  §4  Per-core timing state  (a scoreboard, all fields are *cycle numbers*)
-- ─────────────────────────────────────────────────────────────────────────────

structure StallStats where
  struct : Nat := 0   -- mul / div / dmem-port busy
  data   : Nat := 0   -- RAW (e.g. load-use)
  ctrl   : Nat := 0   -- branch flush / jump redirect bubbles
  comm   : Nat := 0   -- RECV waiting on SEND, or link bandwidth
  deriving Repr, Inhabited

structure CoreSim where
  coord        : Coord
  trace        : List TimedInstr            -- remaining dynamic stream
  issueReadyAt : Nat := 0                   -- earliest cycle front-end may issue
  mulFreeAt    : Nat := 0
  divFreeAt    : Nat := 0
  dmemFreeAt   : Nat := 0
  regReadyAt   : Array Nat := arrReplicate 32 0   -- per-reg write-back cycle
  issued       : Nat := 0
  lastRetireAt : Nat := 0
  stalls       : StallStats := {}
  halted       : Bool := false
  deriving Repr, Inhabited

def CoreSim.mk (co : Coord) (prog : List TimedInstr) : CoreSim :=
  { coord := co, trace := prog }

-- ─────────────────────────────────────────────────────────────────────────────
--  §5  Whole-mesh state
--      `linkValidFrom k = some t`  ⇒  token on link k is readable from cycle t.
--      `linkBusyUntil k`           ⇒  link bandwidth reservation (1 word/cyc).
-- ─────────────────────────────────────────────────────────────────────────────

structure MeshSim where
  cfg           : MeshConfig
  model         : PipelineModel
  cycle         : Nat := 0
  cores         : Array CoreSim
  linkValidFrom : Array (Option Nat)
  linkBusyUntil : Array Nat
  deriving Repr, Inhabited

def MeshSim.init (cfg : MeshConfig) (m : PipelineModel)
    (program : Coord → List TimedInstr) : MeshSim :=
  let cores := (cfg.allCoords.map fun co => CoreSim.mk co (program co)).toArray
  { cfg := cfg, model := m, cycle := 0, cores := cores,
    linkValidFrom := arrReplicate cfg.numLinks none,
    linkBusyUntil := arrReplicate cfg.numLinks 0 }

-- ─────────────────────────────────────────────────────────────────────────────
--  §6  Step ONE core for ONE cycle.
--
--  Threading the fabric arrays through the result lets cores in the same tick
--  observe each other's SENDs at the correct (future) cycle.  Returns the
--  updated core plus the (possibly) updated fabric.
-- ─────────────────────────────────────────────────────────────────────────────

def stepCore (cfg : MeshConfig) (m : PipelineModel) (cyc : Nat)
    (core : CoreSim) (lvf : Array (Option Nat)) (lbu : Array Nat)
    : CoreSim × Array (Option Nat) × Array Nat :=
  if core.halted then
    (core, lvf, lbu)
  else if cyc < core.issueReadyAt then
    -- front-end occupied by a multi-cycle EX or a flush bubble issued earlier
    (core, lvf, lbu)
  else
    match core.trace with
    | [] => ({ core with halted := true }, lvf, lbu)   -- trace exhausted ⇒ done
    | instr :: rest =>
      let cls := instr.cls
      -- 1 ── data hazard (forwarding): operand's producer must have completed EX
      let rdy (r : Option (Fin 32)) : Nat :=
        match r with | none => 0 | some i => core.regReadyAt[i.val]!
      let dataOk : Bool :=
        (! m.modelDataHazard) ||
        (Nat.ble (rdy instr.rs1) cyc && Nat.ble (rdy instr.rs2) cyc)
      -- 2 ── structural hazard (shared functional unit / single dmem port)
      let structFreeAt : Nat :=
        match cls with
        | .mul          => core.mulFreeAt
        | .div          => core.divFreeAt
        | .load | .store => core.dmemFreeAt
        | _             => 0
      let structOk : Bool := Nat.ble structFreeAt cyc
      -- 3 ── communication hazard (NoC link)
      let commOk : Bool :=
        match cls with
        | .tileSend d =>                       -- bandwidth: ≤1 SEND / link / cyc
            Nat.ble (lbu[cfg.linkIndex core.coord d]!) cyc
        | .tileRecv d =>                       -- rendezvous with neighbour's SEND
            match core.coord.neighbor cfg d with
            | none    => true                  -- edge: RTL reads zeroDirPort
            | some nb =>
                if ! m.blockingRecv then true
                else match lvf[cfg.linkIndex nb d.opposite]! with
                     | some vf => Nat.ble vf cyc
                     | none    => false        -- nothing sent yet ⇒ wait
        | _ => true
      -- ── stall arbitration (priority: data > struct > comm) ──────────────────
      if ! dataOk then
        ({ core with issueReadyAt := cyc + 1,
                     stalls := { core.stalls with data := core.stalls.data + 1 } },
         lvf, lbu)
      else if ! structOk then
        ({ core with issueReadyAt := cyc + 1,
                     stalls := { core.stalls with struct := core.stalls.struct + 1 } },
         lvf, lbu)
      else if ! commOk then
        ({ core with issueReadyAt := cyc + 1,
                     stalls := { core.stalls with comm := core.stalls.comm + 1 } },
         lvf, lbu)
      else
        -- ── ISSUE ──────────────────────────────────────────────────────────────
        let exLat := m.exLatency cls
        -- result forwardable `exLat` cycles after issue; full retire includes fill
        let resultReadyAt := cyc + exLat
        let retireAt      := cyc + (m.depth - 1) + (exLat - 1)
        -- destination-register readiness (data-hazard scoreboard)
        let regReadyAt' :=
          match instr.rd with
          | some i => core.regReadyAt.set! i.val resultReadyAt
          | none   => core.regReadyAt
        -- functional-unit / dmem-port occupancy
        let (mulFreeAt', divFreeAt', dmemFreeAt') :=
          match cls with
          | .mul  => (cyc + (if m.mulPipelined then 1 else m.mulLat),
                      core.divFreeAt, core.dmemFreeAt)
          | .div  => (core.mulFreeAt,
                      cyc + (if m.divPipelined then 1 else m.divLat),
                      core.dmemFreeAt)
          | .load | .store => (core.mulFreeAt, core.divFreeAt, cyc + m.dmemBusy)
          | _     => (core.mulFreeAt, core.divFreeAt, core.dmemFreeAt)
        -- fabric write for a SEND (token readable from cyc + tileLinkLat)
        let (lvf', lbu') :=
          match cls with
          | .tileSend d =>
              let k := cfg.linkIndex core.coord d
              (lvf.set! k (some (cyc + m.tileLinkLat)), lbu.set! k (cyc + 1))
          | _ => (lvf, lbu)
        -- control hazard ⇒ when may the front-end issue the NEXT instruction?
        let ctrlBubbles : Nat :=
          match cls with
          | .branch taken => if taken && m.predictNotTaken then m.branchPenalty else 0
          | .jump         => m.jumpPenalty
          | _             => 0
        let nextIssue := cyc + 1 + ctrlBubbles
        let halted := match cls with | .system => true | _ => false
        ({ coord        := core.coord
           trace        := rest
           issueReadyAt := nextIssue
           mulFreeAt    := mulFreeAt'
           divFreeAt    := divFreeAt'
           dmemFreeAt   := dmemFreeAt'
           regReadyAt   := regReadyAt'
           issued       := core.issued + 1
           lastRetireAt := Nat.max core.lastRetireAt retireAt
           stalls       := { core.stalls with ctrl := core.stalls.ctrl + ctrlBubbles }
           halted       := halted },
         lvf', lbu')

-- ─────────────────────────────────────────────────────────────────────────────
--  §7  One global cycle: step every core in lock-step over a shared fabric
-- ─────────────────────────────────────────────────────────────────────────────

def MeshSim.tick (s : MeshSim) : MeshSim :=
  let cyc := s.cycle
  let init := (s.cores, s.linkValidFrom, s.linkBusyUntil)
  let (cores', lvf', lbu') :=
    (List.range s.cores.size).foldl
      (fun (acc : Array CoreSim × Array (Option Nat) × Array Nat) i =>
        let (cs, lvf, lbu) := acc
        let (core', lvf', lbu') := stepCore s.cfg s.model cyc cs[i]! lvf lbu
        (cs.set! i core', lvf', lbu'))
      init
  { s with cycle := cyc + 1, cores := cores',
           linkValidFrom := lvf', linkBusyUntil := lbu' }

/-- Run until all cores halt or `fuel` cycles elapse (fuel bounds NoC deadlock). -/
def MeshSim.run (s : MeshSim) : Nat → MeshSim
  | 0        => s
  | fuel + 1 => if s.cores.all (·.halted) then s else (s.tick).run fuel

-- ─────────────────────────────────────────────────────────────────────────────
--  §8  Metrics extraction
-- ─────────────────────────────────────────────────────────────────────────────

structure Metrics where
  simulatedCycles : Nat                          -- global clock ticks consumed
  makespan        : Nat                           -- last retire over all cores
  totalIssued     : Nat
  perCore         : Array (Coord × Nat × StallStats)
  deriving Repr

def MeshSim.metrics (s : MeshSim) : Metrics :=
  let makespan := s.cores.foldl (fun a c => Nat.max a c.lastRetireAt) 0
  let issued   := s.cores.foldl (fun a c => a + c.issued) 0
  let per := s.cores.map fun c => (c.coord, c.issued, c.stalls)
  { simulatedCycles := s.cycle, makespan := makespan,
    totalIssued := issued, perCore := per }

-- ─────────────────────────────────────────────────────────────────────────────
--  §9  Demo: 2×2 producer→consumer over the East link
--
--   (0,0): SEND E (x1) ; then 3 ALU            ─ producer
--   (1,0): RECV W      ; then 3 ALU            ─ consumer, must wait 1 cycle
--   (0,1),(1,1): 4 ALU each                    ─ independent workers
-- ─────────────────────────────────────────────────────────────────────────────

def aluI  : TimedInstr := { cls := .alu }

def demoProgram (c : Coord) : List TimedInstr :=
  if c.x == 0 && c.y == 0 then
    { cls := .tileSend .E, rs1 := some ⟨1, by decide⟩ } :: List.replicate 3 aluI
  else if c.x == 1 && c.y == 0 then
    { cls := .tileRecv .W, rd := some ⟨2, by decide⟩ } :: List.replicate 3 aluI
  else
    List.replicate 4 aluI

def demoSim : MeshSim :=
  MeshSim.init { cols := 2, rows := 2, layers := 1 } defaultModel demoProgram

#eval (demoSim.run 100).metrics
-- Expect: consumer (1,0) shows comm := 1 (one RECV stall cycle); everyone
-- issues their whole trace; makespan ≈ depth + work − 1.

-- A pure ALU core: n independent 1-cycle ops on a depth-`d` pipeline take
-- exactly n issue cycles (IPC = 1) and a makespan of (n-1) + d.
#eval
  let s := (MeshSim.init { cols := 1, rows := 1 } defaultModel
              (fun _ => List.replicate 8 aluI)).run 100
  (s.metrics.simulatedCycles, s.metrics.makespan)   -- expect (9, 11)

-- A divide (non-pipelined, 34-cycle) immediately followed by a dependent ALU
-- shows up as data-hazard stalls, not as extra issue slots:
#eval
  let prog : List TimedInstr :=
    [ { cls := .div, rd := some ⟨5, by decide⟩, rs1 := some ⟨1, by decide⟩,
        rs2 := some ⟨2, by decide⟩ },
      { cls := .alu, rd := some ⟨6, by decide⟩, rs1 := some ⟨5, by decide⟩ } ]
  let s := (MeshSim.init { cols := 1, rows := 1 } defaultModel (fun _ => prog)).run 200
  s.metrics.perCore

end TileTiming
