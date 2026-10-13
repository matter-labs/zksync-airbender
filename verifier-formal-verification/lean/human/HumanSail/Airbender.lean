import HumanSail.Machine

/-! # Airbender = the official Sail RISC-V model, with the changes listed here

The Sail model is riscv/sail-riscv, turned into Lean by `sail/regen.sh` (pins: `sail/PINS.md`) with
`sail/config/airbender-base.json`: the stock RV32 config with every extension except M and Zicsr switched off,
and no timer or interrupt devices. Everything Airbender does differently from that model is in this file,
marked `-- Airbender:`, following Airbender's ISA table (zksync-airbender `spec/top-down/00 master.md`,
"Supported instruction set").

Our own fast spec `RV.step` (`Human/RV32.lean`), which the program proofs run on, is proven to follow this
machine in `HumanSail/Theorems.lean`. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Airbender

/-! ## The machine's fixed settings -/

/-- `misa`: 32-bit, extensions I and M. -/
def misa : BitVec 32 := 0x40001100

/-- A memory region; misaligned accesses fault (Airbender cannot prove them). -/
def region (base size : Nat) (readable writable executable : Bool) : PMA_Region where
  base := BitVec.ofNat 64 base
  size := BitVec.ofNat 64 size
  include_in_device_tree := false
  attributes := {
    mem_type := .MainMemory, cacheable := true, coherent := true,
    readable, writable, executable, read_idempotent := true, write_idempotent := true,
    misaligned_exceptions := { load_store := some .AlignmentException, vector := some .AlignmentException,
                               amo := .AlignmentException, lrsc := .AlignmentException },
    atomic_support := .AMONone, reservability := .RsrvNone, supports_cbo_zero := false,
    supports_pte_read := false, supports_pte_write := false,
    misaligned_atomicity_granule_size_exp := 0, vector_misaligned_atomicity_granule_size_exp := 0 }

/-- Memory map (`rust/lds/memory.x`): ROM `[0, 4 MiB)` holds the program, RAM `[4 MiB, 1 GiB)`. Nothing else. -/
def RAM_START : Nat := 0x400000
def RAM_END   : Nat := 0x40000000
def memoryMap : List PMA_Region :=
  [ region 0         RAM_START               (readable := true) (writable := false) (executable := true),
    region RAM_START (RAM_END - RAM_START)   (readable := true) (writable := true)  (executable := false) ]

/-- Sail's own initialisation and reset (all registers at their defaults, memory 0). -/
noncomputable def initResult :=
  runF (do sail_model_init (); init_model "") { regs := fun r => by cases r <;> exact default, mem := fun _ => 0 }

/-- The state after reset, with Airbender's `misa` and memory map. -/
noncomputable def stInit : FState :=
  let s := match initResult with | .ok _ s => s | .error _ s => s
  (s.set .misa misa).set .pma_regions memoryMap

/-- Registers a program changes: x1..x31 and the PC (plus Sail's bookkeeping `nextPC` and counters). -/
def Volatile : Register → Bool
  | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7 | .x8 | .x9 | .x10 | .x11 | .x12 | .x13 | .x14 | .x15
  | .x16 | .x17 | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28
  | .x29 | .x30 | .x31 | .PC | .nextPC | .minstret | .minstret_increment => true
  | _ => false

/-- A state of the Airbender machine: every other register (privilege, `misa`, `mstatus`, memory map, …)
is as after reset. -/
def Sys (s : FState) : Prop := ∀ r, Volatile r = false → s.regs r = stInit.regs r

/-! ## The changes -/

/-- The RV32IM instructions Airbender runs. -/
def Supported : instruction → Bool
  | .UTYPE _ | .JAL _ | .JALR _ | .BTYPE _ | .ITYPE _ | .SHIFTIOP _ | .RTYPE _ | .LOAD _ | .STORE _ => true
  | .MUL (_, _, _, op) => op.result_part == .Low || op.signed_rs1 == .Unsigned  -- Airbender: no MULH, MULHSU
  | .DIV (_, _, _, isUnsigned) | .REM (_, _, _, isUnsigned) => isUnsigned        -- Airbender: no DIV, REM
  | _ => false

/-- Decode a 32-bit instruction word: as Sail does, except for the first two rows. -/
noncomputable def decode (w : BitVec 32) : SailM (Option instruction) := do
  let opcode := w.extractLsb' 0 7
  let funct3 := w.extractLsb' 12 3
  let funct7 := w.extractLsb' 25 7
  let rd := regidx.Regidx (w.extractLsb' 7 5)
  let rs1 := regidx.Regidx (w.extractLsb' 15 5)
  let rs2 := regidx.Regidx (w.extractLsb' 20 5)
  if opcode = 0b1100111 then                                     -- Airbender: JALR with any funct3
    pure (some (.JALR (w.extractLsb' 20 12, rs1, rd)))
  else if opcode = 0b0110011 ∧ funct7 ≠ 1 ∧ funct3 = 2 then pure (some (.RTYPE (rs2, rs1, rd, .SLT)))
  else if opcode = 0b0110011 ∧ funct7 ≠ 1 ∧ funct3 = 3 then pure (some (.RTYPE (rs2, rs1, rd, .SLTU)))
  else if opcode = 0b0110011 ∧ funct7 ≠ 1 ∧ funct3 = 4 then pure (some (.RTYPE (rs2, rs1, rd, .XOR)))
  else if opcode = 0b0110011 ∧ funct7 ≠ 1 ∧ funct3 = 6 then pure (some (.RTYPE (rs2, rs1, rd, .OR)))
  else if opcode = 0b0110011 ∧ funct7 ≠ 1 ∧ funct3 = 7 then      -- Airbender: SLT…AND above with any funct7
    pure (some (.RTYPE (rs2, rs1, rd, .AND)))                     -- (except 0000001, the M extension)
  else
    let i ← ext_decode w                                          -- Sail's decoder
    pure (if Supported i then some i else none)

/-- Execute one instruction: as Sail does, except loads into x0. -/
noncomputable def execute (i : instruction) : SailM ExecutionResult :=
  match i with
  | .LOAD (_, _, rd, _, _) => if rd == zreg then pure RETIRE_SUCCESS  -- Airbender: a load into x0 only
                              else SailRV32.Functions.execute i       --   advances the PC (no memory access)
  | _ => SailRV32.Functions.execute i

/-- One step, the way Sail's own `run_hart_active` + `try_step` run a 32-bit instruction: fetch, decode,
`nextPC := PC + 4`, execute, `PC := nextPC`. Anything else is not a step of Airbender (`none`): a fetch fault,
an instruction not listed above, or any trap (misaligned or out-of-range access, misaligned jump target, write
to ROM, …). -/
noncomputable def step (s : FState) : Option FState :=
  let run : SailM Bool := do
    let .F_Base w ← fetch () | pure false
    let some i ← decode w | pure false
    writeReg Register.nextPC ((← readReg Register.PC) + 4)
    let .Retire_Success () ← execute i | pure false
    tick_pc ()
    pure true
  match runF run s with
  | .ok true s' => some s'
  | _ => none

end Airbender
