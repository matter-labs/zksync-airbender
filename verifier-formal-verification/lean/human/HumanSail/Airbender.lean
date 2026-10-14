import HumanSail.Machine
import Human.RV32

/-! # Airbender = the official Sail RISC-V model, with the changes listed here

The Sail model is riscv/sail-riscv, turned into Lean by `sail/regen.sh` (pins: `sail/PINS.md`) with
`sail/config/airbender-base.json`: the stock RV32 config with every extension except M and Zicsr switched off,
and no timer or interrupt devices. Everything Airbender does differently from that model is in this file,
marked `-- Airbender:`, following Airbender's ISA table (zksync-airbender `spec/top-down/00 master.md`,
"Supported instruction set"). Airbender's instruction formats are our own table `RV.decode`; their effect is
Sail's `execute`.

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
  runSail (do sail_model_init (); init_model "") { regs := fun r => by cases r <;> exact default, mem := fun _ => 0 }

/-- The state after reset, with Airbender's `misa` and memory map. -/
noncomputable def resetState : SailState :=
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
def Configured (s : SailState) : Prop := ∀ r, Volatile r = false → s.regs r = resetState.regs r

/-! ## The Sail model as generated

`sail/config/airbender-base.json` switches these extensions off. Airbender has none of them; the ones marked (*)
would otherwise re-decode instructions Airbender runs as plain RV32I. Checked here against the generated model. -/
theorem sail_extensions_off :
    hartSupports .Ext_Zihintntl = false ∧   -- (*) `add x0, x0, x2..x5` would be an NTL hint
    hartSupports .Ext_Zicbop = false ∧      -- (*) `ori x0, rs1, imm` would be a prefetch
    hartSupports .Ext_Zicfilp = false ∧     -- landing pads (would check JALR targets)
    hartSupports .Ext_Zicfiss = false ∧     -- shadow stack
    hartSupports .Ext_C = false ∧ hartSupports .Ext_Zca = false := by  -- compressed instructions
  decide +kernel

/-! ## Airbender's instructions, named as in Sail -/

def sailBop : RV.Cond → bop
  | .eq => .BEQ | .ne => .BNE | .lt => .BLT | .ge => .BGE | .ltu => .BLTU | .geu => .BGEU

def sailRop : RV.Op → rop
  | .sub => .SUB | .sll => .SLL | .slt => .SLT | .sltu => .SLTU | .xor => .XOR | .srl => .SRL | .sra => .SRA
  | .or => .OR | .and => .AND | _ => .ADD   -- (M ops are mapped to MUL/DIV/REM below)

/-- Our instructions (`Human/RV32.lean`) in Sail's vocabulary. Immediates: Sail keeps the encoded bits, we keep
the decoded value, so `toSail` takes the encoded bits back out. -/
def toSail : RV.Instr → instruction
  | .lui rd imm              => .UTYPE (imm.extractLsb' 12 20, .Regidx rd, .LUI)
  | .auipc rd imm            => .UTYPE (imm.extractLsb' 12 20, .Regidx rd, .AUIPC)
  | .jal rd off              => .JAL (off.extractLsb' 0 21, .Regidx rd)
  | .jalr rd rs1 off         => .JALR (off.extractLsb' 0 12, .Regidx rs1, .Regidx rd)
  | .branch c rs1 rs2 off    => .BTYPE (off.extractLsb' 0 13, .Regidx rs2, .Regidx rs1, sailBop c)
  | .load n sg rd rs1 off    => .LOAD (off.extractLsb' 0 12, .Regidx rs1, .Regidx rd, !sg, n)
  | .store n rs2 rs1 off     => .STORE (off.extractLsb' 0 12, .Regidx rs2, .Regidx rs1, n)
  | .opImm .add rd rs1 imm   => .ITYPE (imm.extractLsb' 0 12, .Regidx rs1, .Regidx rd, .ADDI)
  | .opImm .slt rd rs1 imm   => .ITYPE (imm.extractLsb' 0 12, .Regidx rs1, .Regidx rd, .SLTI)
  | .opImm .sltu rd rs1 imm  => .ITYPE (imm.extractLsb' 0 12, .Regidx rs1, .Regidx rd, .SLTIU)
  | .opImm .xor rd rs1 imm   => .ITYPE (imm.extractLsb' 0 12, .Regidx rs1, .Regidx rd, .XORI)
  | .opImm .or rd rs1 imm    => .ITYPE (imm.extractLsb' 0 12, .Regidx rs1, .Regidx rd, .ORI)
  | .opImm .and rd rs1 imm   => .ITYPE (imm.extractLsb' 0 12, .Regidx rs1, .Regidx rd, .ANDI)
  | .opImm .sll rd rs1 imm   => .SHIFTIOP (imm.extractLsb' 0 6, .Regidx rs1, .Regidx rd, .SLLI)
  | .opImm .srl rd rs1 imm   => .SHIFTIOP (imm.extractLsb' 0 6, .Regidx rs1, .Regidx rd, .SRLI)
  | .opImm .sra rd rs1 imm   => .SHIFTIOP (imm.extractLsb' 0 6, .Regidx rs1, .Regidx rd, .SRAI)
  | .opImm _ _ _ imm         => .ILLEGAL imm                    -- never decoded (no M op takes an immediate)
  | .op .mul rd rs1 rs2      => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.Low, .Signed, .Signed⟩)
  | .op .mulhu rd rs1 rs2    => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.High, .Unsigned, .Unsigned⟩)
  | .op .divu rd rs1 rs2     => .DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, true)
  | .op .remu rd rs1 rs2     => .REM (.Regidx rs2, .Regidx rs1, .Regidx rd, true)
  | .op op rd rs1 rs2        => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, sailRop op)

/-! ## The machine -/

/-- Airbender's decoder is our encoding table `RV.decode` (`Human/RV32.lean`, with its `-- Airbender:` rows).
`HumanSail/Theorems.lean` states that Sail's own decoder gives the same instruction for every word of that table,
except the extra encodings Airbender accepts (`Lenient`). -/
def decode (w : BitVec 32) : Option instruction := (RV.decode w).map toSail

/-- Execute one instruction: as Sail does, except loads into x0. -/
noncomputable def execute (i : instruction) : SailM ExecutionResult :=
  match i with
  | .LOAD (_, _, rd, _, _) => if rd == zreg then pure RETIRE_SUCCESS  -- Airbender: a load into x0 only
                              else SailRV32.Functions.execute i       --   advances the PC (no memory access)
  | _ => SailRV32.Functions.execute i

/-- One step, the way Sail's own `run_hart_active` + `try_step` run a 32-bit instruction: fetch, decode,
`nextPC := PC + 4`, execute, `PC := nextPC`. Anything else is not a step of Airbender (`none`): a fetch fault,
a word outside the table, or any trap (misaligned or out-of-range access, write to ROM, …). -/
noncomputable def step (s : SailState) : Option SailState :=
  let run : SailM Bool := do
    let .F_Base w ← fetch () | pure false
    let some i := decode w | pure false
    writeReg Register.nextPC ((← readReg Register.PC) + 4)
    let .Retire_Success () ← execute i | pure false
    if (← readReg Register.nextPC).toNat % 4 ≠ 0 then pure false  -- Airbender: jump targets 4-byte aligned
    else                                                          --   (no compressed instructions)
      tick_pc ()
      pure true
  match runSail run s with
  | .ok true s' => some s'
  | _ => none

end Airbender
