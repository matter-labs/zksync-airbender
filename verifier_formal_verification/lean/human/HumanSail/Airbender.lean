import HumanSail.Machine
import Human.RV32

/-! # Airbender = the official Sail RISC-V model, with the changes listed here

The Sail model is riscv/sail-riscv, turned into Lean by `sail/regen.sh` (pins: `sail/PINS.md`) with
`sail/config/airbender-base.json`: the stock RV32 config with every extension except M and Zicsr switched off,
and no timer or interrupt devices. Everything Airbender does differently from that model is in this file,
marked `-- Airbender:`, following Airbender's ISA table (zksync-airbender `spec/top-down/00 master.md`,
"Supported instruction set"). Airbender's instruction formats are our own table `RV.decode`; their effect is
Sail's `execute`. The machine adds one thing Sail does not have: the program's input (Airbender's non-determinism
source, CSR `0x7c0`): the words not yet read (a list; a read with none left has no next state).

Our own fast spec `RV.step` (`Human/RV32.lean`), which the program proofs run on, follows this machine:
stated in `HumanSail/Theorems.lean`, proven in `slop/Slop/Equiv/`. -/

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

/-- Memory map (`rust/lds/memory.x`): ROM `[0, 4 MiB)` holds the program, RAM `[4 MiB, 1 GiB)`. Nothing else.
The same map as our spec's (`RV.ROM_END`, `RV.RAM_END` in `Human/RV32.lean`). -/
def RAM_START : Nat := RV.ROM_END
def RAM_END   : Nat := RV.RAM_END
def memoryMap : List PMA_Region :=
  [ region 0         RAM_START               (readable := true) (writable := false) (executable := true),
    region RAM_START (RAM_END - RAM_START)   (readable := true) (writable := true)  (executable := false) ]

/-- Sail's own initialisation and reset (all registers at their defaults, memory 0). -/
noncomputable def sailResetRun :=
  runSail (do sail_model_init (); init_model "") { regs := fun r => by cases r <;> exact default, mem := fun _ => 0 }

/-- The state after reset, with Airbender's `misa` and memory map. -/
noncomputable def resetState : SailState :=
  let σ := match sailResetRun with | .ok _ σ => σ | .error _ σ => σ
  (σ.set .misa misa).set .pma_regions memoryMap

/-- The registers a program can change: x1..x31 and the PC (plus Sail's bookkeeping `nextPC` and counters). -/
def writtenByProgram : Register → Bool
  | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7 | .x8 | .x9 | .x10 | .x11 | .x12 | .x13 | .x14 | .x15
  | .x16 | .x17 | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28
  | .x29 | .x30 | .x31 | .PC | .nextPC | .minstret | .minstret_increment => true
  | _ => false

/-- A state of the Airbender machine: every register a program never writes (privilege, `misa`, `mstatus`,
memory map, …) is as after reset. -/
def Configured (σ : SailState) : Prop := ∀ r, writtenByProgram r = false → σ.regs r = resetState.regs r

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

/-- Zimop stays on: Sail decodes Airbender's field operations `mop.rr.N` (and its `execute` is replaced below). -/
theorem sail_zimop_on : hartSupports .Ext_Zimop = true := by decide +kernel

/-! ## Airbender's instructions, named as in Sail -/

def sailBranchOp : RV.Cond → bop
  | .eq => .BEQ | .ne => .BNE | .lt => .BLT | .ge => .BGE | .ltu => .BLTU | .geu => .BGEU

def sailAluOp : RV.Op → rop
  | .sub => .SUB | .sll => .SLL | .slt => .SLT | .sltu => .SLTU | .xor => .XOR | .srl => .SRL | .sra => .SRA
  | .or => .OR | .and => .AND | _ => .ADD   -- (M ops are mapped to MUL/DIV/REM below)

/-- The `N` of `mop.rr.N` for each field operation (Sail decodes `N` from bits 30, 27, 26 of the word). -/
def mopIndex : RV.FieldOp → BitVec 3
  | .add => 0 | .sub => 1 | .mul => 2 | .fma => 3 | .triAdd => 4

def mopOfIndex : BitVec 3 → Option RV.FieldOp
  | 0 => some .add | 1 => some .sub | 2 => some .mul | 3 => some .fma | 4 => some .triAdd | _ => none

/-- A Zicsr instruction on CSR `csr` in Sail's vocabulary (`src`: the register, or the immediate). -/
noncomputable def csrToSail (csr : BitVec 12) (op : RV.CsrOp) (src rd : RV.Reg) : instruction :=
  match op with
  | .rw  => .CSRReg (csr, .Regidx src, .Regidx rd, .CSRRW)
  | .rs  => .CSRReg (csr, .Regidx src, .Regidx rd, .CSRRS)
  | .rc  => .CSRReg (csr, .Regidx src, .Regidx rd, .CSRRC)
  | .rwi => .CSRImm (csr, src, .Regidx rd, .CSRRW)
  | .rsi => .CSRImm (csr, src, .Regidx rd, .CSRRS)
  | .rci => .CSRImm (csr, src, .Regidx rd, .CSRRC)

/-- Our instructions (`Human/RV32.lean`) in Sail's vocabulary. Immediates: Sail keeps the encoded bits, we keep
the decoded value, so `toSail` takes the encoded bits back out. -/
noncomputable def toSail : RV.Instr → instruction
  | .lui rd imm              => .UTYPE (imm.extractLsb' 12 20, .Regidx rd, .LUI)
  | .auipc rd imm            => .UTYPE (imm.extractLsb' 12 20, .Regidx rd, .AUIPC)
  | .jal rd offset           => .JAL (offset.extractLsb' 0 21, .Regidx rd)
  | .jalr rd rs1 offset      => .JALR (offset.extractLsb' 0 12, .Regidx rs1, .Regidx rd)
  | .branch cond rs1 rs2 offset => .BTYPE (offset.extractLsb' 0 13, .Regidx rs2, .Regidx rs1, sailBranchOp cond)
  | .load numBytes signed rd rs1 offset =>
      .LOAD (offset.extractLsb' 0 12, .Regidx rs1, .Regidx rd, !signed, numBytes)
  | .store numBytes rs2 rs1 offset => .STORE (offset.extractLsb' 0 12, .Regidx rs2, .Regidx rs1, numBytes)
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
  | .op op rd rs1 rs2        => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, sailAluOp op)
  | .mop op rd rs1 rs2       => .ZIMOP_MOP_RR (mopIndex op, .Regidx rs2, .Regidx rs1, .Regidx rd)
  | .inputRead op rd         => csrToSail 0x7c0 op 0 rd
  | .inputWrite op src       => csrToSail 0x7c0 op src 0
  | .delegate op             => csrToSail 0x7c7 op 0 0

/-! ## The machine -/

/-! Airbender's decoder is our encoding table `RV.decode` (`Human/RV32.lean`, with its `-- Airbender:` rows), each
instruction then run as Sail's `toSail` of it. `HumanSail/Theorems.lean` states that Sail's own decoder gives the
same instruction for every word of that table, except the extra encodings Airbender accepts (`ExtraEncoding`). -/

/-- Airbender's CSR 0x7c0 (`srcZero`: the source register or immediate is 0): a read of the next input word `next`,
a write (no effect), or rejected. -/
noncomputable def nonDeterminism (next : BitVec 32) (srcZero : Bool) (rd : regidx) : SailM ExecutionResult :=
  if srcZero && rd != zreg then do
    wX_bits rd next
    pure RETIRE_SUCCESS
  else if !srcZero && rd == zreg then pure RETIRE_SUCCESS
  else pure (.Illegal_Instruction ())

/-- Execute one instruction (`next`: the next input word): as Sail does, except loads into x0, the field operations
and CSR 0x7c0. -/
noncomputable def execute (next : BitVec 32) (instr : instruction) : SailM ExecutionResult :=
  match instr with
  | .CSRReg (csr, rs1, rd, _) =>                       -- Airbender: CSR 0x7c0 is the non-determinism source
      if csr == 0x7c0 then nonDeterminism next (rs1 == zreg) rd  --   (`nonDeterminism`; Sail: illegal)
      else SailRV32.Functions.execute instr
  | .CSRImm (csr, imm, rd, _) =>
      if csr == 0x7c0 then nonDeterminism next (imm == 0) rd
      else SailRV32.Functions.execute instr
  | .LOAD (_, _, rd, _, _) => if rd == zreg then pure RETIRE_SUCCESS  -- Airbender: a load into x0 only
                              else SailRV32.Functions.execute instr   --   advances the PC (no memory access)
  | .ZIMOP_MOP_RR (n, rs2, rs1, rd) =>                 -- Airbender: `mop.rr.0 … 4` are field operations
      match mopOfIndex n with                          --   (`RV.mopVal`; Sail's Zimop writes 0), and need rd ≠ x0
      | some op => if rd == zreg then pure (.Illegal_Instruction ()) else do
          let a ← rX_bits rs1
          let b ← rX_bits rs2
          let old ← rX_bits rd
          wX_bits rd (RV.mopVal op a b old)
          pure RETIRE_SUCCESS
      | none => SailRV32.Functions.execute instr
  | _ => SailRV32.Functions.execute instr

/-- Register `i` of a Sail state, read the way Sail's instructions read it (x0 reads as 0). -/
noncomputable def getReg (σ : SailState) (i : RV.Reg) : BitVec 32 :=
  match runSail (rX_bits (.Regidx i)) σ with | .ok v _ => v | .error _ _ => 0

/-- Memory after writing the words `ws` from address `addr` on, little-endian (as `RV.State.storeWords`). -/
def writeWords (mem : Nat → BitVec 8) (addr : RV.Word) : List (BitVec 32) → (Nat → BitVec 8)
  | []      => mem
  | w :: ws => writeWords (writeBytes mem addr.toNat 4 w) (addr + 4) ws

/-- Airbender's delegations are custom circuits with nothing in Sail to compare against (there
`csrrw x0, 0x7c7, x0` is an illegal instruction), so the machine runs our definition (`RV.Delegation`,
`Human/Delegations.lean`) on Sail's state. `none`: the instruction at the PC is not a delegation call. -/
noncomputable def delegation (σ : SailState) : Option (Option SailState) :=
  let pc := σ.regs .PC
  let mem : RV.Word → BitVec 8 := fun a => σ.mem a.toNat
  let w := RV.read mem pc 4
  if pc.toNat % 4 = 0 ∧ pc.toNat + 4 ≤ RAM_START then
    match RV.decode w with
    | some (.delegate _) => some <|
        match RV.Delegation.blake2s (getReg σ 10) (getReg σ 11) (getReg σ 12) mem with
        | some (n, x12, out) =>
            if RV.isRun mem pc w n then
              let σ₁ : SailState := { σ with mem := writeWords σ.mem (getReg σ 10) out.toList }
              let σ₂ := match runSail (wX_bits (.Regidx 12) x12) σ₁ with | .ok _ σ' => σ' | .error _ σ' => σ'
              let pc' := pc + BitVec.ofNat 32 (4 * n)
              some ((σ₂.set .PC pc').set .nextPC pc')
            else none
        | none => none
    | _ => none
  else none

/-- The Airbender machine: Sail's state, plus the input (CSR 0x7c0): the words not yet read. -/
structure Machine where
  sail  : SailState
  input : List (BitVec 32)

/-- One instruction, the way Sail's own `run_hart_active` + `try_step` run a 32-bit instruction: fetch, decode,
`nextPC := PC + 4`, execute, `PC := nextPC`. Gives whether it read an input word; `none`: no step (a fetch fault,
a word outside the table, or any trap: misaligned or out-of-range access, write to ROM, …). -/
noncomputable def sailStep (next : BitVec 32) : SailM (Option Bool) := do
  let .F_Base word ← fetch () | pure none
  let some instr := RV.decode word | pure none
  writeReg Register.nextPC ((← readReg Register.PC) + 4)
  let .Retire_Success () ← execute next (toSail instr) | pure none
  if (← readReg Register.nextPC).toNat % 4 ≠ 0 then pure none  -- Airbender: jump targets 4-byte aligned
  else                                                         --   (no compressed instructions)
    tick_pc ()
    pure (some instr.readsInput)

/-- One step of the machine: a delegation call, or one Sail instruction (no next state for an input read once the
input is used up). -/
noncomputable def step (m : Machine) : Option Machine :=
  match delegation m.sail with
  | some r => r.map fun σ' => ⟨σ', m.input⟩
  | none =>
    match runSail (sailStep (m.input.headD 0)) m.sail, m.input with
    | .ok (some false) σ', input     => some ⟨σ', input⟩
    | .ok (some true)  σ', _ :: rest => some ⟨σ', rest⟩
    | _, _ => none

end Airbender
