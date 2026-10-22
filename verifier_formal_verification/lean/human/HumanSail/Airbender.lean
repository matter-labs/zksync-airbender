import HumanSail.Machine
import Human.RV32

/-! # Airbender = the official Sail RISC-V model, with the changes listed here

The Sail model is riscv/sail-riscv, turned into Lean by `sail/regen.sh` (pins: `sail/PINS.md`) with
`sail/config/airbender-base.json`: the stock RV32 config without timer or interrupt devices and with the few
extensions off that change how base RV32I behaves (`sail/README.md`). The other extensions stay on, but Airbender's
decoder (`RV.decode`, below) rejects their instructions. Everything Airbender does differently from that model is in
this file, marked `-- Airbender:`, following Airbender's ISA table and decoder (as cited in `Human/RV32.lean`).
Airbender's instruction formats are our own table `RV.decode`; their effect is Sail's `execute`. The machine adds one
thing Sail does not have: the program's input (Airbender's non-determinism source, CSR `0x7c0`): the words not yet read
(a list; a read with none left has no next state).

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

/-- `csrrw rd, csr, rs1` in Sail's vocabulary. -/
noncomputable def csrToSail (csr : BitVec 12) (rs1 rd : RV.Reg) : instruction :=
  .CSRReg (csr, .Regidx rs1, .Regidx rd, .CSRRW)

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
  | .rev8 rd rs1             => .REV8 (.Regidx rs1, .Regidx rd)
  | .xorRot n rd rs1         => .ZIMOP_MOP_R (n, .Regidx rs1, .Regidx rd)
  | .inputRead rd            => csrToSail 0x7c0 0 rd
  | .inputWrite src          => csrToSail 0x7c0 src 0
  | .delegate k              => csrToSail k.csr 0 0

/-! ## The machine -/

/-! Airbender's decoder is our encoding table `RV.decode` (`Human/RV32.lean`, with its `-- Airbender:` rows), each
instruction then run as Sail's `toSail` of it. `HumanSail/Theorems.lean` states that Sail's own decoder gives the
same instruction for every word of that table. -/

/-- Airbender's `csrrw rd, 0x7c0, rs1`: a read of the next input word `next` (rs1 = x0, rd ≠ x0), a write (no
effect: rs1 ≠ x0, rd = x0), or rejected. -/
noncomputable def nonDeterminism (next : BitVec 32) (rs1 rd : regidx) : SailM ExecutionResult :=
  if rs1 == zreg && rd != zreg then do
    wX_bits rd next
    pure RETIRE_SUCCESS
  else if rs1 != zreg && rd == zreg then pure RETIRE_SUCCESS
  else pure (.Illegal_Instruction ())

/-- Execute one instruction (`next`: the next input word): as Sail does, except loads into x0, the field operations,
`mop.r.N` and CSR 0x7c0. -/
noncomputable def execute (next : BitVec 32) (instr : instruction) : SailM ExecutionResult :=
  match instr with
  | .CSRReg (csr, rs1, rd, .CSRRW) =>                  -- Airbender: CSR 0x7c0 is the non-determinism source
      if csr == 0x7c0 then nonDeterminism next rs1 rd   --   (`nonDeterminism`; Sail: illegal)
      else SailRV32.Functions.execute instr
  | .LOAD (_, _, rd, _, _) => if rd == zreg then pure RETIRE_SUCCESS  -- Airbender: a load into x0 only
                              else SailRV32.Functions.execute instr   --   advances the PC (no memory access)
  | .ZIMOP_MOP_RR (n, rs2, rs1, rd) =>                 -- Airbender: `mop.rr.0 … 4` are field operations
      match mopOfIndex n with                          --   (`RV.mopVal`; Sail's Zimop writes 0)
      | some op => do
          let a ← rX_bits rs1
          let b ← rX_bits rs2
          let old ← rX_bits rd
          wX_bits rd (RV.mopVal op a b old)
          pure RETIRE_SUCCESS
      | none => SailRV32.Functions.execute instr
  | .ZIMOP_MOP_R (n, rs1, rd) => do                    -- Airbender: `mop.r.N` is `rd := (rd ^^^ rs1)` rotated right
      let a ← rX_bits rs1                              --   by N (`RV.Instr.xorRot`; Sail's Zimop writes 0)
      let old ← rX_bits rd
      wX_bits rd ((old ^^^ a).rotateRight n.toNat)
      pure RETIRE_SUCCESS
  | _ => SailRV32.Functions.execute instr

/-- Register `i` of a Sail state, read the way Sail's instructions read it (x0 reads as 0). -/
noncomputable def getReg (σ : SailState) (i : RV.Reg) : BitVec 32 :=
  match runSail (rX_bits (.Regidx i)) σ with | .ok v _ => v | .error _ _ => 0

/-- Memory after writing the words of `ws` (address, value), little-endian (as `RV.State.storeAll`). -/
def writeAll (mem : Nat → BitVec 8) : List (RV.Word × BitVec 32) → (Nat → BitVec 8)
  | []           => mem
  | (a, w) :: ws => writeAll (writeBytes mem a.toNat 4 w) ws

/-- A delegation call's effect on Sail's state (as `RV.State.applyEffect`). -/
noncomputable def applyEffect (σ : SailState) (e : RV.Effect) : Option SailState :=
  if e.writes.all fun aw => decide (RV.writable aw.1 4 ∧ RV.aligned aw.1 4) then
    let σ₁ : SailState := { σ with mem := writeAll σ.mem e.writes }
    let σ₂ := match runSail (wX_bits (.Regidx e.reg) e.val) σ₁ with | .ok _ σ' => σ' | .error _ σ' => σ'
    let pc' := σ.regs .PC + 4
    some ((σ₂.set .PC pc').set .nextPC pc')
  else none

/-- Airbender's delegations are custom circuits with nothing in Sail to compare against (there `csrrw x0, <csr>, x0`
is an illegal instruction), so the machine runs our definition (`RV.Delegation`, `Human/Delegations.lean`) on Sail's
state. `none`: the instruction at the PC is not a delegation call. -/
noncomputable def delegation (σ : SailState) : Option (Option SailState) :=
  let pc := σ.regs .PC
  let mem : RV.Word → BitVec 8 := fun a => σ.mem a.toNat
  if pc.toNat % 4 = 0 ∧ pc.toNat + 4 ≤ RAM_START then
    match RV.decode (RV.read mem pc 4) with
    | some (.delegate k) =>
        some ((RV.Delegation.effect k (getReg σ 10) (getReg σ 11) (getReg σ 12) mem).bind (applyEffect σ))
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
