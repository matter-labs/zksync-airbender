/-
# The Airbender machine: the Sail RV32 model, restricted to what Airbender supports.

Every Airbender-specific choice is in this file:
* `misa` and the memory map (set in the state after Sail's reset),
* the supported instructions and CSRs (`Supported`, `NopCSR`),
* what one step is (`step`).
The Sail model itself is generated from sail-riscv's stock RV32 config with only the CLINT and the test
interrupt device removed (sail/config/airbender-base.json), because those sit inside Airbender's RAM.
-/
import Slop.Sail.Machine

open Sail SailRV32 SailRV32.Functions

namespace Human

/-- misa: 32-bit, extensions I and M only. -/
def misa : BitVec 32 := 0x40001100

/-- A memory region in which misaligned accesses fault (Airbender cannot prove them). -/
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

/-- rust/lds/memory.x: ROM [0, 2M) holds the program, RAM [2M, 1G) the stack. Nothing else exists. -/
def RAM_START : Nat := 0x200000
def RAM_END   : Nat := 0x40000000
def memoryMap : List PMA_Region :=
  [ region 0         RAM_START               (readable := true) (writable := false) (executable := true),
    region RAM_START (RAM_END - RAM_START)   (readable := true) (writable := true)  (executable := false) ]

/-- Sail's own initialisation and reset (all registers start at their default, memory at 0). -/
noncomputable def initResult :=
  runF (do sail_model_init (); init_model "") { regs := fun r => by cases r <;> exact default, mem := fun _ => 0 }

/-- The state after reset, with Airbender's `misa` and memory map. -/
noncomputable def stInit : FState :=
  let s := match initResult with | .ok _ s => s | .error _ s => s
  (s.set .misa misa).set .pma_regions memoryMap

/-- RV32IM instructions (Sail's decoder already rejects RV64-only forms such as `ld`). Not supported:
`fence`, `ecall`, `ebreak`, `mret`, `wfi`, every other extension, and CSR instructions other than `NopCSR`. -/
def Supported : instruction → Bool
  | .UTYPE _ | .JAL _ | .JALR _ | .BTYPE _ | .ITYPE _ | .SHIFTIOP _ | .RTYPE _
  | .LOAD _ | .STORE _ | .MUL _ | .DIV _ | .REM _ => true
  | _ => false

/-- Airbender's CSRs, accessed with `csrrw` only: 0x7c0 (input/output oracle), 0x7c7, 0x7ca (precompiles).
For now they do nothing (the instruction is skipped). -/
def NopCSR : instruction → Bool
  | .CSRReg (csr, _, _, .CSRRW) => csr == 0x7c0 || csr == 0x7c7 || csr == 0x7ca
  | _ => false

/-- The instruction at the PC, fetched and decoded by Sail. -/
noncomputable def current (s : FState) : Option instruction :=
  match runF (fetch ()) s with
  | .ok (.F_Base w) _ => match runF (ext_decode w) s with | .ok i _ => some i | _ => none
  | _ => none

/-- One step: a supported instruction is executed by Sail's `try_step`; an Airbender CSR is skipped;
anything else stops the machine (`none`). -/
noncomputable def step (s : FState) : Option FState :=
  match current s with
  | some i =>
    if Supported i then
      match runF (try_step 0 false) s with
      | .ok false s' => some s'
      | _ => none
    else if NopCSR i then
      let pc := s.regs .PC + 4
      some (((s.set .PC pc).set .nextPC pc).set .minstret (s.regs .minstret + 1))
    else none
  | none => none

/-- Registers a program may change: the GPRs, the PC and the retired-instruction counter. -/
def Volatile : Register → Bool
  | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7 | .x8 | .x9 | .x10 | .x11 | .x12 | .x13 | .x14 | .x15
  | .x16 | .x17 | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28
  | .x29 | .x30 | .x31 | .PC | .nextPC | .minstret | .minstret_increment => true
  | _ => false

/-- A sane Airbender machine: every other register (privilege, misa, mstatus, PMAs, ...) is as in `stInit`. -/
def Sys (s : FState) : Prop := ∀ r, Volatile r = false → s.regs r = stInit.regs r

/-- `s` executes one instruction that retires normally (no trap, no fault, not stopped). -/
def Retired (s s' : FState) : Prop :=
  step s = some s' ∧ s'.regs .minstret = s.regs .minstret + 1

/-- `n` consecutive retired instructions lead from `s` to `s'`. -/
inductive Runs : Nat → FState → FState → Prop
  | zero : Runs 0 s s
  | succ : Retired s s₁ → Runs n s₁ s' → Runs (n+1) s s'

end Human
