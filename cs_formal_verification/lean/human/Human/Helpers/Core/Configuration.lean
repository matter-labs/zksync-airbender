import SailRV32
import Human.ISA.State

/-! # The Airbender machine's public configuration

The same definition as the verifier branch's `HumanSail/Airbender.lean` (`misa`, `memoryMap`, `resetState`,
`writtenByProgram`), on the simple Sail state `SailState` (every register, byte-addressed memory, cycle counter) that `runSail`
interprets Sail's effects on.

A state of the Airbender machine behaves as Sail with these register values: Sail's own reset (with
`sail/config/airbender-base.json`), `misa` = RV32 I + M (Airbender has no `misa` CSR; this value selects the
decoded extensions) and Airbender's memory map. Everything a program cannot change (privilege, `misa`, `mstatus`,
`mseccfg`, the landing-pad state `elp`, the PMP/PMA registers, …) keeps that value (`Configured`,
`Human/ISA/Sail/Airbender.lean`). -/

namespace Airbender.Reference.RiscV.Sail.Configuration
open _root_.Sail _root_.Sail.ArchSem SailRV32 SailRV32.Functions

/-- All Sail registers, byte-addressed physical memory and the cycle counter. -/
structure SailState where
  /-- The value of every Sail register. -/
  regs : (r : Register) → RegisterType r
  /-- The byte at every physical address. -/
  mem  : Nat → BitVec 8
  /-- The cycle counter: `clockCycle` increments it and `getCycleCount` reads it. -/
  cycles : Nat

/-- Set register `r` to `value`. -/
def SailState.set (σ : SailState) (r : Register) (value : RegisterType r) : SailState :=
  { σ with regs := fun r' => if h : r = r' then h ▸ value else σ.regs r' }

abbrev SailStateM := EStateM (Sail.Error exception) SailState

/-- The `numBytes` bytes at `addr`, little-endian. -/
def readBytes (mem : Nat → BitVec 8) (addr : Nat) : (numBytes : Nat) → BitVec (8 * numBytes)
  | 0 => 0#0
  | n+1 => (by omega : 8 * n + 8 = 8 * (n + 1)) ▸ ((readBytes mem (addr+1) n).append (mem addr))

/-- Memory after writing the `numBytes` bytes of `value` at `addr`, little-endian. -/
def writeBytes (mem : Nat → BitVec 8) (addr : Nat) : (numBytes : Nat) → BitVec (8 * numBytes) → (Nat → BitVec 8)
  | 0, _ => mem
  | n+1, value =>
    let bytes : BitVec (8 + 8 * n) := (by omega : 8 * (n + 1) = 8 + 8 * n) ▸ value
    let restWritten := writeBytes mem (addr+1) n (bytes.extractLsb' 8 (8*n))
    fun a => if a = addr then bytes.extractLsb' 0 8 else restWritten a

/-- The largest memory request in bytes. A request reaches only bytes below `2 ^ 34 + maxRequestBytes`. -/
def maxRequestBytes : Nat := 2 ^ 34

/-- The checks on a memory request. It has no tags, as lean-sail's `interpretSailEffects` requires. It has at most
    `maxRequestBytes` bytes, so it reaches only bytes that an agreeing lean-sail state holds. -/
def checkRequest (req : MemRequest) : SailStateM Unit := do
  if req.numTag != 0 then throw (.Assertion "Tagged memory not supported")
  if maxRequestBytes < req.size then throw (.OutOfMemoryRange req.address.toNat)

/-- How each Sail effect acts on the state, as lean-sail's `interpretSailEffects` does on its hash-map state.
    `RunSailSimulationClaim` (`Human/ISA/Sail/Interpreter.lean`) states the relation. -/
noncomputable def applyEffect : (eff : InstructionEffect) → SailStateM eff.ret
  | .regRead reg _ => do pure ((← get).regs reg)
  | .regWrite reg _ v => modify (·.set reg v)
  | .barrier _ | .cacheOp _ | .tlbOp _ | .translationStart _ | .translationEnd _ | .archException _
  | .returnException | .memWriteAnnounce _ | .printMessage _ => pure ()
  | .clockCycle => modify fun s => { s with cycles := s.cycles + 1 }
  | .getCycleCount => do pure (← get).cycles
  | .memRead req => do
      checkRequest req
      pure (.ok (readBytes (← get).mem req.address.toNat req.size, 0#req.numTag))
  | .memWrite req v _ => do
      checkRequest req
      modify fun s => { s with mem := writeBytes s.mem req.address.toNat req.size v }
      pure (.ok ())

/-- Run a Sail computation. Nondeterministic choices are resolved to the first option. -/
noncomputable def runSail {α} (m : SailM α) (σ : SailState) :
    EStateM.Result (Sail.Error exception) SailState α :=
  (FreeM.liftM (fun
    | .inl (.error err) => throw err
    | .inl (.ok eff) => applyEffect eff
    | .inr (n : Nat) => if h : 0 < n then pure (⟨0, h⟩ : Fin n) else throw .Unreachable) m : SailStateM α).run σ

/-- `misa`: 32-bit, extensions I and M. -/
def misa : BitVec 32 := 0x40001100

/-- A memory region; misaligned accesses fault. -/
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

/-- Memory map: ROM `[0, 2^22)` holds the program (`common_constants/src/rom.rs`), RAM `[2^22, 2^32)` (the
    verifier initialises `MAX_NUM_INIT_WORDS = 2^30` words, `full_statement_verifier/src/unrolled_circuit_params.rs`).
    Nothing else. -/
def memoryMap : List PMA_Region :=
  [ region 0       RV.ROM_END                (readable := true) (writable := false) (executable := true),
    region RV.ROM_END (RV.RAM_END - RV.ROM_END) (readable := true) (writable := true)  (executable := false) ]

/-- Sail's own initialisation and reset (all registers at their defaults, memory 0). -/
noncomputable def sailResetRun :=
  runSail (do sail_model_init (); init_model "")
    { regs := fun r => by cases r <;> exact default, mem := fun _ => 0, cycles := 0 }

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

end Airbender.Reference.RiscV.Sail.Configuration
