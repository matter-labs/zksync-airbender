import Airbender.Proofs.UnifiedReduced.CustomHistory
import Airbender.Proofs.UnifiedReduced.Composition
import Airbender.Proofs.UnifiedReduced.BranchSoundness
import Airbender.Proofs.UnifiedReduced.ComparisonSoundness
import Airbender.Proofs.UnifiedReduced.JumpSoundness
import Airbender.Proofs.UnifiedReduced.ROMSoundness
import Airbender.Proofs.UnifiedReduced.ROMData
import Airbender.Proofs.UnifiedReduced.ShiftSoundness
import Airbender.Proofs.UnifiedReduced.BinarySoundness
import Airbender.Proofs.UnifiedReduced.TraceSoundness
import Airbender.Proofs.UnifiedReduced.WordMemorySoundness
import Airbender.Proofs.UnifiedReduced.TriAddNative
import Airbender.Proofs.UnifiedReduced.Trace
import Airbender.Proofs.UnifiedReduced.Values
import Airbender.Proofs.UnifiedReduced.History
import Airbender.Proofs.UnifiedReduced.Decoder
import Airbender.Proofs.BabyBear

namespace Airbender.UnifiedReduced

/-- Custom TRIADD/XORROT fetches use original Sail decoding and native selector
    equations. Shared initialized history realizes their actual GPR/RAM accesses
    and derives word bounds; x0 preservation is proved from decoder metadata.
    This is memory transport. Custom arithmetic retirement/composition is separate. -/
theorem custom_native_memory_execution [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Trace.NativeInputs customDecoderFields trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    MemoryExecution trace initial cells :=
  Proofs.custom_memory_execution hp inverse accepted inputs decoded

/-- Every admitted native row, in its history-derived order, executes the original
    Sail instruction fetched from public bytes. The final PC and all tracked
    cells match the declared terminal tokens; readonly ROM uses its public bytes.
    `ExecutionInputs` lists public boot/configuration/profile conditions. Reads,
    selectors and word bounds are proved internally from the imported artifact,
    modeled tables and logical matching. No terminal-PC normalization is needed. -/
theorem execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : ExecutionInputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Step program) trace initial cells (Trace.ROMView.token initial) :=
  Proofs.trace_execution hp clockInverse byteInverse inputs accepted decoded


/-- All six unified branches agree with original Sail retirement and native PC
    effects. Public initialization, setup, code alignment and readable ISA
    configuration remain visible; history supplies every range and read. -/
theorem Control.Branch.soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Control.Branch.circuitModel trace initial cells program).SoundnessUnder
      (Control.Branch.InterfaceAssumptions trace initial cells program) JumpBranchSlt.Branch.spec :=
  Control.Branch.Proofs.soundness hp inverse trace initial cells program

/-- SLT/SLTI/SLTU/SLTIU agree with original Sail register/PC effects. Initialized
    history supplies operands; public decoding supplies immediate preprocessing.
    Both PC limbs are ranged, so terminal normalization is not a premise. -/
theorem Control.Comparison.soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Control.Comparison.circuitModel trace initial cells program).SoundnessUnder
      (Control.Comparison.InterfaceAssumptions trace initial cells program) JumpBranchSlt.Comparison.spec :=
  Control.Comparison.Proofs.soundness hp inverse trace initial cells program

/-- Native unified memory accesses execute in actual Sail cells from the public
    boot state. Readonly ROM uses public physical bytes while native permutation
    tokens remain zero. The proved view preserves constraints, matching, PC and
    decoding; shared history derives every read and bound. Instruction retirement
    is a separate claim. `BootInputs` lists only public starting-data conditions. -/
theorem native_rom_memory_execution [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (accepted : Trace.Accepted trace) (inputs : BootInputs trace initial cells program)
    (decoded : Decoded trace program) : MemoryExecution (ROMView.data initial trace) initial cells :=
  ROMView.memory_execution hp inverse accepted inputs decoded

/-- Unified LW/SW, including ROM loads, agree with original Sail memory,
    register and PC effects. The public boot/table/platform interface contains
    no operand ranges or expected reads; shared history and ROM queries supply
    them. `WordMemory.NativeROM` reuses the existing named word mapping. -/
theorem WordMemory.NativeROM.soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (WordMemory.NativeROM.circuitModel trace initial cells program).SoundnessUnder
      (WordMemory.NativeROM.InterfaceAssumptions trace initial cells program) Airbender.WordMemory.spec :=
  WordMemory.NativeROM.Proofs.soundness hp inverse trace initial cells program

/-- Unified RAM LW/SW agree with the original Sail instruction and native
    register/memory/PC effects. Shared initialized history derives all ranges,
    reads and effective addresses. The visible interface selects public RAM
    initialization/configuration and excludes discarded LW writes. -/
theorem WordMemory.soundness [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (WordMemory.circuitModel trace initial cells program).SoundnessUnder
      (WordMemory.InterfaceAssumptions trace initial cells program) Airbender.WordMemory.spec :=
  WordMemory.Proofs.soundness hp inverse trace initial cells program
/-- Unified XOR/OR/AND and XORI/ORI/ANDI agree with original Sail retirement and native
    register/PC effects. Initialization and the modeled pooled setup remain
    visible; shared history/decoding derive reads, ranges and byte preprocessing. -/
theorem Binary.soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Binary.circuitModel trace initial cells program).SoundnessUnder
      (Binary.InterfaceAssumptions trace initial cells program) ShiftBinop.spec :=
  Binary.Proofs.soundness hp clockInverse byteInverse trace initial cells program

/-- Unified JAL/JALR agree with original Sail link, target and retirement effects.
    Initialized history derives source reads and ranges; public decoding derives
    selectors, offset parity and the x0 mask. The unified artifact ranges both
    final PC limbs, so this claim needs no terminal-PC normalization premise. -/
theorem Jump.soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Jump.circuitModel trace initial cells program).SoundnessUnder
      (Jump.InterfaceAssumptions trace initial cells program) JumpBranchSlt.Jump.spec :=
  Jump.Proofs.soundness hp inverse trace initial cells program

/-- Unified shifts and REV8 agree with original Sail register/PC effects.
    The same initialized history derives source bounds and x0 reads. Original
    decoding and native byte/truncation queries derive the amount internally. -/
theorem Shift.soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Shift.circuitModel trace initial cells program).SoundnessUnder
      (Shift.InterfaceAssumptions trace initial cells program) ShiftBinop.spec :=
  Shift.Proofs.soundness hp clockInverse byteInverse trace initial cells program

open Airbender.Reference.RiscV

/-- All unified rows advance four ticks and access each cell after its previous
    write. `accepted` checks imported equations and native state/memory matching;
    `boundary` bounds only the public starting clock and seed timestamps.
    Shared history derives every row's clock bounds and alignment internally.
    This covers all selectors; it does not yet prove their instruction semantics. -/
theorem native_clocks {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (boundary : Trace.ClockBoundary trace) :
    ∀ row ∈ trace.rows, Trace.ClockEffects row.columns row.assignment :=
  Trace.Proofs.trace_clocks hp inverse accepted boundary

/-- Every native register/RAM read, write and final token has bounded word limbs.
    `image` reads the public starting Sail cells; `accepted` binds the actual
    imported accesses through logical matching. Local range queries bound fresh
    results, while shared latest-write history supplies copied and incoming values.
    No operand range or expected read is a premise. Instruction/ABI soundness is separate. -/
theorem native_value_bounds {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (clocks : Trace.ClockBoundary trace)
    {before : Sail.State} {cells : List Trace.Cell}
    (image : Trace.initialImage before cells = some trace.initialMemory) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (Trace.readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (Trace.writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Proofs.value_bounds hp inverse accepted clocks image

/-- Native accesses form a Clean-consistent latest-write/read history seeded by
    actual public Sail values. `distinct` excludes duplicate public cell entries;
    the circuit supplies ports and clocks, and logical matching links their tokens.
    The conclusion proves read consistency, without an expected-read premise. -/
theorem native_memory_history {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (clocks : Trace.ClockBoundary trace)
    {before : Sail.State} {cells : List Trace.Cell}
    (image : Trace.initialImage before cells = some trace.initialMemory)
    (distinct : cells.Nodup) : ∃ history, Trace.MemoryHistory trace history :=
  Proofs.memory_history hp inverse accepted clocks image distinct

/-- The initialized logical history executes as actual Sail cell reads/writes.
    Public initialization and original decoding supply the starting values and
    x0 rules; native constraints supply clocks and transfers. Expected reads,
    operand ranges and instruction results are not premises. `MemoryExecution`
    states the transport result; original ISA retirement is a separate claim. -/
theorem native_memory_execution [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    {initial : Sail.State} {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Trace.NativeInputs decoderFields trace initial cells program)
    (decoded : Decoded trace program) : MemoryExecution trace initial cells :=
  Proofs.memory_execution hp inverse accepted inputs decoded

/-- The native decoder query comes from public Sail bytes and the original
    decoder. Imported equations recover all nineteen selector bits; no decoded
    opcode, operand value or desired result is supplied as an assumption. -/
theorem fetched {p : Nat} [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    {before : Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (accepted : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (membership : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image accepted membership

/-- Standard arithmetic agrees with the original Sail register and PC effects.
    The per-row model keeps public initialization and program membership visible;
    shared native history derives operand/immediate/PC bounds, actual reads and
    x0 preprocessing. Other admitted selectors may participate in that history. -/
theorem soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.UnifiedTrace p) (initial : Sail.State) (cells : List Trace.Cell)
    (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec :=
  Proofs.trace_soundness hp inverse trace initial cells program

theorem babyBear_soundness (trace : Trace.UnifiedTrace babyBearModulus)
    (initial : Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec :=
  soundness (by decide) (by decide) trace initial cells program

/-- TRIADD follows the pinned project operation and Sail's native register/PC
    effects. Initialized history derives all three operands and their ranges;
    original custom decoding supplies the indices and selected branch. -/
theorem TriAdd.soundness {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (TriAdd.circuitModel trace initial cells program).SoundnessUnder
      (TriAdd.InterfaceAssumptions trace initial cells program) TriAdd.spec :=
  Proofs.native_triadd_soundness hp inverse trace initial cells program

theorem TriAdd.babyBear_soundness (trace : Trace.UnifiedTrace babyBearModulus)
    (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry) :
    (TriAdd.circuitModel trace initial cells program).SoundnessUnder
      (TriAdd.InterfaceAssumptions trace initial cells program) TriAdd.spec :=
  TriAdd.soundness (by decide) (by decide) trace initial cells program

end Airbender.UnifiedReduced
