import Airbender.Proofs.UnifiedReduced.Delegation
import Airbender.Proofs.UnifiedReduced.RequestTrace
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.MixedRetirement
import Airbender.Proofs.UnifiedReduced.MixedCustomRetirement
import Airbender.Proofs.UnifiedReduced.MixedBinaryRetirement
import Airbender.Proofs.UnifiedReduced.MixedComparisonRetirement
import Airbender.Proofs.UnifiedReduced.MixedControlRetirement
import Airbender.Proofs.UnifiedReduced.MixedComposition
import Airbender.Proofs.UnifiedReduced.MixedHistory
import Airbender.Proofs.UnifiedReduced.CustomHistory
import Airbender.Proofs.UnifiedReduced.CustomComposition
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
import Airbender.Proofs.UnifiedReduced.XorRotateNative
import Airbender.Proofs.UnifiedReduced.Trace
import Airbender.Proofs.UnifiedReduced.Values
import Airbender.Proofs.UnifiedReduced.History
import Airbender.Proofs.UnifiedReduced.Decoder
import Airbender.Proofs.BabyBear

namespace Airbender.UnifiedReduced

/-- Standard instructions and project TRIADD/XORROT retire in one trace, with
    their original public Sail decoding and shared initialized history. Final
    PC/cells agree with native terminal tokens; readonly ROM uses actual public
    bytes rather than zero shadow slots. `Mixed.Inputs` contains only the shared
    public boot/configuration/profile conditions. No row reads, bounds, decoded
    results or expected outputs are assumptions. Delegation callers are outside
    this registry. -/
theorem Mixed.execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Mixed.Inputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Mixed.Step program) trace initial cells (Trace.ROMView.token initial) :=
  Mixed.Proofs.trace_execution hp clockInverse byteInverse inputs accepted decoded

/-- Standard and project MOP rows share one public Sail-decoded program and
    one initialized native history. Imported equations/membership prove x0
    preservation and actual grouped accesses, including dependencies between
    these instruction kinds. This is physical-image memory transport; boot ROM
    shadows and whole mixed retirement remain separate connections. -/
theorem Mixed.native_memory_execution [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Trace.NativeInputs Mixed.decoderFields trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    MemoryExecution trace initial cells :=
  Mixed.Proofs.memory_execution hp inverse accepted inputs decoded

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

/-- All four project XORROT modes agree with actual Sail register and PC
    retirement. Original decoding fixes the operation; initialized history and
    modeled lookups derive every read, range, selector and destination word. -/
theorem XorRotate.soundness [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (XorRotate.circuitModel trace initial cells program).SoundnessUnder
      (XorRotate.InterfaceAssumptions trace initial cells program) XorRotate.spec :=
  Proofs.native_xorrot_soundness hp clockInverse byteInverse trace initial cells program

theorem XorRotate.babyBear_soundness (trace : Trace.UnifiedTrace babyBearModulus)
    (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry) :
    (XorRotate.circuitModel trace initial cells program).SoundnessUnder
      (XorRotate.InterfaceAssumptions trace initial cells program) XorRotate.spec :=
  XorRotate.soundness (by decide) (by decide) (by decide) trace initial cells program

/-- A TRIADD/XORROT trace executes the pinned project clauses after original
    Sail fetch/decoding, in native history-derived order. Actual register reads,
    word bounds, intermediate states and terminal PC/cells are conclusions.
    `Custom.Inputs` lists only public initialization/code/clocks and modeled tables. -/
theorem Custom.execution_soundness [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Custom.Inputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Custom.Step program) trace initial cells :=
  Proofs.custom_trace_execution hp clockInverse byteInverse inputs accepted decoded

theorem Custom.babyBear_execution_soundness
    {trace : Trace.UnifiedTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Custom.Inputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Custom.Step program) trace initial cells :=
  Custom.execution_soundness (by decide) (by decide) (by decide) inputs accepted decoded

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

/-- Actual public caller bytes bind the unified circuit's full CSR request,
    native virtual tokens, x0 destination and Sail PC/register effects. The
    imported equations derive activity and selectors. Shared worker matching
    and unified caller/worker trace composition remain separate. -/
theorem Caller.soundness [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List Caller.ProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (image : Caller.programImage before addresses = some program)
    (member : (Caller.decoderTable program).Contains #[] (decoderQuery w)) : Caller.Binding w before program :=
  Caller.Proofs.caller_binding hp constraints image member

/-- Bind the actual unified caller/worker pool through original public decoding
    and native clocks. Each issued worker is unique and writes inside its caller
    cycle; unissued zero-clock workers remain explicit. Architectural memory and
    whole-call retirement are separate remaining connections. -/
theorem Caller.request_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : Caller.RequestChecks data) (inputs : Caller.RequestInputs data before addresses) :
    Caller.RequestBinding data before := Caller.Proofs.request_binding hp inverse accepted inputs

/-- Unified standard/custom instructions, callers and workers share one public
    initialized architecture. Reads, word/address bounds, x0 values and worker
    references are derived through Clean history and actual Sail transfers.
    Whole retirement, native ROM shadows and hash spans remain separate. -/
theorem Caller.mixed_memory_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells) : Caller.MixedMemoryEffects data before cells :=
  Caller.Proofs.mixed_memory_effects accepted inputs

/-- ADD/ADDI/SUB/LUI/AUIPC retire in the actual joint machine/worker history.
    `words` identifies the imported columns and `instruction` the original public
    entry. Source cells must exist in public initialization, including sources
    erased by x0 preprocessing; no values or ranges are supplied. Cycle states
    and reads are derived. `input.before` is replaced by that actual pre-state.
    This is clause retirement; current-state fetch and whole mixed composition
    remain separate from the public-image decoder binding. -/
theorem Caller.arithmetic_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus} {input : Reference.RiscV.Sail.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (registers : ∀ index, input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Trace.Cell.register index ∈ cells)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = arithmeticInstruction input) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.Proofs.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (Reference.RiscV.Sail.execution input) :=
  Caller.Proofs.mixed_arithmetic_cycle accepted inputs started member words registers instruction

/-- TRIADD and all four XORROT modes retire in the actual shared worker history.
    The entry and query identify original public decoding; `supported` selects
    an admitted project clause. Native word mappings, reads, ranges, old rd and
    cycle states are derived internally. The reference is the pinned project
    operation with Sail register/PC effects. Current-state fetch and whole mixed
    composition remain separate. -/
theorem Caller.custom_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    {entry : UnifiedReduced.ProgramEntry} (present : entry ∈ program)
    (query : decoderQuery w = entry.query) (supported : Custom.clauseFor entry.instruction ≠ none) :
    ∃ events finalState clause,
      Custom.clauseFor entry.instruction = some clause ∧
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.Proofs.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) clause :=
  Caller.Proofs.mixed_custom_cycle accepted inputs started member present query supported

/-- Standard XOR/OR/AND, their immediates, all shifts and REV8 retire in the
    actual machine/worker history. `shift` chooses the represented family;
    `instruction` ties that choice to original public Sail decoding. The named
    word mapping identifies observations, and history/lookups derive every read,
    range, byte interpretation and shift amount. The actual cycle pre-state
    replaces `input.before`. Current-state fetch and whole mixed composition
    remain separate. -/
theorem Caller.binary_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value) (shift : Bool)
    {w : Nat → ZMod babyBearModulus} {input : Binary.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : Binary.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      (if shift then Shift.instruction input else Binary.instruction input) = some entry.instruction) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.Proofs.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (ShiftBinop.execution input) :=
  Caller.Proofs.mixed_binary_cycle accepted inputs started shift member words instruction

/-- SLT/SLTU and their immediates retire in the same initialized worker history.
    The public instruction is four-byte aligned and uses original Sail decoding.
    The named words identify observations; both operands, their ranges, the
    comparison result and the actual cycle states follow from matching/lookups.
    `input.before` is replaced by the derived pre-state. Current-state fetch and
    whole mixed composition remain separate. -/
theorem Caller.comparison_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus} {input : Control.Comparison.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Comparison.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Control.Comparison.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.Proofs.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (JumpBranchSlt.Comparison.execution input) :=
  Caller.Proofs.mixed_comparison_cycle accepted inputs started member words instruction

/-- All six branches retire in the actual shared worker history. Original public
    Sail decoding fixes the condition/offset; history derives both operands and
    transports public `misa`. Instruction alignment stays explicit. No branch
    decision, target, range or intermediate state is assumed.
    Current-state fetch and whole mixed composition remain separate. -/
theorem Caller.branch_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Control.Branch.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Branch.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Control.Branch.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.Proofs.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (JumpBranchSlt.Branch.execution input) :=
  Caller.Proofs.mixed_branch_cycle accepted inputs started isa member words instruction

/-- JAL/JALR retire in the actual shared worker history. Original public decoding
    fixes the instruction; history supplies the source, link, target and ranges.
    Only public `misa`, instruction alignment and JALR Machine/MLPE-clear
    configuration are required. No target or intermediate state is assumed.
    Current-state fetch and whole mixed composition remain separate. -/
theorem Caller.jump_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Jump.Input}
    (landingPad : input.instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, initial.regs.get? .mseccfg = some security ∧
          SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : Jump.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Jump.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.Proofs.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (JumpBranchSlt.Jump.execution input) :=
  Caller.Proofs.mixed_jump_cycle accepted inputs started isa landingPad member words instruction

end Airbender.UnifiedReduced
