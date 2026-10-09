import Airbender.Proofs.JumpBranchSlt.Soundness
import Airbender.Proofs.JumpBranchSlt.BranchSoundness
import Airbender.Proofs.JumpBranchSlt.JumpSoundness
import Airbender.Proofs.JumpBranchSlt.PCState
import Airbender.Proofs.JumpBranchSlt.Timestamp
import Airbender.Proofs.JumpBranchSlt.Trace
import Airbender.Proofs.JumpBranchSlt.Decoder
import Airbender.Proofs.JumpBranchSlt.Composition
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt

/-- Accepted native rows execute their publicly fetched Sail instructions in
    timestamp order and reach the actual terminal PC and register/cell values.
    Public initialization, canonical termination and logical matching/membership
    are the explicit boundaries in `ExecutionBoundary`, `Accepted` and `Decoded`. -/
theorem trace_soundness {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {program : List ProgramEntry} (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    ∃ after, SailTrace program initial after ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after =
        .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Trace.Proofs.memoryWord sink.value) after :=
  Proofs.native_trace_execution hp inverse inputs accepted decoded

/-- Supply the final-PC range premise for this family's local soundness claims.
    The low bound follows from imported lookups; the high bound follows from
    logical state matching and decoder membership, including the terminal boundary. -/
theorem final_pc_bounds {p n : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {context : PCState.Context p n} {w : Nat → ZMod p}
    (global : PCState.Interface context)
    (outgoing : PCState.Outgoing context (w Variables.finalPCLo, w Variables.finalPCHi))
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w Variables.finalPCLo).val < Arithmetic.limbBase ∧
      (w Variables.finalPCHi).val < Arithmetic.limbBase :=
  Proofs.final_pc_bounds hp global outgoing h

/-- Native four-tick advancement and strict prior-write order for all three
    ports. Initial/prior clock bounds remain history interfaces at this stage. -/
theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs

/-- The actual public program image and logical decoder membership bind the
    imported row to Sail's instruction, including its five native selector bits. -/
theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image h member

namespace Comparison

/-- Shared soundness for SLT, SLTI, SLTU and SLTIU against native Sail register
    and PC effects. Alignment and the final-PC high bound are explicit
    interfaces; the imported arithmetic allows 32-bit PC wraparound. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.comparison_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Comparison

namespace Branch

/-- All six standard branches satisfy the shared native Sail state-transition
    property. Taken targets, fall-through and alignment follow from the artifact;
    decoding, input bounds, native reads and the final-PC high bound remain interfaces. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.branch_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Branch

namespace Jump

/-- Native JAL/JALR register and PC soundness, including x0 writes and wrapping
    links. JALR uses the explicit Machine-mode/MLPE-clear configuration interface. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.jump_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Jump

end Airbender.JumpBranchSlt
