import Airbender.Proofs.ShiftBinop
import Airbender.Proofs.ShiftBinop.RowClaims
import Airbender.Proofs.ShiftBinop.TraceSoundness
import Airbender.Proofs.ShiftBinop.Shifts
import Airbender.Proofs.ShiftBinop.Trace
import Airbender.Proofs.ShiftBinop.Decoder
import Airbender.Proofs.ShiftBinop.Composition
import Airbender.Proofs.BabyBear

namespace Airbender.ShiftBinop

/-- Publicly fetched bitwise/shift/REV8 instructions execute in native time
    order and reach the terminal PC and cell values. All per-row interfaces are
    derived; public initialization and logical matching/membership remain explicit. -/
theorem trace_soundness {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {program : List ProgramEntry} (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (SailStep program) trace initial cells :=
  Proofs.native_trace_execution hp inverse clockInverse inputs accepted decoded


/-- Public bytes are decoded by original Sail and bind the native decoder query
    and both selectors. Register reads are proved separately from memory history. -/
theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image h member

/-- Native four-tick advancement and all strict prior-write comparisons.
    The shared history engine derives these clock inputs from matching. -/
theorem clocks {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs

/-- Original Sail bitwise, shift and REV8 execution, with register and PC effects.
    Shared initialized history discharges all local range/read/decoder interfaces. -/
theorem soundness {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) spec :=
  Proofs.pooled_row_soundness hp clockInverse trace initial cells program

theorem babyBear_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.ShiftBinop
