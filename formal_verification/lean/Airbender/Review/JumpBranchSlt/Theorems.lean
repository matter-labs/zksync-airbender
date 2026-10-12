import Airbender.Proofs.JumpBranchSlt.RowClaims
import Airbender.Proofs.JumpBranchSlt.TraceSoundness
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
    Trace.Realizes (SailStep program) trace initial cells :=
  Proofs.native_trace_execution hp inverse inputs accepted decoded

namespace Comparison

/-- Original Sail execution with register/PC effects. Shared history supplies
    local ranges and reads; public conditions remain visible in the model. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  Proofs.pooled_comparison_soundness hp clockInverse trace initial cells program

theorem babyBear_soundness
    (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  soundness (by decide) (by decide) trace initial cells program

end Comparison

namespace Branch

/-- Original Sail execution with register/PC effects. Shared history supplies
    local ranges and reads; public conditions remain visible in the model. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  Proofs.pooled_branch_soundness hp clockInverse trace initial cells program

theorem babyBear_soundness
    (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  soundness (by decide) (by decide) trace initial cells program

end Branch

namespace Jump

/-- Original Sail execution with register/PC effects. Shared history supplies
    local ranges and reads; public conditions remain visible in the model. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) spec :=
  Proofs.pooled_jump_soundness hp clockInverse trace initial cells program

theorem babyBear_soundness
    (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) spec :=
  soundness (by decide) (by decide) trace initial cells program

end Jump

end Airbender.JumpBranchSlt
