import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.JumpBranchSlt.RowClaims
import Airbender.Proofs.JumpBranchSlt.TraceSoundness
import Airbender.Proofs.JumpBranchSlt.BranchSoundness
import Airbender.Proofs.JumpBranchSlt.JumpSoundness
import Airbender.Proofs.JumpBranchSlt.PCState
import Airbender.Proofs.JumpBranchSlt.Timestamp
import Airbender.Proofs.JumpBranchSlt.Trace
import Airbender.Proofs.JumpBranchSlt.Decoder
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt


namespace Comparison

/-- Original Sail execution with register/PC effects. Shared history supplies
    local ranges and reads; public conditions remain visible in the model. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeWordCapacity p) (clockInverse : SerializedInverse.Clock p)
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
    (hp : FieldCapacity.NativeWordCapacity p) (clockInverse : SerializedInverse.Clock p)
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
    (hp : FieldCapacity.NativeWordCapacity p) (clockInverse : SerializedInverse.Clock p)
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
