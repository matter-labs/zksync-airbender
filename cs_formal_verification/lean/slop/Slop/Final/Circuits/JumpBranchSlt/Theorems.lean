import Slop.JumpBranchSlt.RowClaims
import Slop.JumpBranchSlt.TraceSoundness
import Slop.JumpBranchSlt.BranchSoundness
import Slop.JumpBranchSlt.JumpSoundness
import Slop.JumpBranchSlt.PCState
import Slop.JumpBranchSlt.Timestamp
import Slop.JumpBranchSlt.Trace
import Slop.JumpBranchSlt.Decoder
import Slop.BabyBear

namespace Airbender.JumpBranchSlt


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
