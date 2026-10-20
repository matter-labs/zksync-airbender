import Slop.JumpBranchSlt.RowClaims
import Slop.JumpBranchSlt.TraceSoundness
import Slop.JumpBranchSlt.BranchSoundness
import Slop.JumpBranchSlt.JumpSoundness
import Slop.JumpBranchSlt.PCState
import Slop.JumpBranchSlt.Timestamp
import Slop.JumpBranchSlt.Trace
import Slop.JumpBranchSlt.Decoder
import Slop.JumpBranchSlt.Composition
import Slop.BabyBear

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

end Airbender.JumpBranchSlt
