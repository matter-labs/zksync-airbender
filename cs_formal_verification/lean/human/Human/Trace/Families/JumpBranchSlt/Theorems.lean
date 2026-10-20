import Human.Circuits.AddSub.Reference
import Human.Circuits.JumpBranchSlt.Branch
import Human.Circuits.JumpBranchSlt.Jump
import Human.Circuits.MulDiv.Model
import Human.Circuits.ShiftBinop.Model
import Human.Helpers.Context.Registries.SubwordMemory
import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Memory.SailHistory
import Human.Trace.Families.JumpBranchSlt.Execution
import Human.Trace.Families.MulDiv.Execution
import Human.Trace.Families.ShiftBinop.Execution

-- The statements proven in slop/Slop/Final/Trace/Families/JumpBranchSlt/Theorems.lean (checked by verify.sh).

namespace Airbender.JumpBranchSlt

/-- Accepted native rows execute their publicly fetched Sail instructions in
    timestamp order and reach the actual terminal PC and register/cell values.
    Public initialization, canonical termination and logical matching/membership
    are the explicit boundaries in `ExecutionBoundary`, `Accepted` and `Decoded`. -/
def TraceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {program : List ProgramEntry} (inputs : ExecutionBoundary trace initial cells program) (accepted : Trace.Accepted trace) (decoded : Decoded trace program),
    Trace.Realizes (SailStep program) trace initial cells

end Airbender.JumpBranchSlt
