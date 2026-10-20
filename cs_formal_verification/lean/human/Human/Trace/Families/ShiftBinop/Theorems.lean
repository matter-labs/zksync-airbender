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

-- The statements proven in slop/Slop/Final/Trace/Families/ShiftBinop/Theorems.lean (checked by verify.sh).

namespace Airbender.ShiftBinop

/-- Publicly fetched bitwise/shift/REV8 instructions execute in native time
    order and reach the terminal PC and cell values. All per-row interfaces are
    derived; public initialization and logical matching/membership remain explicit. -/
def TraceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {program : List ProgramEntry} (inputs : ExecutionBoundary trace initial cells program) (accepted : Trace.Accepted trace) (decoded : Decoded trace program),
    Trace.Realizes (SailStep program) trace initial cells

end Airbender.ShiftBinop
