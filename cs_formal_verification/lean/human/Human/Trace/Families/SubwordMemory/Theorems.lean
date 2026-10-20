import Human.Circuits.AddSub.Reference
import Human.Circuits.JumpBranchSlt.Model
import Human.Circuits.ShiftBinop.Model
import Human.Circuits.SubwordMemory.Model
import Human.Helpers.Context.Registries.JumpBranchSlt
import Human.Helpers.Context.Registries.MulDiv
import Human.Helpers.Context.Registries.ShiftBinop
import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Memory.SailHistory
import Human.Trace.Families.SubwordMemory.Execution

-- The statements proven in slop/Slop/Final/Trace/Families/SubwordMemory/Theorems.lean (checked by verify.sh).

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem

/-- RAM LB/LBU/LH/LHU/SB/SH execute the public program in native time order
    and reach its terminal PC and cell values. Global history supplies all input
    bounds and reads; the public boundary contains no per-row assumptions. -/
def RamTraceSoundnessClaim : Prop :=
  ∀ [MemoryPlatform SailRV32.exception] {p : Nat} [Fact p.Prime] (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {program : List ProgramEntry} (inputs : RAMInputs trace initial cells program) (accepted : Trace.Accepted trace) (decoded : Decoded trace program),
    Trace.Realizes (SailStep program) trace initial cells

end Airbender.SubwordMemory
