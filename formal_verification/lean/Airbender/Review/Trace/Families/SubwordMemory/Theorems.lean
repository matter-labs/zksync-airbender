import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.SubwordMemory.RowClaims
import Airbender.Proofs.SubwordMemory.TraceSoundness
import Airbender.Proofs.BabyBear
import Airbender.Proofs.SubwordMemory.Trace
import Airbender.Proofs.SubwordMemory.Composition

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]


/-- RAM LB/LBU/LH/LHU/SB/SH execute the public program in native time order
    and reach its terminal PC and cell values. Global history supplies all input
    bounds and reads; the public boundary contains no per-row assumptions. -/
theorem ram_trace_soundness {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 33554432) (inverse : SerializedInverse.Clock p)
    {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {program : List ProgramEntry} (inputs : RAMInputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (SailStep program) trace initial cells :=
  Proofs.ram_trace_execution hp inverse inputs accepted decoded

end Airbender.SubwordMemory
