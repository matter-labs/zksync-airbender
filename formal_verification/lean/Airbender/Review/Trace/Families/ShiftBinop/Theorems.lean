import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
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
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Limb16 p)
    (clockInverse : SerializedInverse.Clock p)
    {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {program : List ProgramEntry} (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (SailStep program) trace initial cells :=
  Proofs.native_trace_execution hp inverse clockInverse inputs accepted decoded

end Airbender.ShiftBinop
