import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.MulDiv
import Airbender.Proofs.MulDiv.Soundness
import Airbender.Proofs.MulDiv.Product
import Airbender.Proofs.MulDiv.Trace
import Airbender.Proofs.MulDiv.Decoder
import Airbender.Proofs.MulDiv.Composition
import Airbender.Proofs.BabyBear
import Airbender.Proofs.MulDiv.TraceSoundness
import Airbender.Proofs.MulDiv.RowClaims

namespace Airbender.MulDiv


/-- Publicly fetched MUL/MULHU/DIVU/REMU instructions execute in native time
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

end Airbender.MulDiv
