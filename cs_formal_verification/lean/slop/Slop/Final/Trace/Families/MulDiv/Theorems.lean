import Slop.MulDiv
import Slop.MulDiv.Soundness
import Slop.MulDiv.Product
import Slop.MulDiv.Trace
import Slop.MulDiv.Decoder
import Slop.MulDiv.Composition
import Slop.BabyBear
import Slop.MulDiv.TraceSoundness
import Slop.MulDiv.RowClaims

namespace Airbender.MulDiv


/-- Publicly fetched MUL/MULHU/DIVU/REMU instructions execute in native time
    order and reach the terminal PC and cell values. All per-row interfaces are
    derived; public initialization and logical matching/membership remain explicit. -/
theorem trace_soundness {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {program : List ProgramEntry} (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (SailStep program) trace initial cells :=
  Proofs.native_trace_execution hp inverse clockInverse inputs accepted decoded

end Airbender.MulDiv
