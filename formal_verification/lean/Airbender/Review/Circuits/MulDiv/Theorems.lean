import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.MulDiv
import Airbender.Proofs.MulDiv.Soundness
import Airbender.Proofs.MulDiv.Product
import Airbender.Proofs.MulDiv.Trace
import Airbender.Proofs.MulDiv.Decoder
import Airbender.Proofs.BabyBear
import Airbender.Proofs.MulDiv.TraceSoundness
import Airbender.Proofs.MulDiv.RowClaims

namespace Airbender.MulDiv

/-- Every MUL/MULHU/DIVU/REMU row in the shared initialized history agrees
    with original Sail execution and native register/PC effects. Public conditions
    are listed in `Model.lean`; no operand-bound, read or selector premise remains. -/
theorem soundness {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Clock p)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  Proofs.pooled_row_soundness hp inverse trace initial cells program

theorem babyBear_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.MulDiv
