import Slop.MulDiv
import Slop.MulDiv.Soundness
import Slop.MulDiv.Product
import Slop.MulDiv.Trace
import Slop.MulDiv.Decoder
import Slop.BabyBear
import Slop.MulDiv.TraceSoundness
import Slop.MulDiv.RowClaims

namespace Airbender.MulDiv

/-- Every MUL/MULHU/DIVU/REMU row in the shared initialized history agrees
    with original Sail execution and native register/PC effects. Public conditions
    are listed in `Model.lean`; no operand-bound, read or selector premise remains. -/
theorem soundness {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
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
