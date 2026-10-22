import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.SubwordMemory.RowClaims
import Airbender.Proofs.SubwordMemory.TraceSoundness
import Airbender.Proofs.BabyBear
import Airbender.Proofs.SubwordMemory.Trace

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Original Sail subword loads/stores, aligned cell address, merged/register
    writes and PC effects. Shared history supplies all local ranges and reads. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeWordCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  Proofs.pooled_row_soundness hp clockInverse trace initial cells program

theorem babyBear_soundness (trace : Trace.PooledTrace babyBearModulus)
    (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell)
    (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.SubwordMemory
