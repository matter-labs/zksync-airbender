import Airbender.Review.WordMemory.Model
import Airbender.Proofs.WordMemory.TraceSoundness
import Airbender.Proofs.WordMemory.RowClaims

namespace Airbender.WordMemory
open Reference.RiscV.Sail Trace _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Every LW/SW row in the initialized shared history agrees with original Sail:
    effective address, transferred data, GPR/memory effects and PC retirement.
    Public initialization, modeled tables and platform conditions are listed in
    `Model.lean`; bounds and successful reads/accesses are derived internally. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  Proofs.trace_soundness hp inverse trace initial cells program

theorem babyBear_soundness (trace : PooledTrace babyBearModulus)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.WordMemory
