import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.AddSub.Model
import Airbender.Proofs.BabyBear
import Airbender.Proofs.AddSub.TraceSoundness

namespace Airbender.AddSub
open Reference.RiscV Reference.RiscV.Sail Trace

/-- Every ADD/ADDI/SUB/LUI/AUIPC row in the shared initialized history agrees
    with original Sail execution, including discarded writes and PC retirement.
    The per-circuit assumptions are listed in Model.lean; none are input bounds
    or expected reads. Standalone calculation/custom claims remain regressions. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Clock p)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation Sail.spec :=
  Proofs.trace_soundness hp inverse trace initial cells program

theorem babyBear_soundness (trace : PooledTrace babyBearModulus)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation Sail.spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.AddSub
