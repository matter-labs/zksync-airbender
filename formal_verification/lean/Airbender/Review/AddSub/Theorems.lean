import Airbender.Review.AddSub.Model
import Airbender.Proofs.AddSub.TraceSoundness
import Airbender.Proofs.AddSub.RowClaims

namespace Airbender.AddSub
open Reference.RiscV Reference.RiscV.Sail Trace

/-- Every ADD/ADDI/SUB/LUI/AUIPC row in the shared initialized history agrees
    with original Sail execution, including discarded writes and PC retirement.
    The per-circuit assumptions are listed in Model.lean; none are input bounds
    or expected reads. Standalone calculation/custom claims remain regressions. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec :=
  Proofs.trace_soundness hp inverse trace initial cells program

theorem babyBear_soundness (trace : PooledTrace babyBearModulus)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.AddSub
