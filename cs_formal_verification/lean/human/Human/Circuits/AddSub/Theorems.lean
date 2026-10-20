import Human.Circuits.AddSub.Model
import Human.Circuits.JumpBranchSlt.Model
import Human.Circuits.ShiftBinop.Model
import Human.Helpers.Context.Registries.JumpBranchSlt
import Human.Helpers.Context.Registries.MulDiv
import Human.Helpers.Context.Registries.ShiftBinop
import Human.Helpers.Context.Registries.SubwordMemory
import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Memory.SailHistory

-- The statements proven in slop/Slop/Final/Circuits/AddSub/Theorems.lean (checked by verify.sh).

namespace Airbender.AddSub
open Reference.RiscV Reference.RiscV.Sail Trace

/-- Every ADD/ADDI/SUB/LUI/AUIPC row in the shared initialized history agrees
    with original Sail execution, including discarded writes and PC retirement.
    The per-circuit assumptions are listed in Model.lean; none are input bounds
    or expected reads. Standalone calculation/custom claims remain regressions. -/
def SoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation Sail.spec

def BabyBearSoundnessClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : State) (cells : List Cell) (program : List PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation Sail.spec

end Airbender.AddSub
