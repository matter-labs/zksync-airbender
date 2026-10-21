import Human.Circuits.MulDiv.Model
import Human.Helpers.Core.BabyBearPrime

-- The statements proven in slop/Slop/Final/Circuits/MulDiv/Theorems.lean (checked by verify.sh).

namespace Airbender.MulDiv

/-- Every MUL/MULHU/DIVU/REMU row in the shared initialized history agrees
    with original Sail execution and native register/PC effects. Public conditions
    are listed in `Model.lean`; no operand-bound, read or selector premise remains. -/
def SoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

def BabyBearSoundnessClaim : Prop :=
  ∀ (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

end Airbender.MulDiv
