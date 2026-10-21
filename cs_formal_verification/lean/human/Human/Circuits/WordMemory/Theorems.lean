import Human.Circuits.WordMemory.Model
import Human.Helpers.Core.BabyBearPrime

-- The statements proven in slop/Slop/Final/Circuits/WordMemory/Theorems.lean (checked by verify.sh).

namespace Airbender.WordMemory
open Reference.RiscV.Sail Trace _root_.Sail.ArchSem

/-- Every LW/SW row in the initialized shared history agrees with original Sail:
    effective address, transferred data, GPR/memory effects and PC retirement.
    Public initialization, modeled tables and platform conditions are listed in
    `Model.lean`; bounds and successful reads/accesses are derived internally. -/
def SoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

def BabyBearSoundnessClaim : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : State) (cells : List Cell) (program : List PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

end Airbender.WordMemory
