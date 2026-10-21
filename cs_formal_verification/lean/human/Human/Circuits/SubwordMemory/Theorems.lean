import Human.Circuits.SubwordMemory.Model
import Human.Helpers.Core.BabyBearPrime

-- The statements proven in slop/Slop/Final/Circuits/SubwordMemory/Theorems.lean (checked by verify.sh).

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem

/-- Original Sail subword loads/stores, aligned cell address, merged/register
    writes and PC effects. Shared history supplies all local ranges and reads. -/
def SoundnessClaim : Prop :=
  ∀ [MemoryPlatform SailRV32.exception] {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

def BabyBearSoundnessClaim : Prop :=
  ∀ [MemoryPlatform SailRV32.exception] (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

end Airbender.SubwordMemory
