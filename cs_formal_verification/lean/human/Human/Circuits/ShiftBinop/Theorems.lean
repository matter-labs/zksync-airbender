import Human.Circuits.ShiftBinop.Model
import Human.Helpers.Core.BabyBearPrime

-- The statements proven in slop/Slop/Final/Circuits/ShiftBinop/Theorems.lean (checked by verify.sh).

namespace Airbender.ShiftBinop

/-- Original Sail bitwise, shift and REV8 execution, with register and PC effects.
    Shared initialized history discharges all local range/read/decoder interfaces. -/
def SoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

def BabyBearSoundnessClaim : Prop :=
  ∀ [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

end Airbender.ShiftBinop
