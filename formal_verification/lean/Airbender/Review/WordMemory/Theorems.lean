import Airbender.Proofs.WordMemory.Soundness
import Airbender.Proofs.BabyBear

namespace Airbender.WordMemory
open _root_.Sail.ArchSem

variable [MemoryPlatform SailRV32.exception]

/-- RAM LW/SW satisfy the shared native Sail soundness property: effective
    address, loaded/stored data, GPR effects and PC+4. Native memory transport,
    input/port bounds and disabled ROM-table behavior remain explicit interfaces. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) (rom : Table (ZMod p) (fields 9)) :
    (circuitModel rom).SoundnessUnder (InterfaceAssumptions rom) spec :=
  Proofs.soundness hp inverse rom

theorem babyBear_soundness (rom : Table (ZMod babyBearModulus) (fields 9)) :
    (circuitModel rom).SoundnessUnder (InterfaceAssumptions rom) spec :=
  soundness (by decide) (by decide) rom

end Airbender.WordMemory
