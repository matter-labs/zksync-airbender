import Slop.WordMemory.Soundness
import Slop.BabyBear

namespace Airbender.WordMemory
open _root_.Sail.ArchSem


/-- LW (RAM/ROM) and SW satisfy shared native Sail soundness: effective address,
    transferred data, GPR effects and PC+4. Native memory transport, input/port
    bounds and the program table's pre-state binding remain explicit interfaces. -/
theorem row_soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) (rom : Table (ZMod p) (fields 9)) :
    (rowCircuitModel rom).SoundnessUnder (RowInterfaces rom) spec :=
  Proofs.soundness hp inverse rom

theorem babyBear_row_soundness (rom : Table (ZMod babyBearModulus) (fields 9)) :
    (rowCircuitModel rom).SoundnessUnder (RowInterfaces rom) spec :=
  row_soundness (by decide) (by decide) rom

end Airbender.WordMemory
