import Airbender.Proofs.ShiftBinop
import Airbender.Proofs.ShiftBinop.Soundness
import Airbender.Proofs.ShiftBinop.Shifts
import Airbender.Proofs.BabyBear

namespace Airbender.ShiftBinop
/-- XOR/OR/AND, SLL/SRL/SRA (including immediate forms), and REV8, against Sail execution and
    native register/PC effects. Lookups force all operand/result bytes. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp inverse

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide)

end Airbender.ShiftBinop
