import Slop.MulDiv.Soundness
import Slop.BabyBear
namespace Airbender.MulDiv
/-- MUL/MULHU/DIVU/REMU, including zero divisor, proved against original Sail execution plus
    native register/PC effects. Decoder/state interfaces remain explicit. -/
theorem row_soundness {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := p)) spec :=
  Proofs.soundness hp inverse

theorem babyBear_row_soundness :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := babyBearModulus)) spec :=
  row_soundness (by decide) (by decide)

end Airbender.MulDiv
