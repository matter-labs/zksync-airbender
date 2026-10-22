import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.MulDiv.Soundness
import Airbender.Proofs.BabyBear
namespace Airbender.MulDiv
/-- MUL/MULHU/DIVU/REMU, including zero divisor, proved against original Sail execution plus
    native register/PC effects. Decoder/state interfaces remain explicit. -/
theorem row_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeWordCapacity p)
    (inverse : SerializedInverse.Limb16 p) :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := p)) spec :=
  Proofs.soundness hp inverse

theorem babyBear_row_soundness :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := babyBearModulus)) spec :=
  row_soundness (by decide) (by decide)

end Airbender.MulDiv
