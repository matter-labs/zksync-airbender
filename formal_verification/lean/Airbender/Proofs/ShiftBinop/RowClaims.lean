import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.ShiftBinop.Soundness
import Airbender.Proofs.BabyBear

namespace Airbender.ShiftBinop

/-- XOR/OR/AND, SLL/SRL/SRA (including immediate forms), and REV8, against Sail execution and
    native register/PC effects. Lookups force all operand/result bytes. -/
theorem row_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 262144)
    (inverse : SerializedInverse.Limb16 p) :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := p)) spec :=
  Proofs.soundness hp inverse

theorem babyBear_row_soundness :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := babyBearModulus)) spec :=
  row_soundness (by decide) (by decide)

end Airbender.ShiftBinop
