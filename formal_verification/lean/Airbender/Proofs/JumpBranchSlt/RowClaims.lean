import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.JumpBranchSlt.Soundness
import Airbender.Proofs.JumpBranchSlt.BranchSoundness
import Airbender.Proofs.JumpBranchSlt.JumpSoundness
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt

namespace Comparison

theorem row_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p) :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := p)) spec :=
  Proofs.comparison_soundness hp

theorem babyBear_row_soundness :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := babyBearModulus)) spec :=
  row_soundness (by decide)

end Comparison

namespace Branch

theorem row_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p) :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := p)) spec :=
  Proofs.branch_soundness hp

theorem babyBear_row_soundness :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := babyBearModulus)) spec :=
  row_soundness (by decide)

end Branch

namespace Jump

theorem row_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p) :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := p)) spec :=
  Proofs.jump_soundness hp

theorem babyBear_row_soundness :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := babyBearModulus)) spec :=
  row_soundness (by decide)

end Jump

end Airbender.JumpBranchSlt
