import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2G

/-- Imported G mixing agrees with Clean's reference, under the four documented
    input bounds. This does not assert control, address or memory-transport soundness. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 262144)
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := p) control).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp compatible control

theorem babyBear_soundness (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := babyBearModulus) control).SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide) control

end Airbender.Blake2G
