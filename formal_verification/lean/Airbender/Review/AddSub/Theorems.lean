import Airbender.Review.AddSub.Model
import Airbender.Proofs.AddSub
import Airbender.Proofs.BabyBear

namespace Airbender.AddSub
open Airbender.Reference.RiscV

/-- Any satisfying assignment with the stated interfaces agrees with Sail's execution.
    Covers ADD/ADDI/SUB destination writes; PC sequencing is a later obligation. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  Proofs.soundness hp

/-- Concrete instance for the imported BabyBear artifact. -/
theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  soundness (p := babyBearModulus) (by decide)

end Airbender.AddSub
