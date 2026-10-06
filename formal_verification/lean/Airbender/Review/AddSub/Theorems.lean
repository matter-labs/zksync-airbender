import Airbender.Review.AddSub.Model
import Airbender.Proofs.AddSub
import Airbender.Proofs.BabyBear

namespace Airbender.AddSub
open Airbender.Reference.RiscV

/-- Any satisfying assignment with the stated interfaces agrees with Sail's execution.
    Covers ADD/ADDI/SUB destination writes; PC sequencing is a later obligation. -/
theorem soundness {F : Type} [FiniteField F] {p : Nat} [CharP F p]
    (hp : 196608 < p) :
    (circuitModel (F := F)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  Proofs.soundness hp

/-- Fixed inputs give a unique output word. Internal witnesses need not be unique. -/
theorem determinism {F : Type} [FiniteField F] {p : Nat} [CharP F p]
    (hp : 196608 < p) :
    (circuitModel (F := F)).DeterminismUnder InterfaceAssumptions :=
  Proofs.determinism hp

/-- Concrete instance for the imported BabyBear artifact. -/
theorem babyBear_soundness :
    (circuitModel (F := ZMod babyBearModulus)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  soundness (p := babyBearModulus) (by decide)

theorem babyBear_determinism :
    (circuitModel (F := ZMod babyBearModulus)).DeterminismUnder InterfaceAssumptions :=
  determinism (p := babyBearModulus) (by decide)

end Airbender.AddSub
