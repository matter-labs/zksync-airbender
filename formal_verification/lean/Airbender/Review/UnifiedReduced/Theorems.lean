import Airbender.Proofs.UnifiedReduced.AddSub
import Airbender.Proofs.BabyBear

namespace Airbender.UnifiedReduced
open Airbender.Reference.RiscV

/-- Every satisfying standard arithmetic row agrees with native Sail register
    and PC effects, including aliases and decoder-preprocessed x0 writes.
    The selected operation is a decoder interface; exclusivity is proved locally. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (setup : Table (ZMod p) (fields 10)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions Sail.spec :=
  Proofs.standard_soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 10)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions Sail.spec :=
  soundness (by decide) setup

end Airbender.UnifiedReduced
