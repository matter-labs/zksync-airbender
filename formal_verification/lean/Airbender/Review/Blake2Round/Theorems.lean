import Airbender.Proofs.Blake2Round.Control
import Airbender.Proofs.Blake2Round.Lookups
import Airbender.Proofs.Blake2Round.Addresses
import Airbender.Proofs.Blake2Round.Preparation
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2Round.Control

/-- x12's thirteen-bit high limb and next mask are forced by the artifact.
    This is a control-word claim; state, addresses and full compression remain open. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 8192 ≤ p)
    (setup : Table (ZMod p) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := soundness (by decide) setup

end Airbender.Blake2Round.Control

namespace Airbender.Blake2Round.Preparation

/-- The imported equations enforce state initialization and left/right message
    preparation for every control combination. G calls and writeback are separate. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (setup : Table (ZMod p) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := soundness (by decide) setup

end Airbender.Blake2Round.Preparation
