import Airbender.Proofs.Blake2Round.Control
import Airbender.Proofs.Blake2Round.Lookups
import Airbender.Proofs.Blake2Round.Addresses
import Airbender.Proofs.Blake2Round.Preparation
import Airbender.Proofs.Blake2Round.Schedule
import Airbender.Proofs.Blake2Round.Soundness
import Airbender.Proofs.Blake2Round.Finalization
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

namespace Airbender.Blake2Round.Schedule

/-- The sixteen G inputs follow the shared SIGMA schedule, under the caller's
    exclusive round mask. This condition is not derived from the local circuit. -/
theorem soundness {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 4)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := soundness setup

end Airbender.Blake2Round.Schedule

namespace Airbender.Blake2Round.Mixing

/-- All eight G calls and the allocated extended-state writeback agree with
    Clean's round. Only the stated addition-input and message bounds are assumed. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.mixing_soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide)

end Airbender.Blake2Round.Mixing

namespace Airbender.Blake2Round.Finalization

/-- All eight chaining writes match final three-way XOR or non-final preservation.
    The caller supplies the round mask; queries derive all final-XOR bounds. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.finalization_soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (InterfaceAssumptions (p := babyBearModulus)) spec := soundness (by decide) (by decide)

/-- Non-final rounds preserve all eight original chaining-state words.
    The final-XOR flag is derived from the round mask and reduction mode. -/
theorem nonfinal_soundness {p : Nat} [Fact p.Prime] :
    (circuitModel (p := p)).SoundnessUnder (NonFinalAssumptions (p := p)) spec :=
  Proofs.nonfinal_soundness

theorem babyBear_nonfinal_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (NonFinalAssumptions (p := babyBearModulus)) spec := nonfinal_soundness

end Airbender.Blake2Round.Finalization
