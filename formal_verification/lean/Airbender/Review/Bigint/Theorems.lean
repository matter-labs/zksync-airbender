import Airbender.Proofs.Bigint.Control
import Airbender.Proofs.Bigint.SetupSoundness
import Airbender.Proofs.Bigint.Multiplication
import Airbender.Proofs.Bigint.Addresses
import Airbender.Proofs.BabyBear

namespace Airbender.Bigint.Control

/-- Eight-bit control decoding, at most one opcode excluding carry, and cleared
    returned high limb. Full arithmetic/memory soundness is not yet covered. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 256 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    Properties.Soundness (circuitModel setup).relation spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 3)) :
    Properties.Soundness (circuitModel setup).relation spec := soundness (by decide) setup

end Airbender.Bigint.Control

namespace Airbender.Bigint.Additive

/-- The selected custom ADD/SUB/reversed-SUB/copy clause holds for the actual
    written 256-bit value and returned carry/borrow. Input ranges are external;
    result bounds, exclusivity and all carry bits follow from the imported row. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := soundness (by decide) setup

/-- With the modeled production table, native low-byte queries establish the
    source ranges. There are no additional interface assumptions in this claim. -/
theorem modeled_soundness {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p) :
    Properties.Soundness (circuitModel (setupTable (p := p))).relation spec := Proofs.modeled_soundness hp

theorem modeled_babyBear_soundness :
    Properties.Soundness (circuitModel (setupTable (p := babyBearModulus))).relation spec :=
  modeled_soundness (by decide)

end Airbender.Bigint.Additive

namespace Airbender.Bigint.Equality

/-- The selected EQ branch preserves the written operand and returns a correct
    equality Boolean for both incoming carry values. Only input ranges remain
    external; no fixed-table behavior is assumed. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := soundness (by decide) setup

/-- Equality with the modeled production table needs no source-range premise. -/
theorem modeled_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p) :
    Properties.Soundness (circuitModel (setupTable (p := p))).relation spec := Proofs.modeled_soundness hp

theorem modeled_babyBear_soundness :
    Properties.Soundness (circuitModel (setupTable (p := babyBearModulus))).relation spec :=
  modeled_soundness (by decide)

end Airbender.Bigint.Equality

namespace Airbender.Bigint.Multiplication

/-- Both product halves and the low-product overflow response follow from the
    imported row and modeled setup. No additional range/carry assumptions.
    The serialized inverse in this artifact is specific to BabyBear. -/
theorem soundness :
    Properties.Soundness (circuitModel (p := babyBearModulus)).relation spec := Proofs.soundness

end Airbender.Bigint.Multiplication

namespace Airbender.Bigint.Addresses

/-- Native ports address all eight words of both aligned 256-bit blocks.
    Pointer limb bounds remain external; alignment follows from the row.
    This does not establish the global memory or request/response argument. -/
theorem soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness (by decide) (by decide)

end Airbender.Bigint.Addresses
