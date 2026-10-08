import Airbender.Proofs.Bigint.Control
import Airbender.Proofs.Bigint.Additive
import Airbender.Proofs.Bigint.Equality
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

end Airbender.Bigint.Equality
