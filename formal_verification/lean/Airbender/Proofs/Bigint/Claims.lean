import Airbender.Proofs.Bigint.Control
import Airbender.Proofs.Bigint.SetupSoundness
import Airbender.Proofs.Bigint.Multiplication
import Airbender.Proofs.BabyBear
import Airbender.Review.Circuits.Bigint.Theorems
import Airbender.Review.Trace.Workers.Bigint.Theorems

namespace Airbender.Bigint.Control

theorem soundness {p : Nat} [Fact p.Prime] (hp : 256 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    Properties.Soundness (circuitModel setup).relation spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 3)) :
    Properties.Soundness (circuitModel setup).relation spec := soundness (by decide) setup

end Airbender.Bigint.Control

namespace Airbender.Bigint.Additive

theorem soundness {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := soundness (by decide) setup

theorem modeled_soundness {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p) :
    Properties.Soundness (circuitModel (setupTable (p := p))).relation spec := Proofs.modeled_soundness hp

theorem modeled_babyBear_soundness :
    Properties.Soundness (circuitModel (setupTable (p := babyBearModulus))).relation spec :=
  modeled_soundness (by decide)

end Airbender.Bigint.Additive

namespace Airbender.Bigint.Equality

theorem soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := soundness (by decide) setup

theorem modeled_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p) :
    Properties.Soundness (circuitModel (setupTable (p := p))).relation spec := Proofs.modeled_soundness hp

theorem modeled_babyBear_soundness :
    Properties.Soundness (circuitModel (setupTable (p := babyBearModulus))).relation spec :=
  modeled_soundness (by decide)

end Airbender.Bigint.Equality

namespace Airbender.Bigint.Multiplication

theorem soundness :
    Properties.Soundness (circuitModel (p := babyBearModulus)).relation spec := Proofs.soundness

end Airbender.Bigint.Multiplication

namespace Airbender.Bigint.Addresses

theorem soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness (by decide) (by decide)

end Airbender.Bigint.Addresses

namespace Airbender.Bigint.Memory

theorem native_value_bounds [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : Inputs data before cells) :
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (Trace.readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (row.writeToken port).word.Bounded) ∧
    (∀ token ∈ data.terminal, token.word.Bounded) := Proofs.value_bounds hp accepted inputs

end Airbender.Bigint.Memory
