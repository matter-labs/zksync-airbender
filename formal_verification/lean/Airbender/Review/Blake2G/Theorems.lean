import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Blake2G.Control
import Airbender.Proofs.Blake2G.Addresses
import Airbender.Proofs.Blake2G.State
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2G

/-- Imported G mixing agrees with Clean's reference, under the four documented
    input bounds. This does not assert control, address or memory-transport soundness. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := p) control).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp compatible control

theorem babyBear_soundness (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := babyBearModulus) control).SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide) control

namespace Control

/-- The imported controller query enforces the modeled register update and
    all six word indices for active and inactive rows. The eight-bit ABI input
    domain and unproved Rust setup binding are explicit in the model. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) :
    Properties.Soundness (circuitModel (p := p)).relation spec :=
  Proofs.soundness hp

theorem babyBear_soundness :
    Properties.Soundness (circuitModel (p := babyBearModulus)).relation spec :=
  soundness (by decide)

end Control

namespace Addresses

/-- The six addresses described by imported memory metadata select the modeled
    controller's words within the ABI blocks. Pointer bounds and global memory
    transport remain external; alignment and offset bounds are proved locally. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Addresses

namespace State

/-- An active row agrees with Clean's G on all sixteen state words, under
    the explicit port/read/frame interface. Selected lanes are proved distinct
    from the modeled controller; global memory enforcement remains external. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end State

end Airbender.Blake2G
