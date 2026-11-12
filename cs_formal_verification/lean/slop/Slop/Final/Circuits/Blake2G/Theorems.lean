module
public import Slop.Blake2G.Soundness
public import Slop.Final.Generic.Circuits.Blake2G.Theorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.Blake2G

/-- Imported G mixing agrees with Clean's reference, under the four documented
    input bounds. This does not assert control, address or memory-transport soundness. -/
private theorem soundness_generic {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := p) control).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp compatible control

theorem soundness : Airbender.Blake2G.SoundnessClaim := by babybear_instance soundness_generic

end Airbender.Blake2G
