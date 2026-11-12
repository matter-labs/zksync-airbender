module
public import Human.Circuits.Blake2G.Model
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in slop/Slop/Final/Circuits/Blake2G/Theorems.lean (checked by verify.sh).

namespace Airbender.Blake2G

/-- Imported G mixing agrees with Clean's reference, under the four documented
    input bounds. This does not assert control, address or memory-transport soundness. -/
def SoundnessClaim : Prop :=
  ∀ (control : Fin 512 → Vector Nat 7),
    (circuitModel (p := babyBearModulus) control).SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec

end Airbender.Blake2G
