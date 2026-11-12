module
public import Human.Circuits.Blake2G.Model
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in proven/Proven/Final/Circuits/Blake2G/Theorems.lean (checked by verify.sh).

namespace Airbender.Blake2G

/-- Imported G mixing agrees with Clean's reference, under the four documented
    input bounds. This does not assert control, address or memory-transport soundness. -/
def SoundnessClaim : Prop :=
  ∀ (control : Fin 512 → Vector Nat 7),
    Properties.Soundness
      (fun input output w => InterfaceAssumptions (p := babyBearModulus) input output w ∧
        (circuitModel (p := babyBearModulus) control).relation input output w) spec

end Airbender.Blake2G
