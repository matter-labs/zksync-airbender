module
public import Human.Circuits.Blake2G.Theorems

/-! The generic-prime forms of the claims of `human/Human/Circuits/Blake2G/Theorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Blake2G
def SoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 262144 ≤ p) (_compatible : 64 * (-31457280 : ZMod p) = 1) (control : Fin 512 → Vector Nat 7),
    (circuitModel (p := p) control).SoundnessUnder (InterfaceAssumptions (p := p)) spec

end Airbender.Blake2G
