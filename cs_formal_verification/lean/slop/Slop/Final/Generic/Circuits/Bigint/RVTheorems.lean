module
public import Human.Circuits.Bigint.RVTheorems

/-! The generic-prime forms of the claims of `human/Human/Circuits/Bigint/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The slop proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Bigint.Memory
def RVAddressesSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2097152 ≤ p) (_inverse : 32 * (-62914560 : ZMod p) = 1) (data : Delegation.MemoryData p) (before : RV.State) (cells : List Trace.Cell),
    (circuitModel data).SoundnessUnder (RVInterfaceAssumptions data before cells) Addresses.spec

end Airbender.Bigint.Memory
