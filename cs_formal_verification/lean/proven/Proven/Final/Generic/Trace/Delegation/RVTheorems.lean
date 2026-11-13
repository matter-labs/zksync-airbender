module
public import Human.Trace.Delegation.RVTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/Delegation/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Delegation
def RVOperationMemorySoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : MemoryData p} {before : RV.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (_accepted : MemoryAccepted data) (_inputs : RVOperationInputs data before cells control),
    MemorySoundness data ∧ WordBounds data

end Airbender.Delegation
