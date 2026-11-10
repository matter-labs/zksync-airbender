module
public import Human.Trace.Workers.Keccak.RVTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/Workers/Keccak/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The slop proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Keccak
def Native.RVPermutationBoundarySoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_inverse : 256 * (-7864320 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVNativeCallInputs data initial cells) (_tables : data.setup = Delegation.modeledSetup Controller.rows) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.RVWordMapping initial after pointer input output ∧
        Delegation.RVTraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
        ∃ s', RV.calls rvCalls initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * rvCalls.length)))

def Native.RVPermutationSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_inverse : 256 * (-7864320 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVCallInputs data initial cells) (_tables : data.setup = Delegation.modeledSetup Controller.rows) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.RVWordMapping initial after pointer input output ∧
        Delegation.RVTraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
        ∃ s', RV.calls rvCalls initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * rvCalls.length)))

def Native.RVOperationExecutionClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_inverse : 256 * (-7864320 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell} (_accepted : Delegation.MemoryAccepted data) (_inputs : Delegation.RVOperationInputs data before cells Controller.rows) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → Native.RowEffects row.assignment

def Native.RVWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_inverse : 256 * (-7864320 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell} {lower upper : Nat} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVWindowInputs data before cells lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.Caller.RVWindowResult RVSpanResult data before cells lower upper

end Airbender.Keccak
