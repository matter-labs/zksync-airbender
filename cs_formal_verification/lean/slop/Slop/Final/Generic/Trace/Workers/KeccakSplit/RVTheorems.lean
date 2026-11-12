module
public import Human.Trace.Workers.KeccakSplit.RVTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/Workers/KeccakSplit/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The slop proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Keccak.Split.Native
def RVOperationExecutionClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_inverse : 256 * (-7864320 : ZMod p) = 1) {data : MemoryData p} {before : RV.State} {cells : List Trace.Cell} (_accepted : MemoryAccepted data) (_inputs : RVOperationInputs data before cells) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    RVMemoryExecution data before cells ∧ ∀ row ∈ data.rows, RowEffects row

def RVPermutationSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_inverse : 256 * (-7864320 : ZMod p) = 1) {data : MemoryData p} {initial : RV.State} {cells : List Trace.Cell} (_accepted : MemoryAccepted data) (_inputs : RVCallInputs data initial cells) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (states : Fin 362 → RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      states 0 = initial ∧ (∀ index : Fin 361, Call.RVExecutesAt index (states index.castSucc) (states index.succ)) ∧
      Keccak.Permutation.RVWordMapping initial (states 361) pointer input output ∧
      RVTraceMapping data initial (states 361) cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
      ∃ s', RV.calls RV.f1600Calls initial = some s' ∧
        RV.Same s' ((states 361).setPC (initial.pc + BitVec.ofNat 32 (4 * RV.f1600Calls.length)))

end Airbender.Keccak.Split.Native
