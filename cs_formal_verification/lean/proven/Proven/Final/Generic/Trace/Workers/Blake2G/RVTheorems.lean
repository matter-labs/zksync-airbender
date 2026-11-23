module
public import Human.Trace.Workers.Blake2G.RVTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/Workers/Blake2G/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Blake2G
def Native.RVWorkvectorSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell} {reduced : Bool} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVCallInputs data initial cells reduced) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length)))

def Native.RVWorkvectorBoundarySoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell} {reduced : Bool} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVNativeCallInputs data initial cells reduced) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length)))

def Native.RVWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell} {reduced : Bool} {lower upper : Nat} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVWindowInputs data before cells reduced lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.Caller.RVWindowResult (RVSpanResult reduced) data before cells lower upper

end Airbender.Blake2G
namespace Airbender.Blake2G.Native
def RVOperationExecutionClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (_accepted : Delegation.MemoryAccepted data) (_inputs : Delegation.RVOperationInputs data before cells control) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment)

end Airbender.Blake2G.Native
