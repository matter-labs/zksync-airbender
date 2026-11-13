module
public import Human.Trace.Workers.Blake2Round.RVTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/Workers/Blake2Round/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Blake2Round.Native
def RVOperationExecutionClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (_accepted : Delegation.MemoryAccepted data) (_inputs : Delegation.RVOperationInputs data before cells control) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeRound →
        ∃ round, Memory.RoundMask row.assignment round ∧ Row.spec (input round row.assignment) (output row.assignment)

def RVCompressionSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell} {flags : Fin 8} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVCallInputs data initial cells flags) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.RVWordMapping initial after statePointer messagePointer input output message ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output = Compression.run flags input message ∧
        ∃ s', RV.calls (rvCalls flags) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls flags).length)))

def RVCompressionBoundarySoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell} {flags : Fin 8} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVNativeCallInputs data initial cells flags) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.RVWordMapping initial after statePointer messagePointer input output message ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output = Compression.run flags input message ∧
        ∃ s', RV.calls (rvCalls flags) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls flags).length)))

def RVWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell} {flags : Fin 8} {lower upper : Nat} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVWindowInputs data before cells flags lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.Caller.RVWindowResult (RVSpanResult flags) data before cells lower upper

end Airbender.Blake2Round.Native
