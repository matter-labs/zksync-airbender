module
public import Human.Trace.Workers.Blake2Round.RVCall
public import Human.Trace.Delegation.RVHashWindows
public import Human.Helpers.Delegation.RVOperations
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/Workers/Blake2Round/RVTheorems.lean (checked by verify.sh). The
-- public starting point is an `RV.State`; RAM cells are RAM at any address, INCLUDING
-- READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required to be at or
-- above `ROM_END`. The complete-span claims also state the delegate link: the circuit's final state IS the spec's run
-- of the span's round delegations (`RV.calls`, `RV.Delegation.blakeRound`), up to the spec's PC advance.

namespace Airbender.Blake2Round.Native

/-- The complete extended row matches its existing preparation, Clean
    eight-G round, chaining, control and address references on actual RV port values (`RVMemoryExecution`; RAM cells
    include the shadow RAM below `ROM_END`). The exclusive round mask remains the visible caller condition in
    `RVOperationInputs`. -/
def RVOperationExecutionClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {before : RV.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (_accepted : Delegation.MemoryAccepted data) (_inputs : Delegation.RVOperationInputs data before cells control) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeRound →
        ∃ round, Memory.RoundMask row.assignment round ∧ Row.spec (input round row.assignment) (output row.assignment)

/-- The assumptions of `RVOperationExecutionClaim` can be met by a pool with a round row. -/
def RVOperationExecutionSatisfiableClaim : Prop :=
  ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Trace.Cell)
    (control : Fin 4096 → Vector Nat 6),
    Delegation.MemoryAccepted data ∧ Delegation.RVOperationInputs data before cells control ∧
      (∀ cell ∈ cells, cell.Aligned) ∧ ∃ row ∈ data.rows, row.family = .blakeRound

/-- The complete seven or ten round compression reaches its reference
    output in actual RV RAM. `RVWordMapping` identifies successful initial/final block reads; `RVTraceMapping` binds
    the same final state to every native access and terminal token. The final state is the spec's run of the 7/10
    round delegation calls from `initial` (memory and registers; the PC advance is the spec's):
    `RV.calls (rvCalls flags) initial`. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def RVCompressionSoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {initial : RV.State} {cells : List Trace.Cell} {flags : Fin 8} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVCallInputs data initial cells flags) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.RVWordMapping initial after statePointer messagePointer input output message ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output = Compression.run flags input message ∧
        ∃ s', RV.calls (rvCalls flags) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls flags).length)))

/-- The complete extended-BLAKE reference binds actual boundary RV
    reads and the final `RV.State` with retained seed timestamps, with the same delegate link. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def RVCompressionBoundarySoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {initial : RV.State} {cells : List Trace.Cell} {flags : Fin 8} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVNativeCallInputs data initial cells flags) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.RVWordMapping initial after statePointer messagePointer input output message ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output = Compression.run flags input message ∧
        ∃ s', RV.calls (rvCalls flags) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls flags).length)))

/-- The first complete compression reaches its reference (`RVSpanResult`,
    delegate link included) on actual cut `RV.State`s from a retained native boundary. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def RVWindowSoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {before : RV.State} {cells : List Trace.Cell} {flags : Fin 8} {lower upper : Nat} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVWindowInputs data before cells flags lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.Caller.RVWindowResult (RVSpanResult flags) data before cells lower upper

end Airbender.Blake2Round.Native
