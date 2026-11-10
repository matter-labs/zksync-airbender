module
public import Human.Trace.Workers.Blake2G.RVCall
public import Human.Trace.Delegation.RVHashWindows
public import Human.Helpers.Delegation.RVOperations
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/Workers/Blake2G/RVTheorems.lean (checked by verify.sh). The public starting point is an `RV.State`; RAM cells are RAM at any address, INCLUDING
-- READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required to be at or
-- above `ROM_END`. The complete-span claims also state the delegate link: the circuit's final state IS the spec's run
-- of the span's `G` delegations (`RV.calls`, `RV.Delegation.blakeG`), up to the spec's PC advance.

namespace Airbender.Blake2G

/-- The complete native G span updates its actual RAM work vector
    through the pinned 56/80-call schedule and original Clean G, on `RV.State`s. `RVWordMapping` exposes successful
    initial/final reads; `RVTraceMapping` binds the same final state to every native access and terminal token. The
    final state is the spec's run of the 56/80 `G` delegation calls from `initial` (memory and registers; the PC
    advance is the spec's): `RV.calls (rvCalls reduced) initial`. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def Native.RVWorkvectorSoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {initial : RV.State} {cells : List Trace.Cell} {reduced : Bool} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVCallInputs data initial cells reduced) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length)))

/-- The complete G reference binds actual boundary RV reads
    and the final `RV.State`, retaining native seed timestamps, with the same delegate link. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def Native.RVWorkvectorBoundarySoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {initial : RV.State} {cells : List Trace.Cell} {reduced : Bool} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVNativeCallInputs data initial cells reduced) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length)))

/-- A complete G-worker span selected after whole preceding spans reaches
    the pinned work-vector reference (`RVSpanResult`, delegate link included) on its actual native-clock cut
    `RV.State`s. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def Native.RVWindowSoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {before : RV.State} {cells : List Trace.Cell} {reduced : Bool} {lower upper : Nat} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVWindowInputs data before cells reduced lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.Caller.RVWindowResult (RVSpanResult reduced) data before cells lower upper

end Airbender.Blake2G

namespace Airbender.Blake2G.Native

/-- Native G reads and writes agree with Clean's original G reference within
    actual RV memory execution (`RVMemoryExecution`; RAM cells include the shadow RAM below `ROM_END`). -/
def RVOperationExecutionClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {before : RV.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (_accepted : Delegation.MemoryAccepted data) (_inputs : Delegation.RVOperationInputs data before cells control) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment)

/-- The assumptions of `RVOperationExecutionClaim` can be met by a pool with a G row. -/
def RVOperationExecutionSatisfiableClaim : Prop :=
  ∃ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Trace.Cell)
    (control : Fin 4096 → Vector Nat 6),
    Delegation.MemoryAccepted data ∧ Delegation.RVOperationInputs data before cells control ∧
      (∀ cell ∈ cells, cell.Aligned) ∧ ∃ row ∈ data.rows, row.family = .blakeG

end Airbender.Blake2G.Native
