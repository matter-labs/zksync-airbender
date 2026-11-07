import Human.Trace.Workers.Blake2G.RVCall
import Human.Trace.Delegation.RVHashWindows
import Human.Helpers.Delegation.RVOperations

-- The statements proven in slop/Slop/Final/Trace/Workers/Blake2G/RVTheorems.lean (checked by verify.sh). RV siblings
-- of `Theorems.lean`: the public starting point is an `RV.State`; RAM cells are RAM at any address, INCLUDING
-- READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required to be at or
-- above `ROM_END`. The complete-span claims also state the delegate link: the circuit's final state IS the spec's run
-- of the span's `G` delegations (`RV.calls`, `RV.Delegation.blakeG`), up to the spec's PC advance.

namespace Airbender.Blake2G

/-- RV sibling of `Native.WorkvectorSoundnessClaim`: the complete native G span updates its actual RAM work vector
    through the pinned 56/80-call schedule and original Clean G, on `RV.State`s. `RVWordMapping` exposes successful
    initial/final reads; `RVTraceMapping` binds the same final state to every native access and terminal token. The
    final state is the spec's run of the 56/80 `G` delegation calls from `initial` (memory and registers; the PC
    advance is the spec's): `RV.calls (rvCalls reduced) initial`. -/
def Native.RVWorkvectorSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell} {reduced : Bool} (accepted : Delegation.MemoryAccepted data) (inputs : RVCallInputs data initial cells reduced) (aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length)))

/-- RV sibling of `Native.WorkvectorBoundarySoundnessClaim`: the complete G reference binds actual boundary RV reads
    and the final `RV.State`, retaining native seed timestamps, with the same delegate link. -/
def Native.RVWorkvectorBoundarySoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell} {reduced : Bool} (accepted : Delegation.MemoryAccepted data) (inputs : RVNativeCallInputs data initial cells reduced) (aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length)))

/-- RV sibling of `Native.WindowSoundnessClaim`: a complete G-worker span selected after whole preceding spans reaches
    the pinned work-vector reference (`RVSpanResult`, delegate link included) on its actual native-clock cut
    `RV.State`s. -/
def Native.RVWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell} {reduced : Bool} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data) (inputs : RVWindowInputs data before cells reduced lower upper) (aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.Caller.RVWindowResult (RVSpanResult reduced) data before cells lower upper

end Airbender.Blake2G

namespace Airbender.Blake2G.Native

/-- RV sibling of `OperationExecutionClaim`: native G reads and writes agree with Clean's original G reference within
    actual RV memory execution (`RVMemoryExecution`; RAM cells include the shadow RAM below `ROM_END`). -/
def RVOperationExecutionClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.RVOperationInputs data before cells control) (aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment)

end Airbender.Blake2G.Native
