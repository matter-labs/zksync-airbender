import Slop.Blake2G.RVWindows
import Slop.Blake2G.RVNativeExecution
import Human.Trace.Workers.Blake2G.RVTheorems

namespace Airbender.Blake2G

/-- RV sibling of `Native.workvector_soundness` (statement of `Native.RVWorkvectorSoundnessClaim`): the complete
    native G span updates its actual RV RAM work vector (RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW
    RAM BELOW `ROM_END`) through the pinned 56/80-call schedule and original Clean G, and its final state is the
    spec's run of the 56/80 `G` delegation calls from `initial`, up to the spec's PC advance. -/
theorem Native.rv_workvector_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell}
    {reduced : Bool} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVCallInputs data initial cells reduced) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length))) :=
  Proofs.rv_workvector_binding_at_boundary hp inverse accepted (Proofs.RVCallInputs.toRVBoundary inputs) aligned

/-- RV sibling of `Native.workvector_boundary_soundness` (statement of
    `Native.RVWorkvectorBoundarySoundnessClaim`), with the same delegate link. -/
theorem Native.rv_workvector_boundary_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell}
    {reduced : Bool} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVNativeCallInputs data initial cells reduced) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input message output : Vector Arithmetic.Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length))) :=
  Proofs.rv_workvector_binding_at_boundary hp inverse accepted (Proofs.RVNativeCallInputs.toRVBoundary inputs)
    aligned

/-- RV sibling of `Native.window_soundness` (statement of `Native.RVWindowSoundnessClaim`). -/
theorem Native.rv_window_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    {reduced : Bool} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVWindowInputs data before cells reduced lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.RVWindowResult (RVSpanResult reduced) data before cells lower upper :=
  Proofs.rv_window_binding hp inverse accepted inputs aligned

end Airbender.Blake2G

namespace Airbender.Blake2G.Native

/-- RV sibling of `operation_execution` (statement of `RVOperationExecutionClaim`). -/
theorem rv_operation_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.RVOperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment) :=
  Proofs.rv_operation_execution hp inverse accepted inputs aligned

end Airbender.Blake2G.Native
