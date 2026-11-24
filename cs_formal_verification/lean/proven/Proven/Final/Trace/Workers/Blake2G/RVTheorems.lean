module
public import Proven.Blake2G.RVWindows
public import Proven.Blake2G.RVNativeExecution
public import Human.Trace.Workers.Blake2G.RVTheorems
public import Proven.Final.Generic.Trace.Workers.Blake2G.RVTheorems
public import Proven.Field.BabyBearInstance

@[expose] public section

namespace Airbender.Blake2G

/-- RV sibling of `Native.workvector_soundness` (statement of `Native.RVWorkvectorSoundnessClaim`): the complete
    native G span updates its actual RV RAM work vector (RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW
    RAM BELOW `ROM_END`) through the pinned 56/80-call schedule and original Clean G, and its final state is the
    spec's run of the 56/80 `G` delegation calls from `initial`, up to the spec's PC advance. -/
theorem Native.rv_workvector_soundness_generic [Fact p.Prime] (hp : 8388608 ≤ p)
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

theorem Native.rv_workvector_soundness : Airbender.Blake2G.Native.RVWorkvectorSoundnessClaim := by babybear_instance Native.rv_workvector_soundness_generic

/-- RV sibling of `Native.workvector_boundary_soundness` (statement of
    `Native.RVWorkvectorBoundarySoundnessClaim`), with the same delegate link. -/
private theorem Native.rv_workvector_boundary_soundness_generic [Fact p.Prime] (hp : 8388608 ≤ p)
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

theorem Native.rv_workvector_boundary_soundness : Airbender.Blake2G.Native.RVWorkvectorBoundarySoundnessClaim := by babybear_instance Native.rv_workvector_boundary_soundness_generic

/-- RV sibling of `Native.window_soundness` (statement of `Native.RVWindowSoundnessClaim`). -/
theorem Native.rv_window_soundness_generic [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    {reduced : Bool} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVWindowInputs data before cells reduced lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.RVWindowResult (RVSpanResult reduced) data before cells lower upper :=
  Proofs.rv_window_binding hp inverse accepted inputs aligned

theorem Native.rv_window_soundness : Airbender.Blake2G.Native.RVWindowSoundnessClaim := by babybear_instance Native.rv_window_soundness_generic

end Airbender.Blake2G

namespace Airbender.Blake2G.Native

/-- RV sibling of `operation_execution` (statement of `RVOperationExecutionClaim`). -/
private theorem rv_operation_execution_generic [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.RVOperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment) :=
  Proofs.rv_operation_execution hp inverse accepted inputs aligned

theorem rv_operation_execution : Airbender.Blake2G.Native.RVOperationExecutionClaim := by babybear_instance rv_operation_execution_generic

end Airbender.Blake2G.Native
