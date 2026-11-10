module
public import Slop.Keccak.RVWindows
public import Slop.Keccak.RVNativeExecution
public import Slop.Final.Generic.Trace.Workers.Keccak.RVTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.Keccak

/-- RV sibling of `Native.permutation_boundary_soundness`, with the delegate link. -/
private theorem Native.rv_permutation_boundary_soundness_generic [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVNativeCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.RVWordMapping initial after pointer input output ∧
        Delegation.RVTraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
        ∃ s', RV.calls rvCalls initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * rvCalls.length))) :=
  Proofs.rv_permutation_binding_at_boundary hp inverse accepted
    (inputs.toRVBoundary (by norm_num [Trace.timestampBase]; omega) accepted) tables aligned

theorem Native.rv_permutation_boundary_soundness : Airbender.Keccak.Native.RVPermutationBoundarySoundnessClaim := by babybear_instance Native.rv_permutation_boundary_soundness_generic

/-- RV sibling of `Native.permutation_soundness`, with the delegate link. -/
theorem Native.rv_permutation_soundness_generic [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.RVWordMapping initial after pointer input output ∧
        Delegation.RVTraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
        ∃ s', RV.calls rvCalls initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * rvCalls.length))) :=
  Proofs.rv_permutation_binding_at_boundary hp inverse accepted inputs.toRVBoundary tables aligned

theorem Native.rv_permutation_soundness : Airbender.Keccak.Native.RVPermutationSoundnessClaim := by babybear_instance Native.rv_permutation_soundness_generic

/-- RV sibling of `Native.operation_execution`. -/
private theorem Native.rv_operation_execution_generic [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.RVOperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → Native.RowEffects row.assignment :=
  Native.Proofs.rv_operation_execution hp inverse accepted inputs aligned

theorem Native.rv_operation_execution : Airbender.Keccak.Native.RVOperationExecutionClaim := by babybear_instance Native.rv_operation_execution_generic

/-- RV sibling of `Native.window_soundness`, with the delegate link in `RVSpanResult`. -/
theorem Native.rv_window_soundness_generic [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVWindowInputs data before cells lower upper) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.RVWindowResult RVSpanResult data before cells lower upper :=
  Proofs.rv_window_binding hp inverse accepted inputs aligned

theorem Native.rv_window_soundness : Airbender.Keccak.Native.RVWindowSoundnessClaim := by babybear_instance Native.rv_window_soundness_generic

end Airbender.Keccak
