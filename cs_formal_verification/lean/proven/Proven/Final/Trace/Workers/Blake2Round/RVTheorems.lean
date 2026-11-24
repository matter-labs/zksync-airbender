module
public import Proven.Blake2Round.RVWindows
public import Proven.Blake2Round.RVNativeExecution
public import Human.Trace.Workers.Blake2Round.RVTheorems
public import Proven.Final.Generic.Trace.Workers.Blake2Round.RVTheorems
public import Proven.Field.BabyBearInstance

@[expose] public section

namespace Airbender.Blake2Round.Native

/-- RV sibling of `operation_execution` (statement of `RVOperationExecutionClaim`): native extended-BLAKE rows match
    their reference within actual RV memory execution (RAM cells include read-write shadow RAM below `ROM_END`). -/
private theorem rv_operation_execution_generic [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.RVOperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeRound →
        ∃ round, Memory.RoundMask row.assignment round ∧ Row.spec (input round row.assignment) (output row.assignment) :=
  Proofs.rv_operation_execution hp inverse accepted inputs aligned

theorem rv_operation_execution : Airbender.Blake2Round.Native.RVOperationExecutionClaim := by babybear_instance rv_operation_execution_generic

/-- RV sibling of `compression_soundness` (statement of `RVCompressionSoundnessClaim`): the complete 7/10-round
    compression reaches its reference in actual RV RAM (RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW
    RAM BELOW `ROM_END`), and its final state is the spec's run of the round delegation calls from `initial`, up to
    the spec's PC advance. -/
theorem rv_compression_soundness_generic [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell}
    {flags : Fin 8} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVCallInputs data initial cells flags) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.RVWordMapping initial after statePointer messagePointer input output message ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output = Compression.run flags input message ∧
        ∃ s', RV.calls (rvCalls flags) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls flags).length))) :=
  Proofs.rv_compression_binding_at_boundary hp inverse accepted (Proofs.RVCallInputs.toRVBoundary inputs) aligned

theorem rv_compression_soundness : Airbender.Blake2Round.Native.RVCompressionSoundnessClaim := by babybear_instance rv_compression_soundness_generic

/-- RV sibling of `compression_boundary_soundness` (statement of `RVCompressionBoundarySoundnessClaim`), with the
    same delegate link. -/
private theorem rv_compression_boundary_soundness_generic [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Trace.Cell}
    {flags : Fin 8} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVNativeCallInputs data initial cells flags) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.RVWordMapping initial after statePointer messagePointer input output message ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output = Compression.run flags input message ∧
        ∃ s', RV.calls (rvCalls flags) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls flags).length))) :=
  Proofs.rv_compression_binding_at_boundary hp inverse accepted (Proofs.RVNativeCallInputs.toRVBoundary inputs)
    aligned

theorem rv_compression_boundary_soundness : Airbender.Blake2Round.Native.RVCompressionBoundarySoundnessClaim := by babybear_instance rv_compression_boundary_soundness_generic

/-- RV sibling of `window_soundness` (statement of `RVWindowSoundnessClaim`). -/
theorem rv_window_soundness_generic [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    {flags : Fin 8} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVWindowInputs data before cells flags lower upper) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.RVWindowResult (RVSpanResult flags) data before cells lower upper :=
  Proofs.rv_window_binding hp inverse accepted inputs aligned

theorem rv_window_soundness : Airbender.Blake2Round.Native.RVWindowSoundnessClaim := by babybear_instance rv_window_soundness_generic

end Airbender.Blake2Round.Native
