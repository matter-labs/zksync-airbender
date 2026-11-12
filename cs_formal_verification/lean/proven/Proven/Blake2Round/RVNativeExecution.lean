module
public import Proven.Blake2Round.NativeExecution
public import Proven.Delegation.RVExecution
public import Proven.Delegation.SeedOperations
public import Human.Helpers.Delegation.RVOperations

@[expose] public section

/-! RV twin of `NativeExecution.operation_execution`: native extended-BLAKE rows inside actual RV memory execution
    (RAM cells include read-write shadow RAM below `ROM_END`). The per-row reference (`native_effects`) is state-free. -/

namespace Airbender.Blake2Round.Native.Proofs
open Trace
set_option warningAsError true

theorem rv_operation_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.RVOperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeRound →
        ∃ round, Memory.RoundMask row.assignment round ∧ Row.spec (input round row.assignment) (output row.assignment) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have bounds := Delegation.SeedProofs.operation_word_bounds hp inverse accepted
    inputs.publicState.toRVBoundaryInputs.toSeed inputs.tables inputs.rounds inputs.keccakActive
  refine ⟨Delegation.Proofs.rv_native_memory_execution size accepted inputs.publicState aligned, ?_⟩
  intro row member family
  obtain ⟨round, mask⟩ := inputs.rounds row member family
  have holds := accepted.constraints row member
  have reads := bounds.reads row member
  rcases row with ⟨kind, w⟩
  change kind = .blakeRound at family
  subst kind
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints setupTable) importedConstraintsTimestampLookups)
  exact ⟨round, mask, native_effects hp inverse round core mask reads⟩

end Airbender.Blake2Round.Native.Proofs
