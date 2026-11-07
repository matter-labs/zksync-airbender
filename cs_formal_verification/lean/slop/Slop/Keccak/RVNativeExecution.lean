import Slop.Keccak.NativeExecution
import Slop.Delegation.RVExecution
import Slop.Delegation.SeedOperations
import Human.Helpers.Delegation.RVOperations

/-! RV twin of `NativeExecution.operation_execution`: an initialized mixed pool from an `RV.State` executes every access
    as RV cell reads/writes (RAM cells include the shadow RAM below `ROM_END`), and every Keccak row has the native
    effects (state-free, from the seed-level word bounds). -/

namespace Airbender.Keccak.Native.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem rv_operation_execution [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.RVOperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → RowEffects row.assignment := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have boundary := inputs.publicState.toRVBoundaryInputs
  have bounds := Delegation.SeedProofs.operation_word_bounds (by omega) (by linear_combination inverse)
    accepted boundary.toSeed inputs.tables inputs.rounds inputs.keccakActive
  refine ⟨Delegation.Proofs.rv_native_memory_execution size accepted inputs.publicState aligned, ?_⟩
  intro row member family
  have holds := accepted.constraints row member
  have reads := bounds.reads row member
  have active := inputs.keccakActive row member family
  rcases row with ⟨kind, w⟩
  change kind = .keccak at family
  subst kind
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Controller.rows)) importedConstraintsTimestampLookups)
  exact native_effects hp inverse core active reads

end Airbender.Keccak.Native.Proofs
