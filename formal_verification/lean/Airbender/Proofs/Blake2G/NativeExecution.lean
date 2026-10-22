import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.NativeEffects
import Airbender.Review.Circuits.Blake2G.Execution
import Airbender.Proofs.Blake2G.Soundness
import Airbender.Review.Trace.Delegation.Theorems

namespace Airbender.Blake2G.Native.Proofs

open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 250000

theorem operation_execution_at_boundary [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.Proofs.BoundaryOperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have bounds := Delegation.Proofs.operation_word_bounds_at_boundary hp inverse accepted inputs
  refine ⟨Delegation.Proofs.native_memory_execution size accepted inputs.publicState aligned, ?_⟩
  intro row member family
  have holds := accepted.constraints row member
  have reads := bounds.reads row member
  rcases row with ⟨kind, w⟩
  change kind = .blakeG at family
  subst kind
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Control.controllerRows)) importedConstraintsTimestampLookups)
  exact native_effects hp inverse core reads

theorem operation_execution [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.OperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment) :=
  operation_execution_at_boundary hp inverse accepted inputs.toBoundaryInputs aligned

end Airbender.Blake2G.Native.Proofs
