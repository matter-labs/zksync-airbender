import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Keccak.NativeEffects
import Airbender.Proofs.Keccak.MixStage
import Airbender.Proofs.Keccak.Iota
import Airbender.Review.Circuits.Keccak.Execution
import Airbender.Proofs.Keccak.ControllerLayout
import Airbender.Proofs.Keccak.Addresses
import Airbender.Proofs.Keccak.Chi
import Airbender.Proofs.Keccak.RhoRotation
import Airbender.Proofs.Keccak.Rho
import Airbender.Proofs.Keccak.Theta
import Airbender.Proofs.Keccak.DecodeControl
import Airbender.Review.Trace.Delegation.Theorems

namespace Airbender.Keccak.Native.Proofs

open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem operation_execution_at_boundary [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (inverse : SerializedInverse.Scale256 p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.Proofs.BoundaryOperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → RowEffects row.assignment := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have bounds := Delegation.Proofs.operation_word_bounds_at_boundary (by omega) (by
    linear_combination inverse) accepted inputs
  refine ⟨Delegation.Proofs.native_memory_execution size accepted inputs.publicState aligned, ?_⟩
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

theorem operation_execution [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (inverse : SerializedInverse.Scale256 p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.OperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → RowEffects row.assignment :=
  operation_execution_at_boundary hp inverse accepted inputs.toBoundaryInputs aligned

end Airbender.Keccak.Native.Proofs
