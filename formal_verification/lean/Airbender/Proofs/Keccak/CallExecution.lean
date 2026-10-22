import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Delegation.Terminal
import Airbender.Proofs.Keccak.ControlHistory
import Airbender.Proofs.Keccak.PointerHistory
import Airbender.Proofs.Keccak.NativeEffects
import Airbender.Proofs.Keccak.MemorySoundness
import Airbender.Proofs.Delegation.Memory

namespace Airbender.Keccak.Proofs
set_option warningAsError true

theorem call_execution [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (inverse : SerializedInverse.Scale256 p)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data initial cells ∧ CallSchedule data ∧ CallPointer data initial ∧
      ∀ row ∈ data.rows, Native.RowEffects row.assignment := by
  have clockBound : 2 * Trace.timestampBase + 4 < p := by
    norm_num [Trace.timestampBase]
    omega
  have memory : BoundaryMemoryInputs data initial cells Controller.rows :=
    ⟨inputs.memory, inputs.family, by rw [tables]; rfl, inputs.active⟩
  have bounds := Keccak.Memory.Proofs.value_bounds_at_boundary clockBound accepted memory
  refine ⟨Delegation.Proofs.native_memory_execution clockBound accepted inputs.memory aligned,
    call_schedule clockBound accepted inputs, call_pointer clockBound accepted inputs, ?_⟩
  intro row member
  have family := inputs.family row member
  have holds := accepted.constraints row member
  simp only [Delegation.Row.constraints, family, tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Controller.rows)) importedConstraintsTimestampLookups)
  have reads : ∀ port ∈ importedConstraintsMemoryPorts,
      (Trace.readToken row.assignment port).word.Bounded := by
    simpa only [Delegation.Row.ports, family] using bounds.1 row member
  exact Native.Proofs.native_effects hp inverse core (inputs.active row member) reads

end Airbender.Keccak.Proofs
