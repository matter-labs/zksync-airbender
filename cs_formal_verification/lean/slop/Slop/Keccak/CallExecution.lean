import Slop.Keccak.ControlHistory
import Slop.Keccak.PointerHistory
import Slop.Keccak.NativeExecution

namespace Airbender.Keccak.Proofs
set_option warningAsError true

theorem call_execution [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data initial cells ∧ CallSchedule data ∧ CallPointer data initial ∧
      ∀ row ∈ data.rows, Native.RowEffects row.assignment := by
  have operations : Delegation.Proofs.BoundaryOperationInputs data initial cells Controller.rows := by
    refine ⟨inputs.memory, tables, ?_, ?_⟩
    · intro row member blake
      have family := inputs.family row member
      rw [family] at blake
      cases blake
    · intro row member _
      exact inputs.active row member
  have effects := Native.Proofs.operation_execution_at_boundary hp inverse accepted operations aligned
  have clockBound : 2 * Trace.timestampBase + 4 < p := by
    norm_num [Trace.timestampBase]
    omega
  exact ⟨effects.1, call_schedule clockBound accepted inputs,
    call_pointer clockBound accepted inputs,
    fun row member => effects.2 row member (inputs.family row member)⟩

end Airbender.Keccak.Proofs
