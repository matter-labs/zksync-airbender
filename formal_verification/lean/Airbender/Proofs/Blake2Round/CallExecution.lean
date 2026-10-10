import Airbender.Proofs.Blake2Round.CallHistory
import Airbender.Proofs.Blake2Round.NativeExecution

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true

theorem call_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {flags : Fin 8} (accepted : Delegation.MemoryAccepted data)
    (inputs : CallInputs data initial cells flags) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data initial cells ∧
      ∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round ∧
        Row.spec (Native.input round row.assignment) (Native.output row.assignment) := by
  have masks := call_masks (by norm_num [Trace.timestampBase]; omega) accepted inputs
  have operations : Delegation.OperationInputs data initial cells Keccak.Controller.rows := by
    refine ⟨inputs.memory, inputs.tables, ?_, ?_⟩
    · intro row member _
      exact masks row member
    · intro row member keccak
      have family := inputs.family row member
      rw [family] at keccak
      cases keccak
  have result := Native.Proofs.operation_execution hp inverse accepted operations aligned
  exact ⟨result.1, fun row member => result.2 row member (inputs.family row member)⟩

end Airbender.Blake2Round.Proofs
