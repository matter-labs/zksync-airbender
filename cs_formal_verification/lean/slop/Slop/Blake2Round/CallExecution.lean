import Slop.Blake2Round.CallHistory
import Slop.Blake2Round.NativeExecution

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true

theorem call_operation_inputs [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {flags : Fin 8} (accepted : Delegation.MemoryAccepted data)
    (inputs : BoundaryCallInputs data initial cells flags) :
    Delegation.Proofs.BoundaryOperationInputs data initial cells Keccak.Controller.rows := by
  refine ⟨inputs.memory, inputs.tables, ?_, ?_⟩
  · intro row member _
    exact call_masks hp accepted inputs row member
  · intro row member keccak
    rw [inputs.family row member] at keccak
    cases keccak

theorem call_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {flags : Fin 8} (accepted : Delegation.MemoryAccepted data)
    (inputs : BoundaryCallInputs data initial cells flags) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CallModes data flags ∧ Delegation.MemoryExecution data initial cells ∧
      ∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round ∧
        Row.spec (Native.input round row.assignment) (Native.output row.assignment) := by
  have operations := call_operation_inputs (by norm_num [Trace.timestampBase]; omega) accepted inputs
  have result := Native.Proofs.operation_execution_at_boundary hp inverse accepted operations aligned
  exact ⟨call_modes (by norm_num [Trace.timestampBase]; omega) accepted inputs,
    result.1, fun row member => result.2 row member (inputs.family row member)⟩

end Airbender.Blake2Round.Proofs
