import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.CallGroups
import Airbender.Proofs.Blake2Round.PointerHistory
import Airbender.Proofs.Delegation.AtomicHistory

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem call_atomic_observations [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ordered : List (Delegation.Row p)) (after : State), ordered.Perm data.rows ∧
      GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after ∧
      (∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round ∧
        Row.spec (Native.input round row.assignment) (Native.output row.assignment)) ∧
      (∀ row ∈ ordered, ∃ events start finish, events.Perm (row.memorySteps.map transferEvent) ∧
        SailHistory cells events start finish ∧
        ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
          cell.read start = .ok (memoryWord (port.readCode row.assignment)) start ∧
          cell.read finish = .ok (memoryWord (port.writeCode row.assignment)) finish) ∧
      ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (memoryWord token.value) after := by
  obtain ⟨ordered, after, permutation, history, effects, terminal⟩ :=
    call_history hp inverse accepted inputs aligned
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  exact ⟨ordered, after, permutation, history, effects,
    grouped_atomic_observations clockBound accepted inputs.memory permutation history aligned, terminal⟩

end Airbender.Blake2Round.Proofs
