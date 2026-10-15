import Airbender.Review.Trace.Delegation.ReferenceCalls
import Airbender.Proofs.Blake2Round.CallABI
import Airbender.Proofs.Blake2Round.CallGroups
import Airbender.Proofs.Delegation.ReferenceCalls

namespace Airbender.Blake2Round.Call.Proofs
open Arithmetic Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem step_in_span [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial before after : State} {domain : List Cell}
    {events : List MemoryAccess} {historyCells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Blake2Round.Proofs.BoundaryCallInputs data initial domain flags)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ data.rows)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (observed : ∀ port ∈ row.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment port).word.toBitVec before) :
    Executes before after := by
  obtain ⟨round, mask, abi⟩ := abi_in_span hp inverse accepted inputs ram member
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have operation := Blake2Round.Proofs.call_operation_inputs clockBound accepted inputs
  have bounds := Delegation.Proofs.operation_word_bounds_at_boundary hp inverse accepted operation
  have family := inputs.family row member
  rcases row with ⟨kind, w⟩
  change kind = .blakeRound at family
  subst kind
  have core := native_core accepted inputs member
  have full := executes hp inverse (w := w) (round := round) core mask abi
    (fun port present => by
      have included : port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports := by
        change port ∈ importedConstraintsMemoryPorts
        exact present
      exact ⟨bounds.reads _ member port included, bounds.writes _ member port included⟩)
    history permutation (fun port present => by
      obtain ⟨cell, code, read⟩ := observed port (by
        change port ∈ importedConstraintsMemoryPorts
        exact present)
      exact ⟨cell, code, read⟩)
  exact full

theorem reference_call_in_span [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial finalState : State} {domain : List Cell}
    {events : List MemoryAccess} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Blake2Round.Proofs.BoundaryCallInputs data initial domain flags)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ data.rows)
    (execution : Delegation.CallExecution domain events initial finalState row) :
    Delegation.ReferenceCallExecution Executes domain events initial finalState row := by
  obtain ⟨earlier, current, newer, before, after, split, permutation, past, history, future, observed⟩ := execution
  refine ⟨earlier, current, newer, before, after, split, permutation, past, history, future,
    step_in_span hp inverse accepted inputs ram member history permutation ?_⟩
  intro port present
  obtain ⟨cell, _, code, read, _⟩ := observed port present
  exact ⟨cell, code, read⟩

theorem span_reference [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Blake2Round.Proofs.BoundaryCallInputs data initial domain flags)
    (aligned : ∀ cell ∈ domain, cell.Aligned)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat) :
    ∃ after, Relation.ReflTransGen Executes initial after ∧ Delegation.TraceMapping data initial after domain := by
  obtain ⟨ordered, after, permutation, history, _, terminal⟩ :=
    Blake2Round.Proofs.call_history hp inverse accepted inputs aligned
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have noZero : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent,
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro row _ event included
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp included
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
    exact Delegation.Proofs.port_not_zero row (by simpa using portMember)
  refine ⟨after, Delegation.Proofs.grouped_reference history aligned noZero
    (Delegation.Proofs.boundary_readable inputs.memory) ?_,
    Delegation.Proofs.grouped_trace_mapping permutation history terminal⟩
  intro row present events before after readable eventsPerm current
  have member := permutation.mem_iff.mp present
  apply step_in_span hp inverse accepted inputs ram member current eventsPerm
  intro port included
  obtain ⟨cell, _, code, read, _⟩ := Delegation.Proofs.row_atomic_observations clockBound
    accepted inputs.memory member current eventsPerm aligned readable port included
  exact ⟨cell, code, read⟩

end Airbender.Blake2Round.Call.Proofs
