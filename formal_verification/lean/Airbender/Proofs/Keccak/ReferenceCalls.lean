import Airbender.Review.Trace.Delegation.ReferenceCalls
import Airbender.Proofs.Keccak.CallABI
import Airbender.Proofs.Keccak.CallHistory
import Airbender.Proofs.Delegation.ReferenceCalls

namespace Airbender.Keccak.Call.Proofs
open Arithmetic Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem step_in_span [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial before after : State} {domain : List Cell}
    {events : List MemoryAccess} {historyCells : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Keccak.Proofs.BoundaryCallInputs data initial domain)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ data.rows)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (observed : ∀ port ∈ row.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment port).word.toBitVec before) :
    Executes before after := by
  obtain ⟨control, abi, binding⟩ := abi_in_span hp inverse accepted inputs tables ram member
  have memory : Keccak.Proofs.BoundaryMemoryInputs data initial domain Controller.rows :=
    ⟨inputs.memory, inputs.family, by rw [tables]; rfl, inputs.active⟩
  have bounds := Keccak.Memory.Proofs.value_bounds_at_boundary
    (by norm_num [timestampBase]; omega) accepted memory
  have family := inputs.family row member
  have active := inputs.active row member
  rcases row with ⟨kind, w⟩
  change kind = .keccak at family
  subst kind
  have core := native_core accepted tables member
  have full := executes hp inverse (w := w) (control := control) core active abi binding
    (fun port present => by
      have included : port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports := by
        change port ∈ importedConstraintsMemoryPorts
        exact present
      exact ⟨bounds.1 _ member port included, bounds.2.1 _ member port included⟩)
    history permutation (fun port present => by
      obtain ⟨cell, code, read⟩ := observed port (by
        change port ∈ importedConstraintsMemoryPorts
        exact present)
      exact ⟨cell, code, read⟩)
  exact full

theorem reference_call_in_span [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial finalState : State} {domain : List Cell}
    {events : List MemoryAccess}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Keccak.Proofs.BoundaryCallInputs data initial domain)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ data.rows)
    (execution : Delegation.CallExecution domain events initial finalState row) :
    Delegation.ReferenceCallExecution Executes domain events initial finalState row := by
  obtain ⟨earlier, current, newer, before, after, split, permutation, past, history, future, observed⟩ := execution
  refine ⟨earlier, current, newer, before, after, split, permutation, past, history, future,
    step_in_span hp inverse accepted inputs tables ram member history permutation ?_⟩
  intro port present
  obtain ⟨cell, _, code, read, _⟩ := observed port present
  exact ⟨cell, code, read⟩

theorem span_reference [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Keccak.Proofs.BoundaryCallInputs data initial domain)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ domain, cell.Aligned)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat) :
    ∃ after, Relation.ReflTransGen Executes initial after ∧ Delegation.TraceMapping data initial after domain := by
  obtain ⟨ordered, after, permutation, history, terminal⟩ :=
    Keccak.Proofs.call_history hp inverse accepted inputs tables aligned
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
  apply step_in_span hp inverse accepted inputs tables ram member current eventsPerm
  intro port included
  obtain ⟨cell, _, code, read, _⟩ := Delegation.Proofs.row_atomic_observations clockBound
    accepted inputs.memory member current eventsPerm aligned readable port included
  exact ⟨cell, code, read⟩

end Airbender.Keccak.Call.Proofs
