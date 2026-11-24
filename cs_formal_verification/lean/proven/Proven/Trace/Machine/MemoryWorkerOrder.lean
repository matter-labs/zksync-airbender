module
public import Proven.Trace.Machine.MemoryWorkers
public import Proven.Delegation.Memory
public import Proven.KeccakSplit.Setup.Control

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Imported worker comparisons order every standard and split transfer strictly after its read. -/
theorem worker_memory_order {workers : WorkerPools babyBearModulus}
    (accepted : WorkersAccepted workers) (clocks : WorkerClocks workers)
    (previous : ∀ edge ∈ workers.steps, (timeOfPair edge.1.time).Bounded) :
    ∀ edge ∈ workers.steps, (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  intro edge present
  have readBound := previous edge present
  rcases List.mem_append.mp present with standard | split
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp standard
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native : port ∈ row.ports := by simpa using portMember
    have clock := standard_worker_clock clocks member
    have facts := Delegation.Proofs.row_facts workers.standard.setup row (accepted.standardConstraints row member)
    have checked := facts.comparisons port.clock (Delegation.Proofs.clock_member row native)
    have room : (decodeTimestamp row.assignment row.columns.invocation).lo + port.clock.offset < timestampBase := by
      rw [Delegation.Proofs.port_offset row native]
      exact clock.2
    have order := native_port_order_of_room (by decide : 2 * timestampBase + 4 < babyBearModulus)
      clock.1 readBound (facts.offsets port.clock (Delegation.Proofs.clock_member row native)) room checked.1
      (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using checked.2.1)
      (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using checked.2.2)
    exact order.trans_eq (write_time_of_room (by decide : timestampBase < babyBearModulus)
      (base := rawPair row.assignment row.columns.invocation) clock.1 room).2.symm
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp split
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native : port ∈ row.ports := by simpa using portMember
    have clock := split_worker_clock clocks member
    have room : (decodeTimestamp row.assignment row.columns.invocation).lo + port.clock.offset < timestampBase := by
      rw [Keccak.Split.Native.Proofs.port_offset row native]
      exact clock.2
    have order := Keccak.Split.Proofs.split_physical_port_order
      (by decide : 2 * timestampBase + 4 < babyBearModulus) Keccak.Split.Proofs.control_facts row
      (accepted.splitConstraints row member) (accepted.splitActive row member) native clock.1 readBound room
    exact order.trans_eq (write_time_of_room (by decide : timestampBase < babyBearModulus)
      (base := rawPair row.assignment row.columns.invocation) clock.1 room).2.symm

end Airbender.Trace.Machine.Proofs
