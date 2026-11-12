module
public import Proven.Trace.Machine.MemoryWorkers

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Standard worker events occur three ticks after the matched invocation. -/
theorem standard_event_time {workers : WorkerPools babyBearModulus} (clocks : WorkerClocks workers)
    {row : Delegation.Row babyBearModulus} (member : row ∈ workers.standard.rows)
    {event : MemoryAccess} (present : event ∈ row.memorySteps.map transferEvent) :
    event.1 = (timeOfPair (Requests.fulfillment row).time).value + 3 := by
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
  have native : port ∈ row.ports := by simpa using portMember
  have clock := standard_worker_clock clocks member
  have time := (write_time_of_room (by decide : timestampBase < babyBearModulus)
    (base := rawPair row.assignment row.columns.invocation) (offset := port.clock.offset) clock.1
    (by simpa only [Delegation.Proofs.port_offset row native, decodeTimestamp, rawPair] using clock.2)).2
  change (timeOfPair (row.writeToken port).time).value =
    (decodeTimestamp row.assignment row.columns.invocation).value + port.clock.offset at time
  change (timeOfPair (row.writeToken port).time).value + 1 =
    (decodeTimestamp row.assignment row.columns.invocation).value + 3
  rw [time, Delegation.Proofs.port_offset row native]

/-- Split worker events use the same invocation tick convention. -/
theorem split_event_time {workers : WorkerPools babyBearModulus} (clocks : WorkerClocks workers)
    {row : Keccak.Split.Native.Row babyBearModulus} (member : row ∈ workers.split.rows)
    {event : MemoryAccess} (present : event ∈ row.memorySteps.map transferEvent) :
    event.1 = (timeOfPair (splitFulfillment row).time).value + 3 := by
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
  have native : port ∈ row.ports := by simpa using portMember
  have clock := split_worker_clock clocks member
  have time := (write_time_of_room (by decide : timestampBase < babyBearModulus)
    (base := rawPair row.assignment row.columns.invocation) (offset := port.clock.offset) clock.1
    (by simpa only [Keccak.Split.Native.Proofs.port_offset row native, decodeTimestamp, rawPair] using clock.2)).2
  change (timeOfPair (row.writeToken port).time).value =
    (decodeTimestamp row.assignment row.columns.invocation).value + port.clock.offset at time
  change (timeOfPair (row.writeToken port).time).value + 1 =
    (decodeTimestamp row.assignment row.columns.invocation).value + 3
  rw [time, Keccak.Split.Native.Proofs.port_offset row native]

end Airbender.Trace.Machine.Proofs
