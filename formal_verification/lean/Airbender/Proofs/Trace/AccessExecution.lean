import Airbender.Proofs.Trace.SailHistory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

theorem history_access_execution {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    {event : MemoryAccess} (present : event ∈ events) :
    ∃ cell ∈ cells, ∃ earlier middle later newer,
      events = newer ++ event :: earlier ∧
      SailHistory cells earlier before middle ∧
      cell.addressCode = event.2.1 ∧
      cell.read middle = .ok (memoryWord event.2.2.1) middle ∧
      run (cell.write (memoryWord event.2.2.2)) middle = .ok () later ∧
      SailHistory cells newer later after := by
  induction history with
  | nil => cases present
  | @cons head rest before middle after past cell member address read write ih =>
    rcases List.mem_cons.mp present with rfl | previous
    · exact ⟨cell, member, rest, middle, after, [], rfl, past, address, read, write, .nil after⟩
    · obtain ⟨other, domain, earlier, start, finish, newer, shape, old, location, actualRead,
        actualWrite, future⟩ := ih previous
      exact ⟨other, domain, earlier, start, finish, head :: newer, by rw [shape]; rfl,
        old, location, actualRead, actualWrite, .cons future cell member address read write⟩

end Airbender.Trace.Proofs
