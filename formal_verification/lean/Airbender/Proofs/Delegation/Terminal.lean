import Airbender.Proofs.Delegation.SailHistory
import Airbender.Proofs.Trace.TransferTerminal

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem raw_time_injective [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {first last : MemoryAccess} (firstMember : first ∈ rawEvents data)
    (lastMember : last ∈ rawEvents data) (address : first.2.1 = last.2.1)
    (time : first.1 = last.1) : first = last :=
  Trace.Proofs.Transfer.raw_time_injective (transfer_facts hp accepted inputs) (transferInputs inputs) firstMember lastMember address time

theorem event_clock_le [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {first last : MemoryAccess} (firstMember : first ∈ rawEvents data)
    (lastMember : last ∈ rawEvents data) (address : first.2.1 = last.2.1)
    (time : last.1 ≤ first.1) : eventClock data last ≤ eventClock data first :=
  Trace.Proofs.Transfer.event_clock_le (transfer_facts hp accepted inputs) (transferInputs inputs) firstMember lastMember address time

theorem terminal_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {sink : MemoryToken p} (member : sink ∈ data.terminal) :
    ∃ source ∈ data.initial, source.address = sink.address ∧
      ∃ path : List (MemoryToken p), path.head? = some source ∧ path.getLast? = some sink ∧
        (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
        (path.zip path.tail).Perm (data.steps.filter fun edge => edge.1.address = sink.address) :=
  Trace.Proofs.Transfer.terminal_path (transfer_facts hp accepted inputs) (transferInputs inputs) member

theorem terminal_latest_value [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {history : TimestampSortedMemoryAccessList} (bound : history.val.Perm (labeledEvents data))
    {sink : MemoryToken p} (member : sink ∈ data.terminal) :
    MemoryAccessList.lastWriteValue history.val history.property sink.address = sink.value :=
  Trace.Proofs.Transfer.terminal_latest_value (transfer_facts hp accepted inputs) (transferInputs inputs) bound member

theorem terminal_sail_reads [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before after : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {history : TimestampSortedMemoryAccessList} (bound : history.val.Perm (labeledEvents data))
    (realized : SailStateMatches cells history after) :
    ∀ sink ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (memoryWord sink.value) after :=
  Trace.Proofs.Transfer.terminal_sail_reads (transfer_facts hp accepted inputs) (transferInputs inputs) bound realized

end Airbender.Delegation.Proofs
