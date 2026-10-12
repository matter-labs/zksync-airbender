import Airbender.Proofs.Delegation.Memory
import Airbender.Proofs.Trace.TransferHistory

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true

def transferData (data : MemoryData p) : Trace.Proofs.Transfer.Data p :=
  ⟨data.initial, data.terminal, data.steps⟩

def transferInputs {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : MemoryInputs data before cells) : Trace.Proofs.Transfer.Inputs (transferData data) before cells :=
  ⟨inputs.initialization, inputs.distinct⟩

theorem transfer_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    Trace.Proofs.Transfer.Facts (transferData data) :=
  ⟨accepted.matching, preserved_addresses, memory_order hp accepted inputs⟩

abbrev rawEvents (data : MemoryData p) := Trace.Proofs.Transfer.rawEvents (transferData data)
abbrev memoryEpoch (data : MemoryData p) := Trace.Proofs.Transfer.memoryEpoch (transferData data)
abbrev eventClock (data : MemoryData p) := Trace.Proofs.Transfer.eventClock (transferData data)
abbrev labeledEvents (data : MemoryData p) := Trace.Proofs.Transfer.labeledEvents (transferData data)

theorem seed_below_epoch {data : MemoryData p} {source : MemoryToken p}
    (member : source ∈ data.initial) : source.address < memoryEpoch data :=
  Trace.Proofs.Transfer.seed_below_epoch (data := transferData data) member

theorem event_clock_order (data : MemoryData p) {first last : MemoryAccess}
    (lastBound : last.1 = 0 → last.2.1 < memoryEpoch data)
    (earlier : last.1 < first.1) : eventClock data last < eventClock data first :=
  Trace.Proofs.Transfer.event_clock_order (transferData data) lastBound earlier

theorem initialized_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.steps) :
    ∃ cell ∈ cells, cell.addressCode = edge.1.address :=
  Trace.Proofs.Transfer.initialized_cell (transfer_facts hp accepted inputs) (transferInputs inputs).toBoundaryInputs member

theorem zero_event_seed {data : MemoryData p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) (zero : event.1 = 0) :
    ∃ source ∈ data.initial, event = (0, source.address, 0, source.value) :=
  Trace.Proofs.Transfer.zero_event_seed (data := transferData data) member zero

theorem raw_cell_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (address : Nat) : ∃ history : TimestampSortedMemoryAccessList,
      history.val.Perm (MemoryAccessList.filterAddress (rawEvents data) address) ∧
      MemoryAccessList.isConsistentOnline history.val history.property :=
  Trace.Proofs.Transfer.raw_cell_history (transfer_facts hp accepted inputs) (transferInputs inputs).toBoundaryInputs address

theorem raw_seed_bound {data : MemoryData p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) : event.1 = 0 → event.2.1 < memoryEpoch data :=
  Trace.Proofs.Transfer.raw_seed_bound (data := transferData data) member

theorem raw_events_nodup [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    (rawEvents data).Nodup :=
  Trace.Proofs.Transfer.raw_events_nodup (transfer_facts hp accepted inputs) (transferInputs inputs).toBoundaryInputs

theorem event_clock_injective [Fact p.Prime] {data : MemoryData p}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {first last : MemoryAccess} (firstMember : first ∈ rawEvents data)
    (lastMember : last ∈ rawEvents data) (equal : eventClock data first = eventClock data last) :
    first = last :=
  Trace.Proofs.Transfer.event_clock_injective (transferInputs inputs).toBoundaryInputs firstMember lastMember equal

theorem labeled_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    ∃ history : TimestampSortedMemoryAccessList, history.val.Perm (labeledEvents data) ∧
      MemoryAccessList.isConsistentOnline history.val history.property :=
  Trace.Proofs.Transfer.labeled_history (transfer_facts hp accepted inputs) (transferInputs inputs).toBoundaryInputs

end Airbender.Delegation.Proofs
