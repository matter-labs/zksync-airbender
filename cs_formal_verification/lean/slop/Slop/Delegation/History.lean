import Slop.Delegation.Memory
import Slop.Trace.TransferHistory

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true

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

theorem zero_event_seed {data : MemoryData p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) (zero : event.1 = 0) :
    ∃ source ∈ data.initial, event = (0, source.address, 0, source.value) :=
  Trace.Proofs.Transfer.zero_event_seed (data := transferData data) member zero

theorem raw_seed_bound {data : MemoryData p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) : event.1 = 0 → event.2.1 < memoryEpoch data :=
  Trace.Proofs.Transfer.raw_seed_bound (data := transferData data) member

end Airbender.Delegation.Proofs
