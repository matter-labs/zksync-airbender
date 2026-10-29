import Airbender.Review.Helpers.Delegation.Schedule
import Airbender.Proofs.Reduced.StreamMemory
import Airbender.Proofs.Trace.HistoryWindow

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

def machineEvents (row : Trace.Row p PooledFamily) : List MemoryAccess :=
  (machinePorts row).toList.map fun port =>
    transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port)

theorem machine_clocks_unique [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses) :
    (data.machine.rows.map Delegation.Caller.startClock).Nodup := by
  exact state_clocks_unique hp inverse
    accepted.constraints accepted.states inputs.initialClock inputs.initialAligned

theorem machine_clock_facts [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows) :
    Delegation.Caller.startClock row % 4 = 0 ∧
      Delegation.Caller.finishClock row = Delegation.Caller.startClock row + 4 := by
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned row member
  refine ⟨?_, ClockLaws.advance hp inverse data.machine.rom row (accepted.constraints row member) clock.1⟩
  simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using clock.2

theorem machine_event_time [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    {event : MemoryAccess} (present : event ∈ machineEvents row) :
    ∃ offset < 3, event.1 = Delegation.Caller.startClock row + offset + 1 := by
  obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
  have native := machine_port_native row (by simpa using included)
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned row member
  have offsets : row.ports.toList.map (fun port => port.clock.offset) = [0, 1, 2] :=
    @ClockLaws.offsets PooledFamily inferInstance p inferInstance inferInstance row
  have selected : port.clock.offset ∈ row.ports.toList.map (fun port => port.clock.offset) :=
    List.mem_map.mpr ⟨port, by simpa using native, rfl⟩
  rw [offsets] at selected
  have bound : port.clock.offset < 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
    omega
  have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
    clock.1 clock.2 (by omega : port.clock.offset < 4)).2
  exact ⟨port.clock.offset, bound, by simpa only [transferEvent, Delegation.Caller.startClock, Trace.Row.clock, writeToken, decodeTimestamp, timeOfPair, rawPair] using congrArg (fun n => n + 1) time⟩

theorem machine_event_window [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {row other : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows) (included : other ∈ data.machine.rows)
    {event : MemoryAccess} (present : event ∈ machineEvents other) :
    (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row) ↔ other = row := by
  have current := machine_clock_facts hp inverse accepted inputs member
  have previous := machine_clock_facts hp inverse accepted inputs included
  obtain ⟨offset, bound, time⟩ := machine_event_time hp inverse accepted inputs included present
  constructor
  · intro interval
    have same : Delegation.Caller.startClock other = Delegation.Caller.startClock row := by omega
    exact List.inj_on_of_nodup_map (machine_clocks_unique hp inverse accepted inputs) included member same
  · intro same
    subst other
    omega


end Airbender.AddSub.Modular.External.Caller.Proofs
