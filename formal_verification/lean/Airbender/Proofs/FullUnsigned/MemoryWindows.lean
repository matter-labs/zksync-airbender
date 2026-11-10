import Airbender.Proofs.FullUnsigned.RequestSchedule

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- A fulfillment event lies in exactly its caller's CPU cycle. Alignment
and unique native state clocks exclude every other instruction window. -/
theorem unrolled_full_fulfillment_window
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (request : Delegation.Requests.Request babyBearModulus)
    (member : request ∈ workers.rows.map Delegation.Requests.fulfillment ++
      splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached))
    (event : MemoryAccess) (eventClock : event.1 = (timeOfPair request.time).value + 3)
    (row : Trace.Row babyBearModulus PooledFamily) (present : row ∈ trace.rows) :
    ((decodeTimestamp row.assignment row.columns.initialTime).value < event.1 ∧
      event.1 ≤ (decodeTimestamp row.assignment row.columns.initialTime).value + 4) ↔
      row.family = .addSub ∧ Delegation.Requests.Selected row.assignment ∧
        request = Delegation.Requests.caller row.assignment := by
  obtain ⟨caller, included, family, selected, equal, _, time⟩ :=
    unrolled_full_fulfillment_slot accepted equations active initialClock initialAligned request member
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have aligned (current : Trace.Row babyBearModulus PooledFamily) (currentMember : current ∈ trace.rows) :
      (decodeTimestamp current.assignment current.columns.initialTime).value % 4 = 0 := by
    simpa [Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using
      (clocks current currentMember).2
  have rowAligned := aligned row present
  have callerAligned := aligned caller included
  have location : event.1 = (decodeTimestamp caller.assignment caller.columns.initialTime).value + 4 := by
    omega
  constructor
  · intro interval
    have sameClock : (decodeTimestamp caller.assignment caller.columns.initialTime).value =
        (decodeTimestamp row.assignment row.columns.initialTime).value := by omega
    have unique := state_clocks_unique (by decide)
      (by decide +kernel : SerializedInverse.Clock babyBearModulus)
      accepted.cpuEquations accepted.states initialClock initialAligned
    have same : caller = row := List.inj_on_of_nodup_map unique included present sameClock
    subst caller
    exact ⟨family, selected, equal⟩
  · rintro ⟨rowFamily, rowSelected, matched⟩
    let callers := trace.rows.filter fun source => source.family == .addSub &&
      decide (Delegation.Requests.Selected source.assignment)
    have first : caller ∈ callers := List.mem_filter.mpr ⟨included, by
      simp only [family, beq_self_eq_true, selected, decide_true, Bool.and_self]⟩
    have second : row ∈ callers := List.mem_filter.mpr ⟨present, by
      simp only [rowFamily, beq_self_eq_true, rowSelected, decide_true, Bool.and_self]⟩
    have unique : (callers.map fun source => (Delegation.Requests.caller source.assignment).time).Nodup := by
      simpa only [pooledCalls, List.map_map, Function.comp_def, callers] using
        unrolled_request_times_unique accepted initialClock initialAligned
    have same : caller = row := List.inj_on_of_nodup_map unique first second
      (congrArg Delegation.Requests.Request.time (equal.symm.trans matched))
    subst caller
    omega

/-- A standard worker event belongs to a CPU window exactly when that CPU
row issues this worker's full-width request. -/
theorem unrolled_full_standard_event_window
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (worker : Delegation.Row babyBearModulus) (included : worker ∈ workers.rows)
    (event : MemoryAccess) (eventMember : event ∈ worker.memorySteps.map transferEvent)
    (row : Trace.Row babyBearModulus PooledFamily) (present : row ∈ trace.rows) :
    ((decodeTimestamp row.assignment row.columns.initialTime).value < event.1 ∧
      event.1 ≤ (decodeTimestamp row.assignment row.columns.initialTime).value + 4) ↔
      row.family = .addSub ∧ Delegation.Requests.Selected row.assignment ∧
        Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment := by
  have member : Delegation.Requests.fulfillment worker ∈
      workers.rows.map Delegation.Requests.fulfillment ++
        splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached) :=
    List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨worker, included, rfl⟩))
  apply unrolled_full_fulfillment_window accepted equations active initialClock initialAligned
    _ member event ?_ row present
  obtain ⟨edge, inWorker, rfl⟩ := List.mem_map.mp eventMember
  obtain ⟨port, physical, rfl⟩ := List.mem_map.mp inWorker
  have native : port ∈ worker.ports := by simpa using physical
  have clock := (unrolled_request_clock_bounds accepted initialClock initialAligned).2.1 _ member
  have offset := Delegation.Proofs.port_offset worker native
  have written := (write_time_of_room (by decide) (offset := port.clock.offset)
    (base := rawPair worker.assignment worker.columns.invocation) clock.1
    (by simpa only [offset, Delegation.Requests.fulfillment, timeOfPair, rawPair] using clock.2)).2
  have value : (timeOfPair (worker.writeToken port).time).value =
      (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 2 := by
    simpa only [Delegation.Row.writeToken, offset, Delegation.Requests.fulfillment] using written
  change (timeOfPair (worker.writeToken port).time).value + 1 = _
  omega

/-- The same exact-window criterion holds for each current split worker
layout in both cache modes. -/
theorem unrolled_full_split_event_window
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (worker : Keccak.Split.Native.Row babyBearModulus) (included : worker ∈ splitWorkers.rows)
    (event : MemoryAccess) (eventMember : event ∈ (worker.memorySteps splitWorkers.cached).map transferEvent)
    (row : Trace.Row babyBearModulus PooledFamily) (present : row ∈ trace.rows) :
    ((decodeTimestamp row.assignment row.columns.initialTime).value < event.1 ∧
      event.1 ≤ (decodeTimestamp row.assignment row.columns.initialTime).value + 4) ↔
      row.family = .addSub ∧ Delegation.Requests.Selected row.assignment ∧
        worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment := by
  have member : worker.fulfillment splitWorkers.cached ∈
      workers.rows.map Delegation.Requests.fulfillment ++
        splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached) :=
    List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨worker, included, rfl⟩))
  apply unrolled_full_fulfillment_window accepted equations active initialClock initialAligned
    _ member event ?_ row present
  obtain ⟨edge, inWorker, rfl⟩ := List.mem_map.mp eventMember
  obtain ⟨port, physical, rfl⟩ := List.mem_map.mp inWorker
  have native : port ∈ worker.ports splitWorkers.cached := by simpa using physical
  have clock := (unrolled_request_clock_bounds accepted initialClock initialAligned).2.1 _ member
  have offset := Keccak.Split.Native.Proofs.port_offset splitWorkers.cached worker native
  have written := (write_time_of_room (by decide) (offset := port.clock.offset)
    (base := rawPair worker.assignment (worker.columns splitWorkers.cached).invocation) clock.1
    (by simpa only [offset, Keccak.Split.Native.Row.fulfillment, timeOfPair, rawPair] using clock.2)).2
  have value : (timeOfPair (worker.writeToken splitWorkers.cached port).time).value =
      (timeOfPair (worker.fulfillment splitWorkers.cached).time).value + 2 := by
    simpa only [Keccak.Split.Native.Row.writeToken, offset, Keccak.Split.Native.Row.fulfillment] using written
  change (timeOfPair (worker.writeToken splitWorkers.cached port).time).value + 1 = _
  omega

end Airbender.Compiler.MachineTargets.Proofs
