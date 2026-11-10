import Airbender.Proofs.FullUnsigned.BootExecution
import Airbender.Proofs.UnifiedReduced.SupportedUsePrefix

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open Delegation.Caller AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Cut the actual CPU pool before one native state boundary. -/
def unrolledFullPrefixTrace (trace : PooledTrace babyBearModulus)
    (point : PCState.State babyBearModulus) (memory : List (MemoryToken babyBearModulus)) :=
  {trace with rows := trace.rows.filter fun row => decide (row.clock < (timeOfPair point.timestamp).value)
              terminal := point
              terminalMemory := memory}

/-- Keep standard workers whose derived event clock precedes the next cycle. -/
def unrolledFullPrefixWorkers (workers : Delegation.MemoryData babyBearModulus)
    (point : PCState.State babyBearModulus) :=
  {workers with
    rows := workers.rows.filter fun row =>
      decide ((timeOfPair (Delegation.Requests.fulfillment row).time).value + 3 ≤
        (timeOfPair point.timestamp).value)}

/-- Use the same native cut for split workers in either cache mode. -/
def unrolledFullPrefixSplitWorkers (workers : Keccak.Split.Native.MemoryData babyBearModulus)
    (point : PCState.State babyBearModulus) :=
  {workers with
    rows := workers.rows.filter fun row =>
      decide ((timeOfPair (row.fulfillment workers.cached).time).value + 3 ≤
        (timeOfPair point.timestamp).value)}

omit [Fact babyBearModulus.Prime] in
private theorem filter_groups {A B : Type} (rows : List A) (group : A → List B)
    (choose : A → Bool) (selected : B → Bool)
    (agreement : ∀ row ∈ rows, ∀ item ∈ group row, selected item = choose row) :
    (rows.filter choose).flatMap group = (rows.flatMap group).filter selected := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
    have tail := ih (fun row member => agreement row (List.mem_cons_of_mem _ member))
    cases chosen : choose first with
    | true =>
      have all : (group first).filter selected = group first := List.filter_eq_self.mpr
        (fun item member => (agreement first List.mem_cons_self item member).trans chosen)
      simpa only [List.filter_cons, chosen, ↓reduceIte, List.flatMap_cons,
        List.filter_append, List.append_eq, all] using congrArg (List.append (group first)) tail
    | false =>
      have none : (group first).filter selected = [] := List.filter_eq_nil_iff.mpr (by
        intro item member picked
        have same := (agreement first List.mem_cons_self item member).symm.trans picked
        rw [chosen] at same
        cases same)
      simpa only [List.filter_cons, chosen, Bool.false_eq_true, if_false, List.flatMap_cons,
        List.filter_append, none, List.nil_append] using tail

private theorem standard_event_clock
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ workers.rows)
    {edge : MemoryToken babyBearModulus × MemoryToken babyBearModulus} (present : edge ∈ worker.memorySteps) :
    (transferEvent edge).1 = (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 3 := by
  obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
  have native : port ∈ worker.ports := by simpa using included
  have request := (unrolled_request_clock_bounds accepted initialClock initialAligned).2.1 _
    (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨worker, member, rfl⟩)))
  have offset := Delegation.Proofs.port_offset worker native
  have written := (write_time_of_room (by decide) (offset := port.clock.offset)
    (base := rawPair worker.assignment worker.columns.invocation) request.1
    (by simpa only [offset, Delegation.Requests.fulfillment, timeOfPair, rawPair] using request.2)).2
  have time : (timeOfPair (worker.writeToken port).time).value =
      (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 2 := by
    simpa only [Delegation.Row.writeToken, offset, Delegation.Requests.fulfillment] using written
  change (timeOfPair (worker.writeToken port).time).value + 1 = _
  omega

private theorem split_event_clock
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {worker : Keccak.Split.Native.Row babyBearModulus} (member : worker ∈ splitWorkers.rows)
    {edge : MemoryToken babyBearModulus × MemoryToken babyBearModulus}
    (present : edge ∈ worker.memorySteps splitWorkers.cached) :
    (transferEvent edge).1 = (timeOfPair (worker.fulfillment splitWorkers.cached).time).value + 3 := by
  obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
  have native : port ∈ worker.ports splitWorkers.cached := by simpa using included
  have request := (unrolled_request_clock_bounds accepted initialClock initialAligned).2.1 _
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨worker, member, rfl⟩)))
  have offset := Keccak.Split.Native.Proofs.port_offset splitWorkers.cached worker native
  have written := (write_time_of_room (by decide) (offset := port.clock.offset)
    (base := rawPair worker.assignment (worker.columns splitWorkers.cached).invocation) request.1
    (by simpa only [offset, Keccak.Split.Native.Row.fulfillment, timeOfPair, rawPair] using request.2)).2
  have time : (timeOfPair (worker.writeToken splitWorkers.cached port).time).value =
      (timeOfPair (worker.fulfillment splitWorkers.cached).time).value + 2 := by
    simpa only [Keccak.Split.Native.Row.writeToken, offset, Keccak.Split.Native.Row.fulfillment] using written
  change (timeOfPair (worker.writeToken splitWorkers.cached port).time).value + 1 = _
  omega

/-- The combined native prefix has exactly the transfers before its cut.
No valid command, round mask, supported argument or reference result is needed. -/
theorem unrolled_full_prefix_steps
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ trace.rows)
    (positive : 0 < next.clock) (memory : List (MemoryToken babyBearModulus)) :
    (unrolledFullMemoryData (unrolledFullPrefixTrace trace next.start memory)
      (unrolledFullPrefixWorkers workers next.start) (unrolledFullPrefixSplitWorkers splitWorkers next.start)).steps =
      Transfer.beforeSteps (unrolledFullMemoryData trace workers splitWorkers) (next.clock - 1) := by
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have aligned (row : Trace.Row babyBearModulus PooledFamily) (present : row ∈ trace.rows) : row.clock % 4 = 0 := by
    simpa [Trace.Row.clock, decodeTimestamp, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
      using (clocks row present).2
  have cut := aligned next member
  let selected := fun edge : MemoryToken babyBearModulus × MemoryToken babyBearModulus =>
    decide ((timeOfPair edge.2.time).value ≤ next.clock - 1)
  have machine := filter_groups trace.rows
    (fun row => (machinePorts row).toList.map fun port =>
      (readToken row.assignment port, writeToken row.columns row.assignment port))
    (fun row => decide (row.clock < next.clock)) selected (by
      intro row included edge present
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
      have rowAligned := aligned row included
      have event : transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port) ∈
          machineEvents row := List.mem_map.mpr ⟨port, portMember, rfl⟩
      obtain ⟨offset, small, time⟩ := unrolled_cpu_event_time accepted initialClock initialAligned row included _ event
      change (timeOfPair (writeToken row.columns row.assignment port).time).value + 1 = row.clock + offset + 1 at time
      apply Bool.eq_iff_iff.mpr
      simp only [selected, decide_eq_true_eq]
      omega)
  have standard := filter_groups workers.rows Delegation.Row.memorySteps
    (fun row => decide ((timeOfPair (Delegation.Requests.fulfillment row).time).value + 3 ≤ next.clock)) selected (by
      intro row included edge present
      have time := standard_event_clock accepted initialClock initialAligned included present
      change (timeOfPair edge.2.time).value + 1 = _ at time
      apply Bool.eq_iff_iff.mpr
      simp only [selected, decide_eq_true_eq]
      omega)
  have split := filter_groups splitWorkers.rows (Keccak.Split.Native.Row.memorySteps splitWorkers.cached)
    (fun row => decide ((timeOfPair (row.fulfillment splitWorkers.cached).time).value + 3 ≤ next.clock)) selected (by
      intro row included edge present
      have time := split_event_clock accepted initialClock initialAligned included present
      change (timeOfPair edge.2.time).value + 1 = _ at time
      apply Bool.eq_iff_iff.mpr
      simp only [selected, decide_eq_true_eq]
      omega)
  change _ = ((unrolledFullMemoryData trace workers splitWorkers).steps.filter selected)
  simp only [unrolledFullMemoryData, unrolledFullPrefixTrace, unrolledFullPrefixWorkers, unrolledFullPrefixSplitWorkers,
    pooledSteps, Delegation.MemoryData.steps, Keccak.Split.Native.MemoryData.steps, List.filter_append]
  have boundary : (timeOfPair next.start.timestamp).value = next.clock := rfl
  rw [boundary, machine, standard, split]

/-- The actual native worker transfer has its derived invocation event clock. -/
theorem unrolled_full_standard_event_clock
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ workers.rows)
    {edge : MemoryToken babyBearModulus × MemoryToken babyBearModulus} (present : edge ∈ worker.memorySteps) :
    (transferEvent edge).1 = (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 3 := by
  exact standard_event_clock accepted initialClock initialAligned member present

/-- The actual native worker transfer has its derived invocation event clock. -/
theorem unrolled_full_split_event_clock
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {worker : Keccak.Split.Native.Row babyBearModulus} (member : worker ∈ splitWorkers.rows)
    {edge : MemoryToken babyBearModulus × MemoryToken babyBearModulus}
    (present : edge ∈ worker.memorySteps splitWorkers.cached) :
    (transferEvent edge).1 = (timeOfPair (worker.fulfillment splitWorkers.cached).time).value + 3 := by
  exact split_event_clock accepted initialClock initialAligned member present

end Airbender.Compiler.MachineTargets.Proofs
