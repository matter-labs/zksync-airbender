import Airbender.Proofs.UnifiedReduced.MixedMemoryClocks
import Airbender.Proofs.Delegation.CallHistory
import Airbender.Proofs.Delegation.Atomic

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def workerClock (worker : Delegation.Row p) :=
  (decodeTimestamp worker.assignment worker.columns.invocation).value + 3

theorem worker_event_clock [Fact p.Prime] (hp : timestampBase < p)
    {data : RequestTrace p} {before : State} (requests : RequestBinding data before)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    {event : MemoryAccess} (present : event ∈ worker.memorySteps.map transferEvent) :
    event.1 = workerClock worker := by
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
  have native : port ∈ worker.ports := by simpa using portMember
  have time := (write_time_of_room hp (base := rawPair worker.assignment worker.columns.invocation)
    (offset := port.clock.offset) (requests.clocks worker member).1 (by
      simpa only [Delegation.Proofs.port_offset worker native, decodeTimestamp, rawPair]
        using (requests.clocks worker member).2)).2
  change (timeOfPair (worker.writeToken port).time).value =
    (decodeTimestamp worker.assignment worker.columns.invocation).value + port.clock.offset at time
  simp only [transferEvent, time, Delegation.Proofs.port_offset worker native, workerClock]

theorem live_worker_clock [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    (live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)) :
    4 ≤ workerClock worker ∧ workerClock worker % 4 = 0 := by
  have present : Delegation.Requests.fulfillment worker ∈ data.fulfillments.filter
      (fun call => decide (Delegation.Requests.Live call)) :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨worker, member, rfl⟩, decide_eq_true live⟩
  obtain ⟨caller, included, same⟩ := List.mem_map.mp (requests.fulfilled.mem_iff.mpr present)
  obtain ⟨actual, matched, _⟩ := requests.workers caller included
  obtain ⟨_, _, only⟩ := Delegation.Requests.Proofs.unique_fulfillment
    requests.fulfilled requests.invocations.1 (List.mem_map.mpr ⟨caller, included, rfl⟩)
  have equal : worker = actual := (only worker ⟨member, same.symm⟩).trans
    (only actual ⟨matched.1, matched.2.1⟩).symm
  subst actual
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned caller (List.mem_filter.mp included).1
  have aligned : Delegation.Caller.startClock caller % 4 = 0 := by
    simpa [Delegation.Caller.startClock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using clock.2
  have slot : workerClock worker = Delegation.Caller.startClock caller + 4 := by
    dsimp only [workerClock]
    rw [matched.2.2.invocation]
  rw [slot]
  omega

theorem worker_clock_injective [Fact p.Prime]
    {data : RequestTrace p} {before : State} (requests : RequestBinding data before)
    {first last : Delegation.Row p} (fm : first ∈ data.workers.rows) (lm : last ∈ data.workers.rows)
    (fl : Delegation.Requests.Live (Delegation.Requests.fulfillment first))
    (ll : Delegation.Requests.Live (Delegation.Requests.fulfillment last))
    (same : workerClock first = workerClock last) : first = last := by
  let issued := data.workers.rows.filter fun worker => decide (Delegation.Requests.Live (Delegation.Requests.fulfillment worker))
  have unique : (issued.map (fun worker => (Delegation.Requests.fulfillment worker).time)).Nodup := by
    simpa only [issued, List.filter_map, RequestTrace.fulfillments, List.map_map, Function.comp_def]
      using requests.invocations.2
  have equal : (Delegation.Requests.fulfillment first).time = (Delegation.Requests.fulfillment last).time := by
    have fb := (requests.clocks first fm).1.1
    have lb := (requests.clocks last lm).1.1
    have value : (decodeTimestamp first.assignment first.columns.invocation).value =
        (decodeTimestamp last.assignment last.columns.invocation).value := by
      dsimp only [workerClock] at same
      omega
    dsimp [Timestamp.value, timestampBase] at value
    dsimp [timestampBase] at fb lb
    have lo : (decodeTimestamp first.assignment first.columns.invocation).lo =
        (decodeTimestamp last.assignment last.columns.invocation).lo := by omega
    have hi : (decodeTimestamp first.assignment first.columns.invocation).hi =
        (decodeTimestamp last.assignment last.columns.invocation).hi := by omega
    apply Prod.ext
    · exact ZMod.val_injective p lo
    · exact ZMod.val_injective p hi
  exact List.inj_on_of_nodup_map unique (List.mem_filter.mpr ⟨fm, decide_eq_true fl⟩)
    (List.mem_filter.mpr ⟨lm, decide_eq_true ll⟩) equal

theorem machine_event_separate [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    {port : MemoryPort} (present : port ∈ machinePorts row) :
    (transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port)).1 % 4 ≠ 0 := by
  have native := machine_port_native row present
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned row member
  have aligned : Delegation.Caller.startClock row % 4 = 0 := by
    simpa [Delegation.Caller.startClock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using clock.2
  have offset : port.clock.offset < 3 := by
    have mapped : port.clock.offset ∈ row.ports.toList.map (fun port => port.clock.offset) :=
      List.mem_map.mpr ⟨port, by simpa using native, rfl⟩
    have offsets : row.ports.toList.map (fun port => port.clock.offset) = [0, 1, 2] :=
      @ClockLaws.offsets UnifiedFamily inferInstance p inferInstance inferInstance row
    rw [offsets] at mapped
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mapped
    omega

  have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
    clock.1 clock.2 (by omega : port.clock.offset < 4)).2
  change (timeOfPair (writeToken row.columns row.assignment port).time).value =
    Delegation.Caller.startClock row + port.clock.offset at time
  change ((timeOfPair (writeToken row.columns row.assignment port).time).value + 1) % 4 ≠ 0
  rw [time]
  omega

private theorem filter_flatMap (rows : List α) (predicate : α → Bool) (f : α → List β) :
    (rows.filter predicate).flatMap f = rows.flatMap (fun row => if predicate row then f row else []) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases result : predicate row <;> simp [result, ih]

theorem worker_clock_group [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before)
    {events : List MemoryAccess} (permutation : events.Perm (data.mixedSteps.map transferEvent))
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    (live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)) :
    (events.filter fun event => decide (event.1 = workerClock worker)).Perm (worker.memorySteps.map transferEvent) := by
  have target := live_worker_clock hp inverse accepted inputs requests member live
  have projected := permutation.filter fun event => decide (event.1 = workerClock worker)
  have machineEmpty : ((data.machine.rows.flatMap (fun row => (machinePorts row).toList.map fun port =>
      transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port))).filter
      fun event => decide (event.1 = workerClock worker)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event included same
    obtain ⟨row, rowMember, included⟩ := List.mem_flatMap.mp included
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
    have separate := machine_event_separate hp inverse accepted inputs rowMember (by simpa using portMember)
    have equal := of_decide_eq_true same
    rw [equal, target.2] at separate
    exact separate rfl
  let issued := data.workers.rows.filter fun other => decide (Delegation.Requests.Live (Delegation.Requests.fulfillment other))
  have unique : (issued.map workerClock).Nodup := by
    have clocks : (issued.map (fun other => (Delegation.Requests.fulfillment other).time)).Nodup := by
      simpa only [issued, List.filter_map, RequestTrace.fulfillments, List.map_map, Function.comp_def]
        using requests.invocations.2
    have distinct : issued.Nodup := clocks.of_map _
    exact distinct.map_on (fun first fm last lm same => worker_clock_injective requests
      (List.mem_filter.mp fm).1 (List.mem_filter.mp lm).1
      (of_decide_eq_true (List.mem_filter.mp fm).2) (of_decide_eq_true (List.mem_filter.mp lm).2) same)
  have selected : worker ∈ issued := List.mem_filter.mpr ⟨member, decide_eq_true live⟩
  let access := fun other : Delegation.Row p => other.memorySteps.map transferEvent
  have liveOnly : ((data.workers.rows.flatMap access).filter fun event => decide (event.1 = workerClock worker)) =
      ((issued.flatMap access).filter fun event => decide (event.1 = workerClock worker)) := by
    rw [List.filter_flatMap, List.filter_flatMap]
    change _ = (data.workers.rows.filter _).flatMap _
    rw [filter_flatMap]
    apply List.flatMap_congr
    intro other included
    by_cases actual : Delegation.Requests.Live (Delegation.Requests.fulfillment other)
    · simp only [actual, decide_true, if_true]
    · simp only [actual, decide_false]
      apply List.filter_eq_nil_iff.mpr
      intro event present equal
      have time := worker_event_clock (by omega) requests included present
      have zero : (Delegation.Requests.fulfillment other).time = (0, 0) := not_not.mp actual
      have early : workerClock other = 3 := by
        change rawPair other.assignment other.columns.invocation = (0, 0) at zero
        change (timeOfPair (rawPair other.assignment other.columns.invocation)).value + 3 = 3
        rw [zero]
        norm_num [timeOfPair, Timestamp.value, timestampBase]
      have same := of_decide_eq_true equal
      rw [time, early] at same
      omega
  have workers := Delegation.Proofs.call_group_perm workerClock access unique
    (List.Perm.refl (issued.flatMap access)) (by
      intro other present event included
      exact worker_event_clock (by omega) requests (List.mem_filter.mp present).1 included) selected
  have actual : (data.mixedSteps.map transferEvent).filter (fun event => decide (event.1 = workerClock worker)) =
      (issued.flatMap access).filter (fun event => decide (event.1 = workerClock worker)) := by
    simp only [RequestTrace.mixedSteps, List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
      List.filter_append, machineEmpty, List.nil_append, Delegation.MemoryData.steps]
    exact liveOnly
  exact (actual ▸ projected).trans workers

theorem mixed_worker_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (requests : RequestBinding data initial)
    {events : List MemoryAccess} {after : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : SailHistory cells events initial after) :
    ∀ worker ∈ data.workers.rows, Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      Delegation.CallExecution cells events initial after worker := by
  have facts := mixed_memory_facts hp inverse accepted inputs requests
  have initialized : Transfer.Inputs (mixedData data) initial cells := ⟨inputs.initialization, inputs.distinct⟩
  have rawUnique := Transfer.raw_address_clocks_distinct facts initialized
  have nativeSub : (data.mixedSteps.map transferEvent).Sublist (Transfer.rawEvents (mixedData data)) :=
    List.sublist_append_right _ _
  have nativeUnique : ((data.mixedSteps.map transferEvent).map fun event => (event.1, event.2.1)).Nodup :=
    rawUnique.sublist (nativeSub.map (fun event => (event.1, event.2.1)))
  have actualUnique : (events.map fun event => (event.1, event.2.1)).Nodup :=
    (permutation.map (fun event => (event.1, event.2.1))).nodup_iff.mpr nativeUnique
  intro worker member live
  let current := events.filter fun event => decide (event.1 = workerClock worker)
  have grouped := worker_clock_group hp inverse accepted.toRequestChecks inputs.publicProgram requests permutation member live
  have currentSub : current.Sublist events := List.filter_sublist
  have keyUnique : (current.map fun event => (event.1, event.2.1)).Nodup :=
    actualUnique.sublist (currentSub.map (fun event => (event.1, event.2.1)))
  have time : ∀ event ∈ current, event.1 = workerClock worker := by
    intro event present
    exact of_decide_eq_true (List.mem_filter.mp present).2
  have constant : (current.map fun event => (event.1, event.2.1)) =
      (current.map fun event => event.2.1).map (fun address => (workerClock worker, address)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro event present
    simp only [time event present, Function.comp_def]
  rw [constant] at keyUnique
  have distinct : (current.map fun event => event.2.1).Nodup := keyUnique.of_map _
  obtain ⟨start, finish, split, past, call, newer⟩ := Delegation.Proofs.clock_slice ordered history (workerClock worker)
  have readable := history_cells_readable past inputs.aligned (by
    intro cell present
    obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.initialization cell present
    exact ⟨value, read⟩)
  have noZero : ∀ event ∈ current, event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (grouped.mem_iff.mp included)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
    exact Delegation.Proofs.port_not_zero worker (by simpa using portMember)
  have observations := Delegation.Proofs.atomic_observations call inputs.aligned noZero readable distinct
  refine ⟨events.filter (fun event => decide (event.1 < workerClock worker)), current,
    events.filter (fun event => decide (workerClock worker < event.1)), start, finish,
    split, grouped, past, call, newer, ?_⟩
  intro port present
  have included : transferEvent (readToken worker.assignment port, worker.writeToken port) ∈ current := by
    apply grouped.mem_iff.mpr
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩, rfl⟩
  simpa only [transferEvent, readToken, MemoryToken.word, memoryWord, Word.toBitVec, Word.value] using observations _ included

end Airbender.UnifiedReduced.Caller.Proofs
