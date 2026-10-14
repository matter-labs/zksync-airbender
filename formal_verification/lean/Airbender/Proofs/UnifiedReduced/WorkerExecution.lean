import Airbender.Proofs.UnifiedReduced.UnissuedWorkers

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Full invocation uniqueness also groups the zero-clock worker. Strict native
    order places machine events after that group, without a boot-clock premise. -/
theorem all_worker_clock_group [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (image : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup)
    {events : List MemoryAccess} (permutation : events.Perm (data.mixedSteps.map transferEvent))
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) :
    (events.filter fun event => decide (event.1 = workerClock worker)).Perm
      (worker.memorySteps.map transferEvent) := by
  have requests := request_binding hp inverse accepted.toRequestChecks publicProgram
  by_cases live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)
  · exact worker_clock_group hp inverse accepted.toRequestChecks publicProgram requests permutation member live
  have zero : (Delegation.Requests.fulfillment worker).time = (0, 0) := not_not.mp live
  have early : workerClock worker = 3 := by
    change (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 3 = 3
    simp [zero, timeOfPair, Timestamp.value]
  have machineEmpty : ((data.machine.rows.flatMap (fun row => (machinePorts row).toList.map fun port =>
      transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port))).filter
      fun event => decide (event.1 = workerClock worker)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event included same
    obtain ⟨row, rowMember, included⟩ := List.mem_flatMap.mp included
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
    have floor := machine_native_clock_positive hp inverse accepted publicProgram image rowMember
    have time := mixed_machine_time_of_program hp inverse accepted publicProgram rowMember
      (machine_port_native row (by simpa using portMember))
    have time : (transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port)).1 =
        Delegation.Caller.startClock row + port.clock.offset + 1 := by
      simpa [transferEvent, MemoryPort.event, Delegation.Caller.startClock, Trace.Row.clock] using time
    have equal := of_decide_eq_true same
    rw [time, early] at equal
    omega
  have clocks := (worker_invocation_uniqueness hp inverse accepted publicProgram image distinct).clocks
  have unique : (data.workers.rows.map workerClock).Nodup := by
    have shifted := clocks.map (f := fun clock => clock + 3) (by intro a b same; dsimp at same; omega)
    rw [List.map_map] at shifted
    change (data.workers.rows.map workerClock).Nodup at shifted
    exact shifted
  let access := fun other : Delegation.Row p => other.memorySteps.map transferEvent
  have workers := Delegation.Proofs.call_group_perm workerClock access unique
    (List.Perm.refl (data.workers.rows.flatMap access)) (by
      intro other present event included
      exact worker_event_clock (by omega) requests present included) member
  have projected := permutation.filter fun event => decide (event.1 = workerClock worker)
  have actual : (data.mixedSteps.map transferEvent).filter (fun event => decide (event.1 = workerClock worker)) =
      (data.workers.rows.flatMap access).filter (fun event => decide (event.1 = workerClock worker)) := by
    simp only [RequestTrace.mixedSteps, List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
      List.filter_append, machineEmpty, List.nil_append, Delegation.MemoryData.steps, access]
  exact (actual ▸ projected).trans workers

/-- Every worker has actual call states; an unissued worker starts directly at
    the public initial state. This needs only the architectural seed and alignment,
    with no operation masks, valid bigint control or positive invocation premise. -/
theorem all_worker_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before after : State}
    {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (image : initialImage before cells = some data.machine.initialMemory)
    (distinctCells : (cells.map Cell.addressCode).Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {events : List MemoryAccess} (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : SailHistory cells events before after) :
    ∀ worker ∈ data.workers.rows,
      Delegation.CallExecution cells events before after worker ∧
      ((Delegation.Requests.fulfillment worker).time = (0, 0) →
        UnissuedPrefixExecution cells events before after worker) := by
  have requests := request_binding hp inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts hp inverse accepted publicProgram image requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨image, distinctCells⟩
  have rawUnique := Transfer.raw_address_clocks_distinct facts initialized.toBoundaryInputs
  have nativeSub : (data.mixedSteps.map transferEvent).Sublist (Transfer.rawEvents (mixedData data)) :=
    List.sublist_append_right _ _
  have nativeUnique := rawUnique.sublist (nativeSub.map (fun event => (event.1, event.2.1)))
  have actualUnique : (events.map fun event => (event.1, event.2.1)).Nodup :=
    (permutation.map (fun event => (event.1, event.2.1))).nodup_iff.mpr nativeUnique
  intro worker member
  let current := events.filter fun event => decide (event.1 = workerClock worker)
  have grouped := all_worker_clock_group hp inverse accepted publicProgram image distinctCells permutation member
  have currentSub : current.Sublist events := List.filter_sublist
  have keyUnique := actualUnique.sublist (currentSub.map (fun event => (event.1, event.2.1)))
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
  have readable := history_cells_readable past aligned (by
    intro cell present
    obtain ⟨_, _, value, read, _⟩ := image_cell_source image cell present
    exact ⟨value, read⟩)
  have noZero : ∀ event ∈ current, event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (grouped.mem_iff.mp included)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
    exact Delegation.Proofs.port_not_zero worker (by simpa using portMember)
  have observations := Delegation.Proofs.atomic_observations call aligned noZero readable distinct
  have ports : ∀ port ∈ worker.ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code worker.assignment ∧
      cell.read start = .ok (readToken worker.assignment port).word.toBitVec start ∧
      cell.read finish = .ok (worker.writeToken port).word.toBitVec finish := by
    intro port present
    have included : transferEvent (readToken worker.assignment port, worker.writeToken port) ∈ current := by
      apply grouped.mem_iff.mpr
      exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩, rfl⟩
    simpa only [transferEvent, readToken, MemoryToken.word, memoryWord, Word.toBitVec, Word.value] using observations _ included
  constructor
  · exact ⟨_, current, _, start, finish, split, grouped, past, call, newer, ports⟩
  · intro zero
    have early : workerClock worker = 3 := by
      change (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 3 = 3
      simp [zero, timeOfPair, Timestamp.value]
    have empty : (events.filter fun event => decide (event.1 < workerClock worker)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro event present less
      obtain ⟨edge, included, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp present)
      have floor := mixed_write_floor hp inverse accepted publicProgram image edge included
      have less := of_decide_eq_true less
      change (timeOfPair edge.2.time).value + 1 < workerClock worker at less
      rw [early] at less
      omega
    rw [empty] at split past
    cases past
    exact ⟨current, _, finish, by simpa only [List.append_nil] using split,
      grouped, call, newer, ports⟩

/-- The existing initialized realization supplies the single history; grouping
    adds every worker's actual states and isolates its possible unissued prefix. -/
theorem mixed_worker_execution_effects
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells) :
    MixedWorkerExecution data before cells := by
  obtain ⟨events, after, permutation, order, history, _, _, terminal⟩ :=
    (mixed_memory_effects accepted inputs).execution
  have workers := all_worker_execution (by decide) (by decide) accepted inputs.publicProgram
    inputs.initialization inputs.distinct inputs.aligned permutation order history
  exact ⟨events, after, permutation, order, history,
    fun worker member => (workers worker member).1,
    fun worker member => (workers worker member).2, terminal⟩

end Airbender.UnifiedReduced.Caller.Proofs
