import Airbender.Proofs.Reduced.ROMExecution
import Airbender.Proofs.UnifiedReduced.SupportedUsePrefix

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- A prefix ending at a native instruction boundary. Worker selection uses
its derived write-event clock, not a supplied occurrence or bundle plan. -/
def supportedPrefix {p : Nat} [Fact p.Prime] (data : RequestTrace p)
    (point : PCState.State p) (memory : List (MemoryToken p)) : RequestTrace p :=
  let cut := (timeOfPair point.timestamp).value
  { machine := { data.machine with
      rows := data.machine.rows.filter fun row => decide (Delegation.Caller.startClock row < cut)
      terminal := point
      terminalMemory := memory }
    workers := { data.workers with
      rows := data.workers.rows.filter fun worker => decide (workerClock worker ≤ cut) }
    program := data.program }

theorem supported_prefix_callers {p : Nat} [Fact p.Prime] (data : RequestTrace p)
    (point : PCState.State p) (memory : List (MemoryToken p)) :
    (supportedPrefix data point memory).callers = data.callers.filter fun row =>
      decide (Delegation.Caller.startClock row < (timeOfPair point.timestamp).value) := by
  simp only [supportedPrefix, RequestTrace.callers, List.filter_filter]
  apply List.filter_congr
  intro row _
  exact Bool.and_comm _ _

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

/-- Active native workers exclude zero invocations in the exact request ledger. -/
theorem native_requests {data : RequestTrace babyBearModulus} {initial : State}
    (accepted : RequestChecks data) (requests : RequestBinding data initial) :
    data.calls.Perm data.fulfillments := by
  have all : data.fulfillments.filter (fun request => decide (Delegation.Requests.Live request)) =
      data.fulfillments := by
    apply List.filter_eq_self.mpr
    intro request member
    obtain ⟨worker, present, rfl⟩ := List.mem_map.mp member
    exact decide_eq_true (Delegation.Proofs.active_invocation_live
      (accepted.workerConstraints worker present) (accepted.workerActive worker present))
  exact all ▸ requests.fulfilled

/-- Every active worker occupies an aligned native instruction boundary. -/
theorem live_worker_clock_aligned {data : RequestTrace babyBearModulus}
    {initial : State} {ca : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial ca)
    (requests : RequestBinding data initial) {worker : Delegation.Row babyBearModulus}
    (member : worker ∈ data.workers.rows)
    (live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)) :
    workerClock worker % 4 = 0 := by
  have schedule := worker_schedule (by decide) (by decide) accepted inputs requests
  obtain ⟨caller, called, _, slot⟩ := live_worker_slot schedule member live
  have clock := (machine_clock_facts (by decide) (by decide) accepted inputs
    (List.mem_filter.mp called).1).1
  dsimp only [workerClock]
  rw [slot.invocation]
  omega

theorem supported_prefix_requests
    {data : RequestTrace babyBearModulus} {initial : State} {ca : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial ca)
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ data.machine.rows)
    (memory : List (MemoryToken babyBearModulus)) :
    Delegation.Requests.Matching (supportedPrefix data next.start memory).calls
      (supportedPrefix data next.start memory).fulfillments := by
  have requests := request_binding_checks (by decide) (by decide) (by decide) accepted inputs
  have ledger := native_requests accepted requests
  have schedule := worker_schedule (by decide) (by decide) accepted inputs requests
  let choose := fun call : Delegation.Requests.Request babyBearModulus =>
    decide ((timeOfPair call.time).value + 3 ≤ Delegation.Caller.startClock next)
  have cut := (machine_clock_facts (by decide) (by decide) accepted inputs member).1
  have calls : (supportedPrefix data next.start memory).calls = data.calls.filter choose := by
    rw [RequestTrace.calls, supported_prefix_callers]
    change _ = (data.callers.map (fun row => Delegation.Requests.caller row.assignment)).filter choose
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro row included
    obtain ⟨worker, ⟨_, matched, slot⟩, _⟩ := schedule.callers row included
    have invocation : (timeOfPair (Delegation.Requests.caller row.assignment).time).value = Delegation.Caller.startClock row + 1 := by
      rw [← matched]
      exact slot.invocation
    have clock := (machine_clock_facts (by decide) (by decide) accepted inputs
      (List.mem_of_mem_filter included)).1
    apply Bool.eq_iff_iff.mpr
    simp only [choose, invocation, Function.comp_def, decide_eq_true_eq]
    change Delegation.Caller.startClock row < Delegation.Caller.startClock next ↔ _
    omega
  have workers : (supportedPrefix data next.start memory).fulfillments = data.fulfillments.filter choose := by
    simp only [supportedPrefix, RequestTrace.fulfillments, List.filter_map]
    rfl
  have filtered := ledger.filter choose
  rw [← calls, ← workers] at filtered
  exact ((filtered.map Delegation.Requests.Request.issued).append
    (filtered.symm.map Delegation.Requests.Request.empty)).trans List.perm_append_comm

/-- Cutting before a real instruction partitions the actual architectural
transfers. This statement has no round-mask or valid-command hypothesis. -/
theorem supported_prefix_steps_native
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (inputs : RequestInputs data initial ca)
    (initialPositive : 0 < (timeOfPair data.machine.initial.timestamp).value)
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ data.machine.rows)
    (memory : List (MemoryToken babyBearModulus)) :
    (supportedPrefix data next.start memory).mixedSteps =
      Transfer.beforeSteps (mixedData data) (Delegation.Caller.startClock next - 1) := by
  have requests := request_binding_checks (by decide) (by decide) (by decide) accepted.toRequestChecks inputs
  have positive := lt_of_lt_of_le initialPositive (machine_clock_floor (by decide) (by decide) accepted.toRequestChecks inputs member)
  have cut := (machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs member).1
  let selected := fun edge : MemoryToken babyBearModulus × MemoryToken babyBearModulus =>
    decide ((timeOfPair edge.2.time).value ≤ Delegation.Caller.startClock next - 1)
  have machines := filter_groups data.machine.rows
    (fun row => (machinePorts row).toList.map fun port =>
      (readToken row.assignment port, writeToken row.columns row.assignment port))
    (fun row => decide (Delegation.Caller.startClock row < Delegation.Caller.startClock next)) selected (by
      intro row included edge present
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
      have clock := (machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs included).1
      have event : transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port) ∈
          machineEvents row := List.mem_map.mpr ⟨port, portMember, rfl⟩
      obtain ⟨offset, bound, time⟩ := machine_event_time (by decide) (by decide)
        accepted.toRequestChecks inputs included event
      change (timeOfPair (writeToken row.columns row.assignment port).time).value + 1 = _ at time
      dsimp only [selected]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega)
  have workers := filter_groups data.workers.rows Delegation.Row.memorySteps
    (fun worker => decide (workerClock worker ≤ Delegation.Caller.startClock next)) selected (by
      intro worker included edge present
      have event := worker_event_clock (by decide) requests included (List.mem_map.mpr ⟨edge, present, rfl⟩)
      change (timeOfPair edge.2.time).value + 1 = workerClock worker at event
      dsimp only [selected]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega)
  change _ = (data.mixedSteps.filter selected)
  simp only [supportedPrefix, RequestTrace.mixedSteps, Delegation.MemoryData.steps, List.filter_append]
  have boundary : (timeOfPair next.start.timestamp).value = Delegation.Caller.startClock next := rfl
  rw [boundary]
  rw [machines, workers]

/-- A genuine accepted native prefix, with its memory frontier obtained from
exact matching. No hash control, bigint command or reference execution is used
to construct the prefix. -/
theorem supported_prefix_accepted_native
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (inputs : RequestInputs data initial ca)
    (seed : ∀ token ∈ data.machine.initialMemory, (timeOfPair token.time).Bounded)
    (initialPositive : 0 < (timeOfPair data.machine.initial.timestamp).value)
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ data.machine.rows) :
    ∃ memory : List (MemoryToken babyBearModulus),
      MixedMemoryAccepted (supportedPrefix data next.start memory) program ∧
      Transfer.Facts ⟨memory, data.machine.terminalMemory,
        Transfer.afterSteps (mixedData data) (Delegation.Caller.startClock next - 1)⟩ := by
  classical
  have requests := request_binding_checks (by decide) (by decide) (by decide) accepted.toRequestChecks inputs
  have facts := native_memory_facts (by decide) (by decide) accepted inputs seed requests
  obtain ⟨memory, earlier, later⟩ := Transfer.split_at facts (Delegation.Caller.startClock next - 1)
  have states := UnifiedReduced.Caller.Proofs.state_prefix_matching
    (fun state : PCState.State babyBearModulus => (timeOfPair state.timestamp).value)
    Trace.Row.start Trace.Row.finish accepted.states (by
      intro row included
      have clock := (machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs included).2
      change Delegation.Caller.startClock row < Delegation.Caller.finishClock row
      omega) member
  have callers := supported_prefix_callers data next.start memory
  have callerOriginal {row : Trace.Row babyBearModulus PooledFamily}
      (included : row ∈ (supportedPrefix data next.start memory).callers) : row ∈ data.callers := by
    rw [callers] at included
    exact List.mem_of_mem_filter included
  refine ⟨memory, ?_, later⟩
  refine {
    constraints := fun row included => accepted.constraints row (List.mem_of_mem_filter included)
    active := fun row included => accepted.active row (List.mem_of_mem_filter included)
    states := states
    decoded := fun row included => accepted.decoded row (callerOriginal included)
    workerConstraints := fun worker included => accepted.workerConstraints worker (List.mem_of_mem_filter included)
    workerActive := fun worker included => accepted.workerActive worker (List.mem_of_mem_filter included)
    requests := supported_prefix_requests accepted.toRequestChecks inputs member memory
    ordinaryDecoded := ?_
    memory := ?_ }
  · intro row included ordinary
    apply accepted.ordinaryDecoded row (List.mem_of_mem_filter included)
    intro called
    apply ordinary
    rw [callers]
    exact List.mem_filter.mpr ⟨called, (List.mem_filter.mp included).2⟩
  · change (data.machine.initialMemory ++ _).Perm (memory ++ _)
    rw [supported_prefix_steps_native accepted inputs initialPositive member memory]
    exact earlier.matching
/-- Each next worker input is an exact token on the preceding prefix frontier.
There are no intervening writes to worker cells: the caller's architectural
ports access x0, and all workers occupy distinct instruction slots. This proof
uses neither controller validity nor word bounds. -/
theorem supported_prefix_worker_read_native
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (inputs : RequestInputs data initial ca)
    (seed : ∀ token ∈ data.machine.initialMemory, (timeOfPair token.time).Bounded)
    (initialPositive : 0 < (timeOfPair data.machine.initial.timestamp).value)
    {next : Trace.Row babyBearModulus PooledFamily} (called : next ∈ data.callers)
    {worker : Delegation.Row babyBearModulus} (included : worker ∈ data.workers.rows)
    (slot : Delegation.Caller.WorkerSlot next worker)
    {memory : List (MemoryToken babyBearModulus)}
    (suffix : Transfer.Facts ⟨memory, data.machine.terminalMemory,
      Transfer.afterSteps (mixedData data) (Delegation.Caller.startClock next - 1)⟩)
    {port : MemoryPort} (present : port ∈ worker.ports) :
    readToken worker.assignment port ∈ memory := by
  have requests := request_binding_checks (by decide) (by decide) (by decide) accepted.toRequestChecks inputs
  have facts := native_memory_facts (by decide) (by decide) accepted inputs seed requests
  have nextMember := List.mem_of_mem_filter called
  have positive := lt_of_lt_of_le initialPositive (machine_clock_floor (by decide) (by decide) accepted.toRequestChecks inputs nextMember)
  have cut := (machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs nextMember).1
  have writes := slot.writes port present
  have original := mixed_worker_member included present
  have order := facts.order _ original
  change (timeOfPair (readToken worker.assignment port).time).value <
    (timeOfPair (worker.writeToken port).time).value at order
  rw [writes] at order
  have after : (readToken worker.assignment port, worker.writeToken port) ∈
      Transfer.afterSteps (mixedData data) (Delegation.Caller.startClock next - 1) := by
    apply List.mem_filter.mpr
    refine ⟨original, ?_⟩
    change (!decide ((timeOfPair (worker.writeToken port).time).value ≤
      Delegation.Caller.startClock next - 1)) = true
    rw [writes]
    simp
    omega
  have source := suffix.matching.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, after, rfl⟩)))
  rcases List.mem_append.mp source with seed | written
  · exact seed
  · obtain ⟨previous, late, equal⟩ := List.mem_map.mp written
    have lateOriginal := (List.mem_filter.mp late).1
    have lateClock : Delegation.Caller.startClock next ≤ (timeOfPair previous.2.time).value := by
      by_contra tooEarly
      have early : (timeOfPair previous.2.time).value ≤ Delegation.Caller.startClock next - 1 := by omega
      have rejected := (List.mem_filter.mp late).2
      change (!decide ((timeOfPair previous.2.time).value ≤ Delegation.Caller.startClock next - 1)) = true at rejected
      rw [decide_eq_true early] at rejected
      cases rejected
    have beforeWorker : (timeOfPair previous.2.time).value < Delegation.Caller.startClock next + 3 := by
      rw [equal]
      exact order
    rcases List.mem_append.mp lateOriginal with machine | delegated
    · obtain ⟨row, member, edge⟩ := List.mem_flatMap.mp machine
      obtain ⟨machinePort, portMember, same⟩ := List.mem_map.mp edge
      subst previous
      dsimp only [Prod.fst, Prod.snd] at lateClock beforeWorker
      have event : transferEvent (readToken row.assignment machinePort,
          writeToken row.columns row.assignment machinePort) ∈ machineEvents row :=
        List.mem_map.mpr ⟨machinePort, portMember, rfl⟩
      obtain ⟨offset, bound, time⟩ := machine_event_time (by decide) (by decide)
        accepted.toRequestChecks inputs member event
      change (timeOfPair (writeToken row.columns row.assignment machinePort).time).value + 1 = _ at time
      have aligned := (machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs member).1
      have sameClock : Delegation.Caller.startClock row = Delegation.Caller.startClock next := by omega
      have same := List.inj_on_of_nodup_map
        (machine_clocks_unique (by decide) (by decide) accepted.toRequestChecks inputs) member nextMember sameClock
      subst row
      have nativePort : machinePort ∈ machinePorts next := by simpa using portMember
      rw [machine_ports_caller called] at nativePort
      have modes : machinePort = AddSub.importedConstraintsMemoryPorts[0] ∨
          machinePort = AddSub.importedConstraintsMemoryPorts[2] := by simpa [architecturalPorts] using nativePort
      have zero : (writeToken next.columns next.assignment machinePort).address = (Cell.register 0).addressCode := by
        rcases modes with rfl | rfl
        · exact (requests.callers next called).1.sourceAddress
        · exact (requests.callers next called).1.destinationAddress
      have sameAddress := congrArg MemoryToken.address equal
      exact False.elim (Delegation.Proofs.port_not_zero worker present (sameAddress.symm.trans zero))
    · obtain ⟨other, member, edge⟩ := List.mem_flatMap.mp delegated
      obtain ⟨otherPort, portMember, same⟩ := List.mem_map.mp edge
      subst previous
      dsimp only [Prod.fst, Prod.snd] at lateClock beforeWorker
      have nativePort : otherPort ∈ other.ports := by simpa using portMember
      have time := worker_event_clock (by decide) requests member
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨otherPort, portMember, rfl⟩, rfl⟩)
      change (timeOfPair (other.writeToken otherPort).time).value + 1 = workerClock other at time
      have live := Delegation.Proofs.active_invocation_live
        (accepted.workerConstraints other member) (accepted.workerActive other member)
      have aligned := live_worker_clock_aligned accepted.toRequestChecks inputs requests member live
      omega

end Airbender.AddSub.Modular.External.Caller.Proofs
