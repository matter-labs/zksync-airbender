import Airbender.Proofs.UnifiedReduced.WorkerExecution
import Airbender.Proofs.ExternalBoundary.NativeRequests
import Airbender.Review.Helpers.UnifiedReduced.NativeMemory
import Airbender.Review.Helpers.UnifiedReduced.RetirementProfile
import Airbender.Review.Trace.UnifiedReduced.DelegationUse
import Airbender.Proofs.Trace.TransferSplit

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Cut an exactly matched, strictly increasing state graph immediately before
one of its actual edges. The frontier is that edge's exact input state; no PC,
reference execution or desired boundary is supplied independently. -/
theorem state_prefix_matching {S R : Type} [DecidableEq S]
    (rank : S → Nat) (start finish : R → S)
    {initial terminal : S} {rows : List R}
    (matched : (initial :: rows.map finish).Perm (terminal :: rows.map start))
    (advance : ∀ row ∈ rows, rank (start row) < rank (finish row))
    {next : R} (member : next ∈ rows) :
    (initial :: (rows.filter fun row => decide (rank (start row) < rank (start next))).map finish).Perm
      (start next :: (rows.filter fun row => decide (rank (start row) < rank (start next))).map start) := by
  classical
  let past := rows.filter fun row => decide (rank (start row) < rank (start next))
  let future := rows.filter fun row => !decide (rank (start row) < rank (start next))
  have partition : (past ++ future).Perm rows := List.filter_append_perm _ _
  have covered : List.Subperm (past.map start) (initial :: past.map finish) := by
    apply List.subperm_iff_count.mpr
    intro token
    by_cases missing : token ∉ past.map start
    · rw [List.count_eq_zero_of_not_mem missing]; exact Nat.zero_le _
    · obtain ⟨row, present, same⟩ := List.mem_map.mp (Classical.not_not.mp missing)
      have early : rank token < rank (start next) := by
        rw [← same]
        exact of_decide_eq_true (List.mem_filter.mp present).2
      have absent : token ∉ future.map finish := by
        intro included
        obtain ⟨later, included, equal⟩ := List.mem_map.mp included
        have original := (List.mem_filter.mp included).1
        have late : ¬ rank (start later) < rank (start next) := by
          intro early
          have rejected := (List.mem_filter.mp included).2
          rw [decide_eq_true early] at rejected
          cases rejected
        have increasing := advance later original
        rw [equal] at increasing
        omega
      have matching := matched.count_eq token
      have writes := (partition.map finish).count_eq token
      have reads := (partition.map start).count_eq token
      simp only [List.map_append, List.count_append, List.count_cons] at writes reads matching ⊢
      rw [List.count_eq_zero_of_not_mem absent] at writes
      omega
  obtain ⟨arranged, permuted, included⟩ := List.subperm_iff.mp covered
  obtain ⟨middle, boundary⟩ := included.exists_perm_append
  have frontierMatching : (initial :: past.map finish).Perm (middle ++ past.map start) :=
    (permuted.symm.trans boundary).trans List.perm_append_comm
  have produced : start next ∈ initial :: past.map finish := by
    have original : start next ∈ initial :: rows.map finish :=
      matched.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨next, member, rfl⟩))
    rcases List.mem_cons.mp original with same | written
    · exact List.mem_cons.mpr (Or.inl same)
    · obtain ⟨row, present, same⟩ := List.mem_map.mp written
      have earlier := advance row present
      rw [same] at earlier
      exact List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨row, List.mem_filter.mpr ⟨present, decide_eq_true earlier⟩, same⟩)
  have unread : start next ∉ past.map start := by
    intro included
    obtain ⟨row, present, equal⟩ := List.mem_map.mp included
    have earlier := of_decide_eq_true (List.mem_filter.mp present).2
    rw [equal] at earlier
    omega
  have frontier : start next ∈ middle := by
    exact (List.mem_append.mp (frontierMatching.mem_iff.mp produced)).resolve_right unread
  have length := frontierMatching.length_eq
  simp only [List.length_cons, List.length_map, List.length_append] at length
  have one : middle.length = 1 := by omega
  have same : middle = [start next] := by
    cases middle with
    | nil => simp at one
    | cons first rest =>
      have empty : rest = [] := List.length_eq_zero_iff.mp (by simp_all)
      subst rest
      have same : start next = first := by simpa only [List.mem_singleton] using frontier
      rw [same]
  simpa only [same, List.singleton_append] using frontierMatching

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

theorem supported_prefix_callers {p : Nat} [Fact p.Prime] (data : RequestTrace p)
    (point : PCState.State p) (memory : List (MemoryToken p)) :
    (supportedPrefix data point memory).callers = data.callers.filter fun row =>
      decide (Delegation.Caller.startClock row < (timeOfPair point.timestamp).value) := by
  simp only [supportedPrefix, RequestTrace.callers, List.filter_filter]
  apply List.filter_congr
  intro row _
  exact Bool.and_comm _ _

/-- Cutting before a real instruction partitions the actual architectural
transfers. This statement has no round-mask or valid-command hypothesis. -/
theorem supported_prefix_steps
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : RequestInputs data initial ca)
    (image : initialImage initial cells = some data.machine.initialMemory)
    {next : Trace.Row babyBearModulus UnifiedFamily} (member : next ∈ data.machine.rows)
    (memory : List (MemoryToken babyBearModulus)) :
    (supportedPrefix data next.start memory).mixedSteps =
      Transfer.beforeSteps (mixedData data) (Delegation.Caller.startClock next - 1) := by
  have requests := request_binding (by decide) (by decide) accepted.toRequestChecks inputs
  have positive := machine_native_clock_positive (by decide) (by decide) accepted inputs image member
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

/-- Exact request matching is preserved by the same cut. Native participation
rules out zero-clock surplus workers before the filtering argument. -/
theorem supported_prefix_requests
    {data : RequestTrace babyBearModulus} {initial : State} {ca : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial ca)
    {next : Trace.Row babyBearModulus UnifiedFamily} (member : next ∈ data.machine.rows)
    (memory : List (MemoryToken babyBearModulus)) :
    Delegation.Requests.Matching (supportedPrefix data next.start memory).calls
      (supportedPrefix data next.start memory).fulfillments := by
  have requests := request_binding (by decide) (by decide) accepted inputs
  have ledger := ExternalBoundary.Requests.Proofs.native_binding accepted requests
  let choose := fun call : Delegation.Requests.Request babyBearModulus =>
    decide ((timeOfPair call.time).value + 3 ≤ Delegation.Caller.startClock next)
  have cut := (machine_clock_facts (by decide) (by decide) accepted inputs member).1
  have calls : (supportedPrefix data next.start memory).calls = data.calls.filter choose := by
    rw [RequestTrace.calls, supported_prefix_callers]
    change _ = (data.callers.map (fun row => request row.assignment)).filter choose
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro row included
    obtain ⟨worker, ⟨_, matched, slot⟩, _⟩ := requests.workers row included
    have invocation : (timeOfPair (request row.assignment).time).value = Delegation.Caller.startClock row + 1 := by
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

/-- A genuine accepted native prefix, with its memory frontier obtained from
exact matching. No hash control, bigint command or reference execution is used
to construct the prefix. -/
theorem supported_prefix_accepted
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : RequestInputs data initial ca)
    (image : initialImage initial cells = some data.machine.initialMemory)
    {next : Trace.Row babyBearModulus UnifiedFamily} (member : next ∈ data.machine.rows) :
    ∃ memory : List (MemoryToken babyBearModulus),
      MixedMemoryAccepted (supportedPrefix data next.start memory) program ∧
      Transfer.Facts ⟨memory, data.machine.terminalMemory,
        Transfer.afterSteps (mixedData data) (Delegation.Caller.startClock next - 1)⟩ := by
  classical
  have requests := request_binding (by decide) (by decide) accepted.toRequestChecks inputs
  have facts := mixed_memory_facts (by decide) (by decide) accepted inputs image requests
  obtain ⟨memory, earlier, later⟩ := Transfer.split_at facts (Delegation.Caller.startClock next - 1)
  have states := state_prefix_matching
    (fun state : PCState.State babyBearModulus => (timeOfPair state.timestamp).value)
    Trace.Row.start Trace.Row.finish accepted.states (by
      intro row included
      have clock := (machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs included).2
      change Delegation.Caller.startClock row < Delegation.Caller.finishClock row
      omega) member
  have callers := supported_prefix_callers data next.start memory
  have callerOriginal {row : Trace.Row babyBearModulus UnifiedFamily}
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
    rw [supported_prefix_steps accepted inputs image member memory]
    exact earlier.matching

def supported_prefix_inputs
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (inputs : NativeMemoryInputs data program initial ca oa cells)
    (point : PCState.State babyBearModulus) (memory : List (MemoryToken babyBearModulus)) :
    NativeMemoryInputs (supportedPrefix data point memory) program initial ca oa cells :=
  ⟨⟨inputs.publicProgram.image, inputs.publicProgram.initialClock, inputs.publicProgram.initialAligned⟩,
    inputs.ordinaryProgram, inputs.initialization, inputs.distinct, inputs.aligned, inputs.setup, inputs.tables⟩

def supported_prefix_profile [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell}
    (profile : RetirementProfile data program initial cells)
    (point : PCState.State babyBearModulus) (memory : List (MemoryToken babyBearModulus)) :
    RetirementProfile (supportedPrefix data point memory) program initial cells :=
  ⟨⟨profile.code.ram, profile.code.ordinary, profile.code.callers⟩, profile.registers,
    profile.configuration, profile.ordinary, profile.landingPadDisabled, profile.loads⟩

/-- Each next worker input is an exact token on the preceding prefix frontier.
There are no intervening writes to worker cells: the caller's architectural
ports access x0, and all workers occupy distinct instruction slots. This proof
uses neither controller validity nor word bounds. -/
theorem supported_prefix_worker_read
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : RequestInputs data initial ca)
    (image : initialImage initial cells = some data.machine.initialMemory)
    {next : Trace.Row babyBearModulus UnifiedFamily} (called : next ∈ data.callers)
    {worker : Delegation.Row babyBearModulus} (included : worker ∈ data.workers.rows)
    (slot : Delegation.Caller.WorkerSlot next worker)
    {memory : List (MemoryToken babyBearModulus)}
    (suffix : Transfer.Facts ⟨memory, data.machine.terminalMemory,
      Transfer.afterSteps (mixedData data) (Delegation.Caller.startClock next - 1)⟩)
    {port : MemoryPort} (present : port ∈ worker.ports) :
    readToken worker.assignment port ∈ memory := by
  have requests := request_binding (by decide) (by decide) accepted.toRequestChecks inputs
  have facts := mixed_memory_facts (by decide) (by decide) accepted inputs image requests
  have nextMember := List.mem_of_mem_filter called
  have positive := machine_native_clock_positive (by decide) (by decide) accepted inputs image nextMember
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
      have modes : machinePort = importedConstraintsMemoryPorts[0] ∨
          machinePort = importedConstraintsMemoryPorts[2] := by simpa [architecturalPorts] using nativePort
      have zero : (writeToken next.columns next.assignment machinePort).address = (Cell.register 0).addressCode := by
        rcases modes with rfl | rfl
        · exact (requests.callers next called).registers.1
        · exact (requests.callers next called).registers.2.1
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
      have aligned := (live_worker_clock (by decide) (by decide) accepted.toRequestChecks inputs requests member live).2
      omega

end Airbender.UnifiedReduced.Caller.Proofs
