import Airbender.Review.Trace.UnifiedReduced.WindowProjection
import Airbender.Proofs.UnifiedReduced.MixedWindows
import Airbender.Proofs.UnifiedReduced.WorkerProjection
import Airbender.Proofs.Trace.HistoryRestriction
import Airbender.Proofs.Delegation.BoundaryRestriction

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem worker_write_off_cut [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {data : RequestTrace p} {before : State}
    {addresses : List (BitVec 32)} (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before) {cut : Nat} (aligned : cut % 4 = 0)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) : worker.writeTime ≠ cut := by
  have write := Delegation.Caller.Proofs.worker_write_time (by omega)
    (requests.clocks worker member).1 (requests.clocks worker member).2
  by_cases live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)
  · have clock := live_worker_clock hp inverse accepted inputs requests member live
    have time : worker.writeTime + 1 = workerClock worker := by
      rw [write]
      change ((decodeTimestamp worker.assignment worker.columns.invocation).value + 2) + 1 =
        (decodeTimestamp worker.assignment worker.columns.invocation).value + 3
      omega
    rw [← time] at clock
    omega
  · have zero : (Delegation.Requests.fulfillment worker).time = (0, 0) := not_not.mp live
    have time : worker.writeTime = 2 := by simp [write, zero, timeOfPair, Timestamp.value]
    omega

theorem worker_prefix_shift [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {data : RequestTrace p} {before : State}
    {addresses : List (BitVec 32)} (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before) {cut : Nat} (aligned : cut % 4 = 0) (positive : 2 ≤ cut) :
    data.workers.prefixRows (cut - 1) = data.workers.prefixRows cut := by
  apply List.filter_congr
  intro worker member
  have different := worker_write_off_cut hp inverse accepted inputs requests aligned member
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem window_machine_addresses [Fact p.Prime] {data : RequestTrace p} {before : State}
    (accepted : MixedMemoryAccepted data []) (requests : RequestBinding data before) {lower upper : Nat} :
    ∀ edge ∈ (data.windowMachineRows lower upper).flatMap (fun row => (machinePorts row).toList.map fun port =>
      (readToken row.assignment port, writeToken row.columns row.assignment port)),
      edge.1.address = (Cell.register 0).addressCode ∧ edge.2.address = (Cell.register 0).addressCode := by
  intro edge member
  obtain ⟨row, present, step⟩ := List.mem_flatMap.mp member
  exact caller_only_addresses accepted requests edge (List.mem_flatMap.mpr
    ⟨row, List.mem_of_mem_filter present, step⟩)

theorem window_filtered_tokens [Fact p.Prime] {data : RequestTrace p} {before : State}
    (accepted : MixedMemoryAccepted data []) (requests : RequestBinding data before) (lower upper : Nat) (written : Bool) :
    (((data.windowSteps lower upper).map fun edge => if written then edge.2 else edge.1).filter
      fun token => token.address != (Cell.register 0).addressCode) =
      ((data.workers.windowRows lower upper).flatMap Delegation.Row.memorySteps).map
        (fun edge => if written then edge.2 else edge.1) :=
  Delegation.Caller.Proofs.filtered_architectural_tokens _ _ (window_machine_addresses accepted requests)
    (Delegation.Caller.Proofs.worker_addresses (data := ⟨data.workers.setup, data.workers.windowRows lower upper, [], []⟩)) written

theorem prefix_filtered_tokens [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {data : RequestTrace p} {before : State}
    {addresses : List (BitVec 32)} (accepted : MixedMemoryAccepted data []) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before) {lower : Nat} (first : lower % 4 = 0) (positive : 2 ≤ lower) (written : Bool) :
    (((data.prefixSteps lower).map fun edge => if written then edge.2 else edge.1).filter
      fun token => token.address != (Cell.register 0).addressCode) =
      ((data.workers.prefixRows lower).flatMap Delegation.Row.memorySteps).map
        (fun edge => if written then edge.2 else edge.1) := by
  let priorMachine := (data.machine.rows.flatMap fun row => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)).filter
      fun edge => decide ((timeOfPair edge.2.time).value < lower)
  let priorWorkers := data.workers.steps.filter fun edge => decide ((timeOfPair edge.2.time).value < lower)
  have projection := Delegation.Caller.Proofs.filtered_architectural_tokens priorMachine priorWorkers
    (fun edge member => caller_only_addresses accepted requests edge (List.mem_of_mem_filter member))
    (fun edge member => Delegation.Caller.Proofs.worker_addresses edge (List.mem_of_mem_filter member)) written
  have clock : priorWorkers = (data.workers.prefixRows lower).flatMap Delegation.Row.memorySteps := by
    rw [← worker_prefix_shift hp inverse accepted.toRequestChecks inputs requests first positive,
      Delegation.Proofs.native_prefix_steps]
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [clock] at projection
  have parts : data.prefixSteps lower = priorMachine ++ priorWorkers := by
    simp only [RequestTrace.prefixSteps, RequestTrace.mixedSteps, List.filter_append, priorMachine, priorWorkers]
  rw [parts, clock]
  exact projection

theorem native_boundary_restriction {tokens : List (MemoryToken p)} {state : State} {cells : List Cell}
    (boundary : NativeBoundary tokens state cells) :
    NativeBoundary (tokens.filter fun token => token.address != (Cell.register 0).addressCode)
      state (Delegation.Caller.workerCells cells) :=
  ⟨Delegation.Proofs.boundary_image_restriction boundary.1 (fun address => address != (Cell.register 0).addressCode),
    fun token member => boundary.2 token (List.mem_of_mem_filter member)⟩

theorem projected_window [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data []) (inputs : MixedMemoryInputs data [] before ca oa cells)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) :
    ProjectedWindowExecution data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have window := mixed_window_execution hp clockInverse rotationInverse accepted inputs first last positive ordered
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, prefixMatching, matching, startBoundary, finishBoundary⟩ := window.execution
  have selectedMatching := matching.filter fun token => token.address != (Cell.register 0).addressCode
  have writes := window_filtered_tokens accepted requests lower upper true
  have reads := window_filtered_tokens accepted requests lower upper false
  change ((data.windowSteps lower upper).map Prod.snd).filter _ = _ at writes
  change ((data.windowSteps lower upper).map Prod.fst).filter _ = _ at reads
  simp only [List.filter_append, writes, reads] at selectedMatching
  have priorMatching := prefixMatching.filter fun token => token.address != (Cell.register 0).addressCode
  have priorWrites := prefix_filtered_tokens size clockInverse accepted inputs.publicProgram requests first positive true
  have priorReads := prefix_filtered_tokens size clockInverse accepted inputs.publicProgram requests first positive false
  change ((data.prefixSteps lower).map Prod.snd).filter _ = _ at priorWrites
  change ((data.prefixSteps lower).map Prod.fst).filter _ = _ at priorReads
  simp only [List.filter_append, priorWrites, priorReads] at priorMatching
  have startProjected := native_boundary_restriction startBoundary
  have finishProjected := native_boundary_restriction finishBoundary
  have histories (events : List MemoryAccess) (edges : List (MemoryToken p × MemoryToken p))
      (permutation : events.Perm (edges.map transferEvent)) (stateBefore stateAfter : State)
      (history : SailHistory cells events stateBefore stateAfter)
      :
      ∃ actual, actual.Perm ((edges.filter fun edge => edge.1.address != (Cell.register 0).addressCode).map transferEvent) ∧
        SailHistory (Delegation.Caller.workerCells cells) actual stateBefore stateAfter := by
    refine ⟨_, ?_, history_worker_cells history⟩
    have actual := permutation.filter (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode))
    rw [List.filter_map] at actual
    change (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).Perm
      ((edges.filter fun edge => decide (edge.1.address ≠ (Cell.register 0).addressCode)).map transferEvent) at actual
    have predicate : (fun edge : MemoryToken p × MemoryToken p => decide (edge.1.address ≠ (Cell.register 0).addressCode)) =
        (fun edge => edge.1.address != (Cell.register 0).addressCode) := by
      funext edge
      apply Bool.eq_iff_iff.mpr
      simp
    rw [predicate] at actual
    exact actual
  have prefixSteps : (data.prefixSteps lower).filter (fun edge => edge.1.address != (Cell.register 0).addressCode) =
      (data.workers.prefixRows lower).flatMap Delegation.Row.memorySteps := by
    simp only [RequestTrace.prefixSteps, RequestTrace.mixedSteps, List.filter_append]
    have machineRemoved : ((data.machine.rows.flatMap fun row => (machinePorts row).toList.map fun port =>
        (readToken row.assignment port, writeToken row.columns row.assignment port)).filter
        (fun edge => decide ((timeOfPair edge.2.time).value < lower))).filter
        (fun edge => edge.1.address != (Cell.register 0).addressCode) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro edge member
      simp [(caller_only_addresses accepted requests edge (List.mem_of_mem_filter member)).1]
    rw [machineRemoved, List.nil_append]
    have workerKept : (data.workers.steps.filter fun edge => decide ((timeOfPair edge.2.time).value < lower)).filter
        (fun edge => edge.1.address != (Cell.register 0).addressCode) =
        data.workers.steps.filter fun edge => decide ((timeOfPair edge.2.time).value < lower) := by
      apply List.filter_eq_self.mpr
      intro edge member
      exact bne_iff_ne.mpr (Delegation.Caller.Proofs.worker_addresses edge (List.mem_of_mem_filter member)).1
    rw [workerKept, ← worker_prefix_shift size clockInverse accepted.toRequestChecks inputs.publicProgram requests first positive,
      Delegation.Proofs.native_prefix_steps]
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have spanSteps : (data.windowSteps lower upper).filter (fun edge => edge.1.address != (Cell.register 0).addressCode) =
      (data.workers.windowRows lower upper).flatMap Delegation.Row.memorySteps := by
    simp only [RequestTrace.windowSteps, List.filter_append]
    have machineRemoved : ((data.windowMachineRows lower upper).flatMap fun row => (machinePorts row).toList.map fun port =>
        (readToken row.assignment port, writeToken row.columns row.assignment port)).filter
        (fun edge => edge.1.address != (Cell.register 0).addressCode) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro edge member
      simp [(window_machine_addresses accepted requests edge member).1]
    rw [machineRemoved, List.nil_append]
    apply List.filter_eq_self.mpr
    intro edge member
    exact bne_iff_ne.mpr (Delegation.Caller.Proofs.worker_addresses
      (data := ⟨data.workers.setup, data.workers.windowRows lower upper, [], []⟩) edge member).1
  obtain ⟨prefixEvents, prefixPerm, prefixHistory⟩ := histories earlierEvents _ firstPerm before atStart firstHistory
  obtain ⟨workerEvents, workerPerm, workerHistory⟩ := histories spanEvents _ spanPerm atStart atFinish spanHistory
  rw [prefixSteps] at prefixPerm
  rw [spanSteps] at workerPerm
  refine ⟨window.requests, start, finish, earlierEvents, spanEvents, atStart, atFinish,
    firstPerm, spanPerm, firstHistory, spanHistory, startBoundary, finishBoundary,
    ⟨?_, priorMatching⟩, ⟨⟨prefixEvents, prefixPerm, prefixHistory⟩, ?_⟩,
    ⟨?_, selectedMatching⟩, ⟨startProjected.1, inputs.distinct.sublist (List.filter_sublist.map Cell.addressCode),
      fun token member => (startProjected.2 token member).2,
      fun row member => (requests.clocks row (List.mem_of_mem_filter member)).2⟩,
    finishProjected, ⟨⟨workerEvents, workerPerm, workerHistory⟩, ?_⟩⟩
  · intro row member
    exact accepted.workerConstraints row (List.mem_of_mem_filter member)
  · intro token member
    exact native_boundary_read startProjected member
  · intro row member
    exact accepted.workerConstraints row (List.mem_of_mem_filter member)
  · intro token member
    exact native_boundary_read finishProjected member

end Airbender.UnifiedReduced.Caller.Proofs
