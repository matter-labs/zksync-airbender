import Airbender.Review.Trace.UnifiedReduced.PreparedRoundWindows
import Airbender.Proofs.UnifiedReduced.PreparedHashWindows
import Airbender.Proofs.Blake2Round.ControlPool

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem prepared_worker_after_cut [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower : Nat}
    (scope : ControlPreparation data program lower 12 (hashPreparation (.blakeRound flags)))
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) : lower < worker.writeTime := by
  by_contra earlier
  have present : worker ∈ data.workers.prefixRows lower :=
    List.mem_filter.mpr ⟨member, decide_eq_true (by omega)⟩
  rw [scope.prefixScope] at present
  cases present

theorem prepared_round_caller_suffix [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedRoundInputs data before ca oa cells program flags lower)
    (first : lower % 4 = 0) (positive : 2 ≤ lower) (requests : RequestBinding data before) :
    ∀ row ∈ data.machine.rows, lower ≤ Delegation.Caller.startClock row → row ∈ data.callers := by
  have live : ∀ worker ∈ data.workers.rows, Delegation.Requests.Live (Delegation.Requests.fulfillment worker) := by
    intro worker member zero
    have time := Delegation.Caller.Proofs.worker_write_time (by omega)
      (requests.clocks worker member).1 (requests.clocks worker member).2
    have time : worker.writeTime = 2 := by simpa [zero, timeOfPair, Timestamp.value] using time
    have later := prepared_worker_after_cut inputs.preparation member
    omega
  have allLive : data.fulfillments.filter (fun call => decide (Delegation.Requests.Live call)) = data.fulfillments := by
    apply List.filter_eq_self.mpr
    intro call member
    change call ∈ data.workers.rows.map Delegation.Requests.fulfillment at member
    obtain ⟨worker, workerMember, rfl⟩ := List.mem_map.mp member
    exact decide_eq_true (live worker workerMember)
  have callCount := requests.fulfilled.length_eq
  rw [allLive] at callCount
  simp only [RequestTrace.calls, RequestTrace.fulfillments, List.length_map] at callCount
  have callersAfter : ∀ row ∈ data.callers, lower ≤ Delegation.Caller.startClock row := by
    intro row member
    obtain ⟨worker, matched, _⟩ := requests.workers row member
    have later := prepared_worker_after_cut inputs.preparation matched.1
    have write := Delegation.Caller.Proofs.worker_write_time (by omega)
      (requests.clocks worker matched.1).1 (requests.clocks worker matched.1).2
    change worker.writeTime = (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 2 at write
    have invocation := matched.2.2.invocation
    change (timeOfPair (Delegation.Requests.fulfillment worker).time).value = Delegation.Caller.startClock row + 1 at invocation
    have aligned := (machine_clock_facts hp clockInverse accepted.toRequestChecks inputs.publicProgram
      (List.mem_of_mem_filter member)).1
    omega
  let suffix := data.machine.rows.filter fun row => decide (lower ≤ Delegation.Caller.startClock row)
  have selected : suffix.filter (fun row => decide (Selected row.assignment)) = data.callers := by
    simp only [suffix, RequestTrace.callers, List.filter_filter]
    apply List.filter_congr
    intro row member
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨And.left, fun chosen => ⟨chosen, callersAfter row (List.mem_filter.mpr ⟨member, decide_eq_true chosen⟩)⟩⟩
  have count := native_suffix_count hp clockInverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned first
    (by have floor := inputs.preparation.afterInitial; omega) inputs.preparation.beforeTerminal
  have length : suffix.length = data.workers.rows.length := by
    change suffix.length = _ at count
    rw [inputs.duration] at count
    omega
  have same : suffix.filter (fun row => decide (Selected row.assignment)) = suffix := by
    apply List.Sublist.eq_of_length List.filter_sublist
    rw [selected, callCount, length]
  intro row member later
  rw [← selected, same]
  exact List.mem_filter.mpr ⟨member, decide_eq_true later⟩

theorem prepared_round_suffix_tokens [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedRoundInputs data before ca oa cells program flags lower)
    (first : lower % 4 = 0) (positive : 2 ≤ lower) (requests : RequestBinding data before) (written : Bool) :
    (((Transfer.afterSteps (mixedData data) (lower - 1)).map fun edge => if written then edge.2 else edge.1).filter
      fun token => token.address != (Cell.register 0).addressCode) =
      data.workers.steps.map (fun edge => if written then edge.2 else edge.1) := by
  let machine := (data.machine.rows.flatMap fun row => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)).filter
      fun edge => !decide ((timeOfPair edge.2.time).value ≤ lower - 1)
  have machineZero : ∀ edge ∈ machine,
      edge.1.address = (Cell.register 0).addressCode ∧ edge.2.address = (Cell.register 0).addressCode := by
    intro edge member
    have late : lower - 1 < (timeOfPair edge.2.time).value := by
      simpa using (List.mem_filter.mp member).2
    obtain ⟨row, present, step⟩ := List.mem_flatMap.mp (List.mem_of_mem_filter member)
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
    have native := machine_port_native row (by simpa using included)
    have clocks := state_clock_inputs hp clockInverse accepted.constraints accepted.states
      inputs.publicProgram.initialClock inputs.publicProgram.initialAligned row present
    have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime) (offset := port.clock.offset)
      clocks.1 clocks.2 (by have small := machine_port_offset row (by simpa using included); omega)).2
    change (timeOfPair (writeToken row.columns row.assignment port).time).value =
      Delegation.Caller.startClock row + port.clock.offset at time
    change lower - 1 < (timeOfPair (writeToken row.columns row.assignment port).time).value at late
    have small := machine_port_offset row (by simpa using included)
    have aligned := (machine_clock_facts hp clockInverse accepted.toRequestChecks inputs.publicProgram present).1
    have caller := prepared_round_caller_suffix hp clockInverse accepted inputs first positive requests row present (by omega)
    rw [machine_ports_caller caller] at included
    have modes : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using included
    rcases modes with rfl | rfl
    · exact ⟨(requests.callers row caller).registers.1, (requests.callers row caller).registers.1⟩
    · exact ⟨(requests.callers row caller).registers.2.1, (requests.callers row caller).registers.2.1⟩
  have workers : data.workers.steps.filter (fun edge => !decide ((timeOfPair edge.2.time).value ≤ lower - 1)) =
      data.workers.steps := by
    apply List.filter_eq_self.mpr
    intro edge member
    obtain ⟨row, present, step⟩ := List.mem_flatMap.mp member
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
    have time := Delegation.Proofs.row_write_time row (by simpa using included)
    have later := prepared_worker_after_cut inputs.preparation present
    simp only [time, Delegation.Proofs.rowWriteTime, Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  have steps : Transfer.afterSteps (mixedData data) (lower - 1) = machine ++ data.workers.steps := by
    simp only [Transfer.afterSteps, mixedData, RequestTrace.mixedSteps, List.filter_append, machine, workers]
  rw [steps]
  exact Delegation.Caller.Proofs.filtered_architectural_tokens machine data.workers.steps machineZero
    Delegation.Caller.Proofs.worker_addresses written

theorem prepared_round_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedRoundInputs data before ca oa cells program flags lower) (first : lower % 4 = 0) :
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have floor := inputs.preparation.afterInitial
  have positive : 2 ≤ lower := by omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  obtain ⟨start, earlier, later⟩ := Transfer.split_at facts (lower - 1)
  have prefixEqual : Transfer.beforeSteps (mixedData data) (lower - 1) = data.prefixSteps lower := by
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have prefixMatching := earlier.matching
  rw [prefixEqual] at prefixMatching
  obtain ⟨token, member, address, _, word⟩ := preparation_token hp clockInverse accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization inputs.preparation (by decide) first prefixMatching
  have word : token.word = Blake2Round.controlAt flags 0 := by
    rw [word, hash_preparation_value]
    have bound := flags.isLt
    simp [Delegation.Caller.HashSpan.controlStart, Word.ofBitVec, Blake2Round.controlAt, limbBase, BitVec.toNat_ofNat]
    omega
  let keep := fun token : MemoryToken p => token.address != (Cell.register 0).addressCode
  let projected : Delegation.MemoryData p :=
    ⟨data.workers.setup, data.workers.rows, start.filter keep, data.machine.terminalMemory.filter keep⟩
  have matching := later.matching.filter keep
  have writes := prepared_round_suffix_tokens size clockInverse accepted inputs first positive requests true
  have reads := prepared_round_suffix_tokens size clockInverse accepted inputs first positive requests false
  change ((Transfer.afterSteps (mixedData data) (lower - 1)).map Prod.snd).filter keep = _ at writes
  change ((Transfer.afterSteps (mixedData data) (lower - 1)).map Prod.fst).filter keep = _ at reads
  simp only [List.filter_append, writes, reads] at matching
  have selected : Delegation.MemoryAccepted projected := ⟨accepted.workerConstraints, matching⟩
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp (by
    change (data.machine.initialMemory.map MemoryToken.address).Nodup
    rw [image_addresses inputs.initialization]
    exact inputs.distinct)
  have pool : Blake2Round.Proofs.ControlMatchingInputs projected flags := by
    refine ⟨⟨matching, Delegation.Proofs.preserved_addresses, ?_⟩,
      unique.sublist (List.filter_sublist.map MemoryToken.address), inputs.tables, inputs.family,
      ⟨token, List.mem_filter.mpr ⟨member, ?_⟩, address, word⟩, inputs.roundsBound⟩
    · intro edge present
      exact facts.order edge (List.mem_append.mpr (Or.inr present))
    · simp [keep, address, Cell.addressCode]
  have masks := Blake2Round.Proofs.matching_masks size selected pool
  intro row present
  exact masks row present

theorem prepared_round_memory_inputs [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedRoundInputs data before ca oa cells program flags lower) (first : lower % 4 = 0) :
    MixedMemoryInputs data program before ca oa cells :=
  ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables,
    fun row member _ => prepared_round_masks hp clockInverse accepted inputs first row member⟩

theorem prepared_round_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower upper : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedRoundWindowInputs data before ca oa cells program flags lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    JointHashWindowResult data before cells (.blakeRound flags) lower upper := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have memory := prepared_round_memory_inputs (by omega) clockInverse accepted inputs.toPreparedRoundInputs first
  have floor := inputs.preparation.afterInitial
  have duration := inputs.spanDuration
  have projection := mixed_projected_window (by omega) clockInverse rotationInverse accepted memory first last
    (by omega) (by omega) (by omega) inputs.beforeTerminal (by simpa only [inputs.calls] using duration)
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, prefixMatching, _, startBoundary, finishBoundary,
    selected, initialized, finalBoundary, target⟩ := projection.execution
  have control := preparation_at_boundary (by omega) clockInverse accepted memory inputs.preparation
    (by decide) first prefixMatching startBoundary
  have entry : (Cell.register 12).read atStart = .ok (Delegation.Caller.HashSpan.blakeRound flags).controlStart atStart := by
    simpa only [hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.Protocol (data.windowProjection lower upper start finish) atStart (.blakeRound flags) :=
    ⟨inputs.tables, fun row member => inputs.family row (List.mem_of_mem_filter member), entry, inputs.calls⟩
  have result := Delegation.Caller.Proofs.hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target finalBoundary.1.addresses
  exact ⟨projection.requests,
    (Delegation.Caller.Proofs.window_call_count projection.requests).trans inputs.calls,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, startBoundary, finishBoundary, selected, initialized, result⟩

end Airbender.UnifiedReduced.Caller.Proofs
