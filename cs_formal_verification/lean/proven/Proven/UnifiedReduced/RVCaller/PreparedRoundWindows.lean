module
public import Human.Trace.UnifiedReduced.RVPreparedRoundWindows
public import Proven.UnifiedReduced.RVCaller.PreparedHashWindows
public import Proven.Defs.Trace.Workers.Blake2Round.Call

@[expose] public section

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_prepared_worker_after_cut [Fact p.Prime]
    {data : RVRequestTrace p} {lower : Nat}
    (prefixEmpty : data.workers.prefixRows lower = [])
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) : lower < worker.writeTime := by
  by_contra earlier
  have present : worker ∈ data.workers.prefixRows lower :=
    List.mem_filter.mpr ⟨member, decide_eq_true (by omega)⟩
  rw [prefixEmpty] at present
  cases present

theorem rv_prepared_round_caller_suffix [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedRoundInputs data before ca oa cells program flags lower)
    (first : lower % 4 = 0) (positive : 2 ≤ lower) (requests : RVRequestBinding data before) :
    ∀ row ∈ data.machine.rows, lower ≤ Delegation.Caller.startClock row → row ∈ data.callers := by
  have live : ∀ worker ∈ data.workers.rows, Delegation.Requests.Live (Delegation.Requests.fulfillment worker) := by
    intro worker member zero
    have time := Delegation.Caller.Proofs.worker_write_time (by omega)
      (requests.clocks worker member).1 (requests.clocks worker member).2
    have time : worker.writeTime = 2 := by simpa [zero, timeOfPair, Timestamp.value] using time
    have later := rv_prepared_worker_after_cut inputs.prefixEmpty member
    omega
  have allLive : data.fulfillments.filter (fun call => decide (Delegation.Requests.Live call)) = data.fulfillments := by
    apply List.filter_eq_self.mpr
    intro call member
    change call ∈ data.workers.rows.map Delegation.Requests.fulfillment at member
    obtain ⟨worker, workerMember, rfl⟩ := List.mem_map.mp member
    exact decide_eq_true (live worker workerMember)
  have callCount := requests.fulfilled.length_eq
  rw [allLive] at callCount
  simp only [RVRequestTrace.calls, RVRequestTrace.fulfillments, List.length_map] at callCount
  have callersAfter : ∀ row ∈ data.callers, lower ≤ Delegation.Caller.startClock row := by
    intro row member
    obtain ⟨worker, matched, _⟩ := requests.workers row member
    have later := rv_prepared_worker_after_cut inputs.prefixEmpty matched.1
    have write := Delegation.Caller.Proofs.worker_write_time (by omega)
      (requests.clocks worker matched.1).1 (requests.clocks worker matched.1).2
    change worker.writeTime = (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 2 at write
    have invocation := matched.2.2.invocation
    change (timeOfPair (Delegation.Requests.fulfillment worker).time).value = Delegation.Caller.startClock row + 1 at invocation
    have aligned := (rv_machine_clock_facts hp clockInverse accepted.toRVRequestChecks inputs.publicProgram
      (List.mem_of_mem_filter member)).1
    omega
  let suffix := data.machine.rows.filter fun row => decide (lower ≤ Delegation.Caller.startClock row)
  have selected : suffix.filter (fun row => decide (Selected row.assignment)) = data.callers := by
    simp only [suffix, RVRequestTrace.callers, List.filter_filter]
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

theorem rv_prepared_round_suffix_tokens [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedRoundInputs data before ca oa cells program flags lower)
    (first : lower % 4 = 0) (positive : 2 ≤ lower) (requests : RVRequestBinding data before) (written : Bool) :
    (((Transfer.afterSteps (rv_mixedData data) (lower - 1)).map fun edge => if written then edge.2 else edge.1).filter
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
    have native := rv_machine_port_native row (by simpa using included)
    have clocks := state_clock_inputs hp clockInverse accepted.constraints accepted.states
      inputs.publicProgram.initialClock inputs.publicProgram.initialAligned row present
    have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime) (offset := port.clock.offset)
      clocks.1 clocks.2 (by have small := rv_machine_port_offset row (by simpa using included); omega)).2
    change (timeOfPair (writeToken row.columns row.assignment port).time).value =
      Delegation.Caller.startClock row + port.clock.offset at time
    change lower - 1 < (timeOfPair (writeToken row.columns row.assignment port).time).value at late
    have small := rv_machine_port_offset row (by simpa using included)
    have aligned := (rv_machine_clock_facts hp clockInverse accepted.toRVRequestChecks inputs.publicProgram present).1
    have caller := rv_prepared_round_caller_suffix hp clockInverse accepted inputs first positive requests row present (by omega)
    rw [rv_machine_ports_caller caller] at included
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
    have later := rv_prepared_worker_after_cut inputs.prefixEmpty present
    simp only [time, Delegation.Proofs.rowWriteTime, Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  have steps : Transfer.afterSteps (rv_mixedData data) (lower - 1) = machine ++ data.workers.steps := by
    simp only [Transfer.afterSteps, rv_mixedData, RVRequestTrace.mixedSteps, List.filter_append, machine, workers]
  rw [steps]
  exact Delegation.Caller.Proofs.filtered_architectural_tokens machine data.workers.steps machineZero
    Delegation.Caller.Proofs.worker_addresses written

theorem rv_prepared_round_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedRoundInputs data before ca oa cells program flags lower) (first : lower % 4 = 0) :
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have floor := inputs.preparation.afterInitial
  have positive : 2 ≤ lower := by omega
  have requests := rv_request_binding size clockInverse accepted.toRVRequestChecks inputs.publicProgram
  have facts := rv_mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  obtain ⟨start, earlier, later⟩ := Transfer.split_at facts (lower - 1)
  have prefixEqual : Transfer.beforeSteps (rv_mixedData data) (lower - 1) = data.prefixSteps lower := by
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have prefixMatching := earlier.matching
  rw [prefixEqual] at prefixMatching
  obtain ⟨token, member, address, _, word⟩ := rv_preparation_token hp clockInverse accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization inputs.preparation (by decide) first prefixMatching
  have word : token.word = Blake2Round.controlAt flags 0 := by
    rw [word, rv_hash_preparation_value]
    have bound := flags.isLt
    simp [Delegation.Caller.HashSpan.controlStart, Word.ofBitVec, Blake2Round.controlAt, limbBase, BitVec.toNat_ofNat]
    omega
  let keep := fun token : MemoryToken p => token.address != (Cell.register 0).addressCode
  let projected : Delegation.MemoryData p :=
    ⟨data.workers.setup, data.workers.rows, start.filter keep, data.machine.terminalMemory.filter keep⟩
  have matching := later.matching.filter keep
  have writes := rv_prepared_round_suffix_tokens size clockInverse accepted inputs first positive requests true
  have reads := rv_prepared_round_suffix_tokens size clockInverse accepted inputs first positive requests false
  change ((Transfer.afterSteps (rv_mixedData data) (lower - 1)).map Prod.snd).filter keep = _ at writes
  change ((Transfer.afterSteps (rv_mixedData data) (lower - 1)).map Prod.fst).filter keep = _ at reads
  simp only [List.filter_append, writes, reads] at matching
  have selected : Delegation.MemoryAccepted projected := ⟨accepted.workerConstraints, matching⟩
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp (by
    change (data.machine.initialMemory.map MemoryToken.address).Nodup
    rw [rvImage_addresses inputs.initialization]
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

theorem rv_prepared_round_memory_inputs [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedRoundInputs data before ca oa cells program flags lower) (first : lower % 4 = 0) :
    RVMixedMemoryInputs data program before ca oa cells :=
  ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables,
    fun row member _ => rv_prepared_round_masks hp clockInverse accepted inputs first row member⟩

theorem rv_prepared_round_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower upper : Nat}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedRoundWindowInputs data before ca oa cells program flags lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    RVJointHashWindowResult data before cells (.blakeRound flags) lower upper := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have memory := rv_prepared_round_memory_inputs (by omega) clockInverse accepted inputs.toRVPreparedRoundInputs first
  have floor := inputs.preparation.afterInitial
  have duration := inputs.spanDuration
  have projection := rv_mixed_projected_window (by omega) clockInverse rotationInverse accepted memory first last
    (by omega) (by omega) (by omega) inputs.beforeTerminal (by simpa only [inputs.calls] using duration)
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, prefixMatching, _, startBoundary, finishBoundary,
    selected, initialized, finalBoundary, target⟩ := projection.execution
  have control := rv_preparation_at_boundary (by omega) clockInverse accepted memory inputs.preparation
    (by decide) first prefixMatching startBoundary
  have entry : (Cell.register 12).readRV atStart = some (Delegation.Caller.HashSpan.blakeRound flags).controlStart := by
    simpa only [rv_hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.RVProtocol (data.windowProjection lower upper start finish) atStart (.blakeRound flags) :=
    ⟨inputs.tables, fun row member => inputs.family row (List.mem_of_mem_filter member), entry, inputs.calls⟩
  have result := rv_hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target finalBoundary.1.addresses
  exact ⟨projection.requests,
    (Delegation.Caller.Proofs.window_call_count projection.requests).trans inputs.calls,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, startBoundary, finishBoundary, selected, initialized, result⟩

theorem rv_prepared_round_region_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {regions : List RoundRegion} {region : RoundRegion}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedProtocolInputs data before ca oa cells program regions)
    (scope : RVRoundRegionInputs data program region) :
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have floor := scope.preparation.afterInitial
  have duration := scope.duration
  have positive : 2 ≤ region.lower := by omega
  have requests := rv_request_binding size clockInverse accepted.toRVRequestChecks inputs.publicProgram
  have facts := rv_mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  obtain ⟨start, earlier, suffix⟩ := Transfer.split_at facts (region.lower - 1)
  obtain ⟨finish, window, _⟩ := Transfer.split_at suffix (region.upper - 1)
  change Transfer.Facts ⟨start, finish,
    Transfer.windowSteps (rv_mixedData data) (region.lower - 1) (region.upper - 1)⟩ at window
  rw [← rv_mixed_window_steps size clockInverse accepted.toRVRequestChecks inputs.publicProgram
    scope.aligned.1 scope.aligned.2 positive (by omega)] at window
  have prefixMatching := earlier.matching
  rw [rv_mixed_prefix_steps data (by omega)] at prefixMatching
  obtain ⟨token, member, address, _, word⟩ := rv_preparation_token hp clockInverse accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization scope.preparation (by decide)
    scope.aligned.1 prefixMatching
  have word : token.word = Blake2Round.controlAt region.flags 0 := by
    rw [word, rv_hash_preparation_value]
    have bound := region.flags.isLt
    simp [Delegation.Caller.HashSpan.controlStart, Word.ofBitVec, Blake2Round.controlAt, limbBase, BitVec.toNat_ofNat]
    omega
  have schedule := rv_caller_window_schedule size clockInverse accepted.toRVRequestChecks inputs.publicProgram
    scope.aligned.1 scope.aligned.2 positive (by omega) (by omega) scope.beforeTerminal duration
  let keep := fun token : MemoryToken p => token.address != (Cell.register 0).addressCode
  let projected := data.windowProjection region.lower region.upper start finish
  have matching := window.matching.filter keep
  have writes := rv_caller_window_filtered_tokens schedule requests true
  have reads := rv_caller_window_filtered_tokens schedule requests false
  change ((data.windowSteps region.lower region.upper).map Prod.snd).filter keep = _ at writes
  change ((data.windowSteps region.lower region.upper).map Prod.fst).filter keep = _ at reads
  simp only [List.filter_append, writes, reads] at matching
  have selected : Delegation.MemoryAccepted projected := by
    refine ⟨fun row member => accepted.workerConstraints row (List.mem_of_mem_filter member), matching⟩
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp (by
    change (data.machine.initialMemory.map MemoryToken.address).Nodup
    rw [rvImage_addresses inputs.initialization]
    exact inputs.distinct)
  have pool : Blake2Round.Proofs.ControlMatchingInputs projected region.flags := by
    refine ⟨⟨matching, Delegation.Proofs.preserved_addresses, ?_⟩,
      unique.sublist (List.filter_sublist.map MemoryToken.address), inputs.tables, scope.family,
      ⟨token, List.mem_filter.mpr ⟨member, ?_⟩, address, word⟩, scope.roundsBound⟩
    · intro edge present
      have member := List.mem_flatMap.mp present
      obtain ⟨row, included, step⟩ := member
      exact facts.order edge (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨row, List.mem_of_mem_filter included, step⟩)))
    · simp [address, Cell.addressCode]
  exact Blake2Round.Proofs.matching_masks size selected pool

theorem rv_prepared_protocol_memory_inputs [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {regions : List RoundRegion}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedProtocolInputs data before ca oa cells program regions) :
    RVMixedMemoryInputs data program before ca oa cells := by
  refine ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables, ?_⟩
  intro row member family
  obtain ⟨region, included, inside⟩ := inputs.coverage row member family
  exact rv_prepared_round_region_masks hp clockInverse accepted inputs (inputs.scopes region included) row inside

theorem rv_prepared_protocol_reference_at_states [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before atStart atFinish : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {regions : List RoundRegion} {window : HashWindow}
    {start finish : List (MemoryToken p)} {spanEvents : List MemoryAccess}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedProtocolInputs data before ca oa cells program regions)
    (scope : RVPreparedProtocolWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0)
    (prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps window.lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps window.lower).map Prod.fst))
    (matching : (start ++ (data.windowSteps window.lower window.upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps window.lower window.upper).map Prod.fst))
    (startBoundary : RVNativeBoundary start atStart cells) (finishBoundary : RVNativeBoundary finish atFinish cells)
    (spanPerm : spanEvents.Perm ((data.windowSteps window.lower window.upper).map transferEvent))
    (spanHistory : RVHistory cells spanEvents atStart atFinish) :
    Delegation.Caller.HashSpan.RVResult window.span (data.windowProjection window.lower window.upper start finish) atStart atFinish
      (Delegation.Caller.workerCells cells) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := rv_prepared_protocol_memory_inputs (by omega) clockInverse accepted inputs
  have floor := scope.preparation.afterInitial
  have duration := scope.duration
  have schedule := rv_caller_window_schedule size clockInverse accepted.toRVRequestChecks inputs.publicProgram
    first last (by omega) (by omega) (by omega) scope.beforeTerminal (by simpa only [scope.calls] using duration)
  have requests := rv_request_binding size clockInverse accepted.toRVRequestChecks inputs.publicProgram
  obtain ⟨selected, initialized, terminal, target⟩ :=
    rv_mixed_worker_window_at_states accepted memory schedule requests matching startBoundary finishBoundary spanPerm spanHistory (rv_mixed_zero_writes size clockInverse accepted memory)
  have control := rv_preparation_at_boundary (by omega) clockInverse accepted memory scope.preparation
    (rv_hash_control_register_nonzero window.span) first prefixMatching startBoundary
  have entry : (Cell.register window.span.controlRegister).readRV atStart = some window.span.controlStart := by
    simpa only [rv_hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.RVProtocol (data.windowProjection window.lower window.upper start finish)
      atStart window.span := ⟨inputs.tables, scope.family, entry, scope.calls⟩
  exact rv_hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target terminal.1.addresses

theorem rv_prepared_protocol_sequence_at_segments [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {regions : List RoundRegion} {windows : List HashWindow}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ windows, RVPreparedProtocolWindowInputs data program window)
    {cut : Nat} {tokens : List (MemoryToken p)} {state : RV.State} {segments : List (RVWindowSegment p)}
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval))
    (actual : RVWindowSegmentsRealize data cells cut tokens state (windows.map HashWindow.interval) segments) :
    List.Forall₂ (RVHashWindowResult data cells) windows segments := by
  induction windows generalizing cut tokens state segments with
  | nil =>
    cases segments with
    | nil => exact .nil
    | cons _ _ => exact False.elim actual
  | cons window rest ih =>
    cases segments with
    | nil => exact False.elim actual
    | cons segment segments =>
      obtain ⟨_, _, first, last, restOrder⟩ := ordered
      obtain ⟨_, _, _, prefixMatching, spanPerm, spanHistory, matching, startBoundary, finishBoundary, tail⟩ := actual
      have scope := scopes window (List.mem_cons_self ..)
      have result := rv_prepared_protocol_reference_at_states hp clockInverse accepted inputs scope first last
        prefixMatching matching startBoundary finishBoundary spanPerm spanHistory
      have floor := scope.preparation.afterInitial
      have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
      have requests := rv_request_windows size clockInverse accepted.toRVRequestChecks inputs.publicProgram first last (by omega)
      exact .cons ⟨requests, (Delegation.Caller.Proofs.window_call_count requests).trans scope.calls, result⟩
        (ih (fun next member => scopes next (List.mem_cons_of_mem _ member)) restOrder tail)

theorem rv_prepared_protocol_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {regions : List RoundRegion} {first : HashWindow} {rest : List HashWindow}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, RVPreparedProtocolWindowInputs data program window)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    RVPreparedHashSequenceResult data before cells first rest := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have aligned : first.lower % 4 = 0 := ordered.2.2.1
  have floor := (scopes first (List.mem_cons_self ..)).preparation.afterInitial
  have memory := rv_prepared_protocol_memory_inputs (by omega) clockInverse accepted inputs
  obtain ⟨sequence, actual⟩ := rv_mixed_window_sequence (by omega) clockInverse rotationInverse accepted memory
    aligned (by omega) ordered
  exact ⟨sequence, actual, rv_prepared_protocol_sequence_at_segments hp clockInverse accepted inputs scopes ordered actual.segments⟩

theorem rv_program_protocol_window_inputs [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.RVProgramEntry} {window : HashWindow}
    (accepted : RVMixedMemoryAccepted data program) (publicProgram : RVRequestInputs data before ca)
    (ordinaryProgram : rvProgramImageWith UnifiedReduced.rvDecoderFields before oa = some program) (registry : RVSequentialProgram program)
    (scope : RVProgramProtocolWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0) :
    RVPreparedProtocolWindowInputs data program window := by
  have floor := scope.preparation.afterInitial
  have schedule := rv_program_caller_window hp clockInverse accepted publicProgram ordinaryProgram registry scope.region
    first last (by omega) (by have := scope.duration; omega) (by omega) scope.beforeTerminal
  refine ⟨schedule.family, scope.preparation, ?_, scope.duration, scope.beforeTerminal⟩
  rw [← schedule.workerCount, schedule.machineCount, scope.duration]
  omega

theorem rv_program_prepared_protocol_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {regions : List RoundRegion} {first : HashWindow} {rest : List HashWindow}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedProtocolInputs data before ca oa cells program regions)
    (registry : RVSequentialProgram program)
    (scopes : ∀ window ∈ first :: rest, RVProgramProtocolWindowInputs data program window)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    RVPreparedHashSequenceResult data before cells first rest := by
  have aligned : ∀ {windows : List HashWindow} {cut : Nat},
      WindowsOrdered cut (windows.map HashWindow.interval) →
      ∀ window ∈ windows, window.lower % 4 = 0 ∧ window.upper % 4 = 0 := by
    intro windows
    induction windows with
    | nil => intro cut _ window member; cases member
    | cons head tail ih =>
      intro cut order window member
      obtain ⟨_, _, first, last, restOrder⟩ := order
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨first, last⟩
      · exact ih restOrder window member
  apply rv_prepared_protocol_sequence hp clockInverse accepted inputs _ ordered
  intro window member
  exact rv_program_protocol_window_inputs (by norm_num [timestampBase]; omega) clockInverse accepted
    inputs.publicProgram inputs.ordinaryProgram registry (scopes window member)
    (aligned ordered window member).1 (aligned ordered window member).2

end Airbender.UnifiedReduced.Caller.Proofs
