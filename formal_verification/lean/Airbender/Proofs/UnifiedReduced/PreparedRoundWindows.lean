import Airbender.Review.Trace.UnifiedReduced.PreparedRoundWindows
import Airbender.Proofs.UnifiedReduced.PreparedHashWindows
import Airbender.Proofs.Blake2Round.ControlPool
import Airbender.Proofs.UnifiedReduced.ComputedRoundRegions

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem prepared_worker_after_cut [Fact p.Prime]
    {data : RequestTrace p} {lower : Nat}
    (prefixEmpty : data.workers.prefixRows lower = [])
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) : lower < worker.writeTime := by
  by_contra earlier
  have present : worker ∈ data.workers.prefixRows lower :=
    List.mem_filter.mpr ⟨member, decide_eq_true (by omega)⟩
  rw [prefixEmpty] at present
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
    have later := prepared_worker_after_cut inputs.prefixEmpty member
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
    have later := prepared_worker_after_cut inputs.prefixEmpty matched.1
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
    have later := prepared_worker_after_cut inputs.prefixEmpty present
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

theorem prepared_round_region_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program)
    (scope : RoundRegionInputs data program region) :
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  exact computed_round_region_masks hp clockInverse accepted inputs
    (literal_computed_round_region_inputs scope)

theorem prepared_protocol_memory_inputs [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedProtocolInputs data before ca oa cells program regions) :
    MixedMemoryInputs data program before ca oa cells :=
  computed_protocol_memory_inputs hp clockInverse accepted (literal_computed_protocol_inputs inputs)

theorem prepared_protocol_reference_at_states [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before atStart atFinish : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {window : HashWindow}
    {start finish : List (MemoryToken p)} {spanEvents : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedProtocolInputs data before ca oa cells program regions)
    (scope : PreparedProtocolWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0)
    (prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps window.lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps window.lower).map Prod.fst))
    (matching : (start ++ (data.windowSteps window.lower window.upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps window.lower window.upper).map Prod.fst))
    (startBoundary : NativeBoundary start atStart cells) (finishBoundary : NativeBoundary finish atFinish cells)
    (spanPerm : spanEvents.Perm ((data.windowSteps window.lower window.upper).map transferEvent))
    (spanHistory : SailHistory cells spanEvents atStart atFinish) :
    window.span.Result (data.windowProjection window.lower window.upper start finish) atStart atFinish
      (Delegation.Caller.workerCells cells) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := prepared_protocol_memory_inputs (by omega) clockInverse accepted inputs
  have floor := scope.preparation.afterInitial
  have duration := scope.duration
  have schedule := caller_window_schedule size clockInverse accepted.toRequestChecks inputs.publicProgram
    first last (by omega) (by omega) (by omega) scope.beforeTerminal (by simpa only [scope.calls] using duration)
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  obtain ⟨selected, initialized, terminal, target⟩ :=
    mixed_worker_window_at_states accepted memory schedule requests matching startBoundary finishBoundary spanPerm spanHistory
  have control := preparation_at_boundary (by omega) clockInverse accepted memory scope.preparation
    (hash_control_register_nonzero window.span) first prefixMatching startBoundary
  have entry : (Cell.register window.span.controlRegister).read atStart = .ok window.span.controlStart atStart := by
    simpa only [hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.Protocol (data.windowProjection window.lower window.upper start finish)
      atStart window.span := ⟨inputs.tables, scope.family, entry, scope.calls⟩
  exact Delegation.Caller.Proofs.hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target terminal.1.addresses

theorem prepared_protocol_sequence_at_segments [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {windows : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ windows, PreparedProtocolWindowInputs data program window)
    {cut : Nat} {tokens : List (MemoryToken p)} {state : State} {segments : List (WindowSegment p)}
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval))
    (actual : WindowSegmentsRealize data cells cut tokens state (windows.map HashWindow.interval) segments) :
    List.Forall₂ (HashWindowResult data cells) windows segments := by
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
      have result := prepared_protocol_reference_at_states hp clockInverse accepted inputs scope first last
        prefixMatching matching startBoundary finishBoundary spanPerm spanHistory
      have floor := scope.preparation.afterInitial
      have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
      have requests := request_windows size clockInverse accepted.toRequestChecks inputs.publicProgram first last (by omega)
      exact .cons ⟨requests, (Delegation.Caller.Proofs.window_call_count requests).trans scope.calls, result⟩
        (ih (fun next member => scopes next (List.mem_cons_of_mem _ member)) restOrder tail)

theorem prepared_protocol_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, PreparedProtocolWindowInputs data program window)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    PreparedHashSequenceResult data before cells first rest := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have aligned : first.lower % 4 = 0 := ordered.2.2.1
  have floor := (scopes first (List.mem_cons_self ..)).preparation.afterInitial
  have memory := prepared_protocol_memory_inputs (by omega) clockInverse accepted inputs
  obtain ⟨sequence, actual⟩ := mixed_window_sequence (by omega) clockInverse rotationInverse accepted memory
    aligned (by omega) ordered
  exact ⟨sequence, actual, prepared_protocol_sequence_at_segments hp clockInverse accepted inputs scopes ordered actual.segments⟩

theorem program_protocol_window_inputs [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {window : HashWindow}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : SequentialProgram program)
    (scope : ProgramProtocolWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0) :
    PreparedProtocolWindowInputs data program window := by
  have floor := scope.preparation.afterInitial
  have schedule := program_caller_window hp clockInverse accepted publicProgram ordinaryProgram registry scope.region
    first last (by omega) (by have := scope.duration; omega) (by omega) scope.beforeTerminal
  refine ⟨schedule.family, scope.preparation, ?_, scope.duration, scope.beforeTerminal⟩
  rw [← schedule.workerCount, schedule.machineCount, scope.duration]
  omega

theorem program_round_region_inputs [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : SequentialProgram program)
    (scope : ProgramRoundRegionInputs data program region) :
    RoundRegionInputs data program region := by
  have floor := scope.preparation.afterInitial
  have schedule := program_caller_window hp clockInverse accepted publicProgram ordinaryProgram registry scope.code
    scope.aligned.1 scope.aligned.2 (by omega) scope.extent.1 (by omega) scope.beforeTerminal
  have count : (data.workers.windowRows region.lower region.upper).length = (region.upper - region.lower) / 4 :=
    schedule.workerCount.symm.trans schedule.machineCount
  refine ⟨schedule.family, scope.preparation, ?_, ?_, scope.aligned, scope.beforeTerminal⟩
  · rw [count]
    have extent := scope.extent
    omega
  · rw [count]
    have aligned := scope.aligned
    have extent := scope.extent
    omega

theorem program_round_worker_coverage [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : SequentialProgram program)
    (scopes : ∀ region ∈ regions, ProgramRoundRegionInputs data program region)
    (coverage : ProgramRoundCallerCoverage data regions) : RoundWorkerCoverage data regions := by
  have size : 524288 < p := by norm_num [timestampBase] at hp; omega
  have binding := request_binding hp clockInverse accepted.toRequestChecks publicProgram
  have pcClock := sequential_program_pc_clock hp clockInverse accepted publicProgram ordinaryProgram registry
  intro worker member family
  constructor
  · rintro ⟨region, included, inside⟩ zero
    have scope := scopes region included
    have floor := scope.preparation.afterInitial
    have requests := request_windows hp clockInverse accepted.toRequestChecks publicProgram
      scope.aligned.1 scope.aligned.2 (by omega)
    exact (requests.unissued worker member zero).2 inside
  · intro live
    have fulfilled : Delegation.Requests.fulfillment worker ∈
        data.fulfillments.filter (fun call => decide (Delegation.Requests.Live call)) :=
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨worker, member, rfl⟩, decide_eq_true live⟩
    obtain ⟨caller, callerMember, same⟩ := List.mem_map.mp (binding.fulfilled.mem_iff.mpr fulfilled)
    have decoded := accepted.decoded caller callerMember
    change ∃ i : Fin data.program.length, caller.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
    obtain ⟨i, query⟩ := decoded
    let entry := data.program.get i
    have entryFamily : entry.data.family = .blakeRound :=
      (matched_caller_entry_family (by omega) query same.symm).symm.trans family
    obtain ⟨region, included, range⟩ := coverage entry (List.get_mem _ _) entryFamily
    have pc := caller_query_pc_word (by dsimp [limbBase]; omega) query
    have clock := pcClock caller (List.mem_of_mem_filter callerMember)
    rw [pc, Word.ofBitVec_value] at clock
    have inside : caller ∈ Delegation.Caller.windowCallers data.callers region.lower region.upper := by
      apply List.mem_filter.mpr
      exact ⟨callerMember, decide_eq_true (by dsimp only [entry] at range; omega)⟩
    have scope := scopes region included
    have floor := scope.preparation.afterInitial
    have requests := request_windows hp clockInverse accepted.toRequestChecks publicProgram
      scope.aligned.1 scope.aligned.2 (by omega)
    obtain ⟨selected, selectedMatch, _⟩ := requests.callerMatches caller inside
    obtain ⟨chosen, _, unique⟩ := Delegation.Requests.Proofs.unique_fulfillment binding.fulfilled binding.invocations.1
      (List.mem_map.mpr ⟨caller, callerMember, rfl⟩)
    have equal : worker = selected :=
      (unique worker ⟨member, same.symm⟩).trans
        (unique selected ⟨List.mem_of_mem_filter selectedMatch.1, selectedMatch.2.1⟩).symm
    exact ⟨region, included, equal.symm ▸ selectedMatch.1⟩

theorem program_round_live_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program) (registry : SequentialProgram program)
    (scopes : ∀ region ∈ regions, ProgramRoundRegionInputs data program region)
    (coverage : ProgramRoundCallerCoverage data regions) :
    ∀ worker ∈ data.workers.rows, worker.family = .blakeRound →
      Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      ∃ round, Blake2Round.Memory.RoundMask worker.assignment round := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have covered := program_round_worker_coverage size clockInverse accepted
    inputs.publicProgram inputs.ordinaryProgram registry scopes coverage
  intro worker member family live
  obtain ⟨region, included, inside⟩ := (covered worker member family).mpr live
  have scope := program_round_region_inputs size clockInverse accepted
    inputs.publicProgram inputs.ordinaryProgram registry (scopes region included)
  exact prepared_round_region_masks hp clockInverse accepted inputs scope worker inside

theorem round_worker_coverage_boundary [Fact p.Prime]
    {data : RequestTrace p} {regions : List RoundRegion} (coverage : RoundWorkerCoverage data regions) :
    (∀ worker ∈ data.workers.rows, worker.family = .blakeRound →
      ∃ region ∈ regions, worker ∈ data.workers.windowRows region.lower region.upper) ↔
    ¬ ∃ worker ∈ data.workers.rows, worker.family = .blakeRound ∧
      (Delegation.Requests.fulfillment worker).time = (0, 0) := by
  constructor
  · intro all ⟨worker, member, family, zero⟩
    exact ((coverage worker member family).mp (all worker member family)) zero
  · intro noZero worker member family
    apply (coverage worker member family).mpr
    intro zero
    exact noZero ⟨worker, member, family, zero⟩

theorem program_prepared_protocol_inputs [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProgramPreparedProtocolInputs data before ca oa cells program regions) :
    PreparedProtocolInputs data before ca oa cells program regions := by
  refine ⟨inputs.toProtocolContextInputs, ?_, inputs.coverage⟩
  intro region member
  exact program_round_region_inputs hp clockInverse accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.registry (inputs.scopes region member)

theorem program_prepared_protocol_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProgramPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, ProgramProtocolWindowInputs data program window)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    PreparedHashSequenceResult data before cells first rest := by
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
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have context := program_prepared_protocol_inputs size clockInverse accepted inputs
  apply prepared_protocol_sequence hp clockInverse accepted context _ ordered
  intro window member
  exact program_protocol_window_inputs (by norm_num [timestampBase]; omega) clockInverse accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.registry (scopes window member)
    (aligned ordered window member).1 (aligned ordered window member).2

theorem wrapped_program_protocol_window_inputs [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {window : HashWindow}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (scope : WrappedProgramProtocolWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0) :
    PreparedProtocolWindowInputs data program window := by
  have floor := scope.preparation.afterInitial
  have schedule := wrapped_program_caller_window hp clockInverse setup accepted publicProgram ordinaryProgram registry scope.region
    first last (by omega) (by have := scope.duration; omega) (by omega) scope.beforeTerminal
  refine ⟨schedule.family, scope.preparation, ?_, scope.duration, scope.beforeTerminal⟩
  rw [← schedule.workerCount, schedule.machineCount, scope.duration]
  omega

theorem wrapped_program_round_region_inputs [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (scope : WrappedProgramRoundRegionInputs data program region) :
    RoundRegionInputs data program region := by
  have floor := scope.preparation.afterInitial
  have schedule := wrapped_program_caller_window hp clockInverse setup accepted publicProgram ordinaryProgram registry scope.code
    scope.aligned.1 scope.aligned.2 (by omega) scope.extent.1 (by omega) scope.beforeTerminal
  have count : (data.workers.windowRows region.lower region.upper).length = (region.upper - region.lower) / 4 :=
    schedule.workerCount.symm.trans schedule.machineCount
  refine ⟨schedule.family, scope.preparation, ?_, ?_, scope.aligned, scope.beforeTerminal⟩
  · rw [count]
    have extent := scope.extent
    omega
  · rw [count]
    have aligned := scope.aligned
    have extent := scope.extent
    omega

theorem wrapped_program_round_worker_coverage [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, WrappedProgramRoundRegionInputs data program region)
    (coverage : WrappedProgramRoundCallerCoverage data regions) : RoundWorkerCoverage data regions := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have binding := request_binding size clockInverse accepted.toRequestChecks publicProgram
  have pcClock := wrapped_program_pc_clock hp clockInverse setup accepted publicProgram ordinaryProgram registry
  have clocks := state_clock_inputs size clockInverse accepted.constraints accepted.states
    publicProgram.initialClock publicProgram.initialAligned
  have intervals := state_clock_interval size clockInverse accepted.constraints accepted.states
    publicProgram.initialClock publicProgram.initialAligned
  intro worker member family
  constructor
  · rintro ⟨region, included, inside⟩ zero
    have scope := scopes region included
    have floor := scope.preparation.afterInitial
    have requests := request_windows size clockInverse accepted.toRequestChecks publicProgram
      scope.aligned.1 scope.aligned.2 (by omega)
    exact (requests.unissued worker member zero).2 inside
  · intro live
    have fulfilled : Delegation.Requests.fulfillment worker ∈
        data.fulfillments.filter (fun call => decide (Delegation.Requests.Live call)) :=
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨worker, member, rfl⟩, decide_eq_true live⟩
    obtain ⟨caller, callerMember, same⟩ := List.mem_map.mp (binding.fulfilled.mem_iff.mpr fulfilled)
    have decoded := accepted.decoded caller callerMember
    change ∃ i : Fin data.program.length, caller.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
    obtain ⟨i, query⟩ := decoded
    let entry := data.program.get i
    have entryFamily : entry.data.family = .blakeRound :=
      (matched_caller_entry_family (by omega) query same.symm).symm.trans family
    have machineMember := List.mem_of_mem_filter callerMember
    have pc := caller_query_pc_word (by dsimp [limbBase]; omega) query
    have clock := pcClock caller machineMember
    rw [pc, Word.ofBitVec_roundtrip] at clock
    have bounds := intervals caller machineMember
    have alignment : Delegation.Caller.startClock caller % 4 = 0 := by
      simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
        using (clocks caller machineMember).2
    obtain ⟨region, included, range⟩ := coverage entry (List.get_mem _ _) entryFamily
      (Delegation.Caller.startClock caller) bounds.1 bounds.2 alignment clock
    have inside : caller ∈ Delegation.Caller.windowCallers data.callers region.lower region.upper := by
      apply List.mem_filter.mpr
      exact ⟨callerMember, decide_eq_true range⟩
    have scope := scopes region included
    have floor := scope.preparation.afterInitial
    have requests := request_windows size clockInverse accepted.toRequestChecks publicProgram
      scope.aligned.1 scope.aligned.2 (by omega)
    obtain ⟨selected, selectedMatch, _⟩ := requests.callerMatches caller inside
    obtain ⟨chosen, _, unique⟩ := Delegation.Requests.Proofs.unique_fulfillment binding.fulfilled binding.invocations.1
      (List.mem_map.mpr ⟨caller, callerMember, rfl⟩)
    have equal : worker = selected :=
      (unique worker ⟨member, same.symm⟩).trans
        (unique selected ⟨List.mem_of_mem_filter selectedMatch.1, selectedMatch.2.1⟩).symm
    exact ⟨region, included, equal.symm ▸ selectedMatch.1⟩

theorem wrapped_program_round_live_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program) (registry : WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, WrappedProgramRoundRegionInputs data program region)
    (coverage : WrappedProgramRoundCallerCoverage data regions) :
    ∀ worker ∈ data.workers.rows, worker.family = .blakeRound →
      Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      ∃ round, Blake2Round.Memory.RoundMask worker.assignment round := by
  have minimum : 4194304 ≤ p := by omega
  have covered := wrapped_program_round_worker_coverage minimum clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram registry scopes coverage
  intro worker member family live
  obtain ⟨region, included, inside⟩ := (covered worker member family).mpr live
  have scope := wrapped_program_round_region_inputs minimum clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram registry (scopes region included)
  exact prepared_round_region_masks hp clockInverse accepted inputs scope worker inside

theorem wrapped_program_prepared_protocol_inputs [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramPreparedProtocolInputs data before ca oa cells program regions) :
    PreparedProtocolInputs data before ca oa cells program regions := by
  refine ⟨inputs.toProtocolContextInputs, ?_, inputs.coverage⟩
  intro region member
  exact wrapped_program_round_region_inputs hp clockInverse inputs.setup accepted inputs.publicProgram
    inputs.ordinaryProgram inputs.registry (inputs.scopes region member)

theorem wrapped_program_prepared_protocol_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, WrappedProgramProtocolWindowInputs data program window)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    PreparedHashSequenceResult data before cells first rest := by
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
  have context := wrapped_program_prepared_protocol_inputs (by omega) clockInverse accepted inputs
  apply prepared_protocol_sequence hp clockInverse accepted context _ ordered
  intro window member
  exact wrapped_program_protocol_window_inputs (by omega) clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.registry (scopes window member)
    (aligned ordered window member).1 (aligned ordered window member).2

end Airbender.UnifiedReduced.Caller.Proofs
