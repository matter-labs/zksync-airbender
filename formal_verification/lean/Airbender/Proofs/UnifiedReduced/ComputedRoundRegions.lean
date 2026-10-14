import Airbender.Review.Trace.UnifiedReduced.ComputedRoundRegions
import Airbender.Proofs.UnifiedReduced.ComputedHashWindows
import Airbender.Proofs.Blake2Round.ControlPool

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem literal_computed_round_region_inputs [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (scope : RoundRegionInputs data program region) : ComputedRoundRegionInputs data program region :=
  ⟨scope.family, .literal scope.preparation, scope.roundsBound, scope.duration, scope.aligned, scope.beforeTerminal⟩

theorem literal_computed_protocol_inputs [Fact p.Prime]
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (inputs : PreparedProtocolInputs data before ca oa cells program regions) :
    ComputedPreparedProtocolInputs data before ca oa cells program regions :=
  ⟨inputs.toProtocolContextInputs,
    fun region member => literal_computed_round_region_inputs (inputs.scopes region member), inputs.coverage⟩

theorem literal_computed_protocol_window_inputs [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {window : HashWindow}
    (scope : PreparedProtocolWindowInputs data program window) : ComputedProtocolWindowInputs data program window :=
  ⟨scope.family, .literal scope.preparation, scope.calls, scope.duration, scope.beforeTerminal⟩

theorem computed_round_region_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program)
    (scope : ComputedRoundRegionInputs data program region) :
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have floor := hash_control_preparation_after_initial scope.preparation
  have duration := scope.duration
  have positive : 2 ≤ region.lower := by omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  obtain ⟨start, earlier, suffix⟩ := Transfer.split_at facts (region.lower - 1)
  obtain ⟨finish, window, _⟩ := Transfer.split_at suffix (region.upper - 1)
  change Transfer.Facts ⟨start, finish,
    Transfer.windowSteps (mixedData data) (region.lower - 1) (region.upper - 1)⟩ at window
  rw [← mixed_window_steps size clockInverse accepted.toRequestChecks inputs.publicProgram
    scope.aligned.1 scope.aligned.2 positive (by omega)] at window
  have prefixMatching := earlier.matching
  rw [mixed_prefix_steps data (by omega)] at prefixMatching
  obtain ⟨token, member, address, _, word⟩ := hash_control_preparation_token hp clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization scope.preparation
    scope.aligned.1 prefixMatching
  have word : token.word = Blake2Round.controlAt region.flags 0 := by
    rw [word]
    have bound := region.flags.isLt
    simp [Delegation.Caller.HashSpan.controlStart, Word.ofBitVec, Blake2Round.controlAt, limbBase, BitVec.toNat_ofNat]
    omega
  have schedule := caller_window_schedule size clockInverse accepted.toRequestChecks inputs.publicProgram
    scope.aligned.1 scope.aligned.2 positive (by omega) (by omega) scope.beforeTerminal duration
  let keep := fun token : MemoryToken p => token.address != (Cell.register 0).addressCode
  let projected := data.windowProjection region.lower region.upper start finish
  have matching := window.matching.filter keep
  have writes := caller_window_filtered_tokens schedule requests true
  have reads := caller_window_filtered_tokens schedule requests false
  change ((data.windowSteps region.lower region.upper).map Prod.snd).filter keep = _ at writes
  change ((data.windowSteps region.lower region.upper).map Prod.fst).filter keep = _ at reads
  simp only [List.filter_append, writes, reads] at matching
  have selected : Delegation.MemoryAccepted projected := by
    refine ⟨fun row member => accepted.workerConstraints row (List.mem_of_mem_filter member), matching⟩
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp (by
    change (data.machine.initialMemory.map MemoryToken.address).Nodup
    rw [image_addresses inputs.initialization]
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
    · simp [address, Cell.addressCode, Delegation.Caller.HashSpan.controlRegister]
  exact Blake2Round.Proofs.matching_masks size selected pool

theorem wrapped_program_computed_round_region_inputs [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (scope : WrappedProgramComputedRoundRegionInputs data program region) :
    ComputedRoundRegionInputs data program region := by
  have schedule := wrapped_program_hash_preparation_schedule hp clockInverse setup accepted publicProgram
    ordinaryProgram registry scope.preparation scope.code scope.aligned.1 scope.aligned.2
    scope.extent.1 scope.beforeTerminal
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

theorem wrapped_program_computed_round_region_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {region : RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program) (registry : WrappedSequentialProgram program)
    (scope : WrappedProgramComputedRoundRegionInputs data program region) :
    ComputedRoundRegionInputs data program region ∧
      ∀ row ∈ data.workers.windowRows region.lower region.upper,
        ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  have shape := wrapped_program_computed_round_region_inputs (by omega) clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram registry scope
  exact ⟨shape, computed_round_region_masks hp clockInverse accepted inputs shape⟩

theorem computed_protocol_memory_inputs [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ComputedPreparedProtocolInputs data before ca oa cells program regions) :
    MixedMemoryInputs data program before ca oa cells := by
  refine ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables, ?_⟩
  intro row member family
  obtain ⟨region, included, inside⟩ := inputs.coverage row member family
  exact computed_round_region_masks hp clockInverse accepted inputs.toProtocolContextInputs
    (inputs.scopes region included) row inside

theorem computed_round_worker_coverage [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, ComputedRoundRegionInputs data program region)
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
    have floor := hash_control_preparation_after_initial scope.preparation
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
    have floor := hash_control_preparation_after_initial scope.preparation
    have requests := request_windows size clockInverse accepted.toRequestChecks publicProgram
      scope.aligned.1 scope.aligned.2 (by omega)
    obtain ⟨selected, selectedMatch, _⟩ := requests.callerMatches caller inside
    obtain ⟨chosen, _, unique⟩ := Delegation.Requests.Proofs.unique_fulfillment binding.fulfilled binding.invocations.1
      (List.mem_map.mpr ⟨caller, callerMember, rfl⟩)
    have equal : worker = selected :=
      (unique worker ⟨member, same.symm⟩).trans
        (unique selected ⟨List.mem_of_mem_filter selectedMatch.1, selectedMatch.2.1⟩).symm
    exact ⟨region, included, equal.symm ▸ selectedMatch.1⟩

theorem computed_protocol_reference_at_states [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before atStart atFinish : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {window : HashWindow}
    {start finish : List (MemoryToken p)} {spanEvents : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ComputedPreparedProtocolInputs data before ca oa cells program regions)
    (scope : ComputedProtocolWindowInputs data program window)
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
  have memory := computed_protocol_memory_inputs (by omega) clockInverse accepted inputs
  have floor := hash_control_preparation_after_initial scope.preparation
  have duration := scope.duration
  have schedule := caller_window_schedule size clockInverse accepted.toRequestChecks inputs.publicProgram
    first last (by omega) (by omega) (by omega) scope.beforeTerminal (by simpa only [scope.calls] using duration)
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  obtain ⟨selected, initialized, terminal, target⟩ :=
    mixed_worker_window_at_states accepted memory schedule requests matching startBoundary finishBoundary spanPerm spanHistory
  have control := hash_control_preparation_at_boundary (by omega) clockInverse accepted memory scope.preparation
    first prefixMatching startBoundary
  have entry : (Cell.register window.span.controlRegister).read atStart = .ok window.span.controlStart atStart := by
    simpa only [hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.Protocol (data.windowProjection window.lower window.upper start finish)
      atStart window.span := ⟨inputs.tables, scope.family, entry, scope.calls⟩
  exact Delegation.Caller.Proofs.hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target terminal.1.addresses

theorem computed_protocol_sequence_at_segments [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {windows : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ComputedPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ windows, ComputedProtocolWindowInputs data program window)
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
      have result := computed_protocol_reference_at_states hp clockInverse accepted inputs scope first last
        prefixMatching matching startBoundary finishBoundary spanPerm spanHistory
      have floor := hash_control_preparation_after_initial scope.preparation
      have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
      have requests := request_windows size clockInverse accepted.toRequestChecks inputs.publicProgram first last (by omega)
      exact .cons ⟨requests, (Delegation.Caller.Proofs.window_call_count requests).trans scope.calls, result⟩
        (ih (fun next member => scopes next (List.mem_cons_of_mem _ member)) restOrder tail)

theorem computed_protocol_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ComputedPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, ComputedProtocolWindowInputs data program window)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    PreparedHashSequenceResult data before cells first rest := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have aligned : first.lower % 4 = 0 := ordered.2.2.1
  have floor := hash_control_preparation_after_initial (scopes first (List.mem_cons_self ..)).preparation
  have memory := computed_protocol_memory_inputs (by omega) clockInverse accepted inputs
  obtain ⟨sequence, actual⟩ := mixed_window_sequence (by omega) clockInverse rotationInverse accepted memory
    aligned (by omega) ordered
  exact ⟨sequence, actual, computed_protocol_sequence_at_segments hp clockInverse accepted inputs scopes ordered actual.segments⟩

theorem wrapped_program_computed_round_worker_coverage [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, WrappedProgramComputedRoundRegionInputs data program region)
    (coverage : WrappedProgramRoundCallerCoverage data regions) : RoundWorkerCoverage data regions := by
  apply computed_round_worker_coverage hp clockInverse setup accepted publicProgram ordinaryProgram registry _ coverage
  intro region member
  exact wrapped_program_computed_round_region_inputs hp clockInverse setup accepted publicProgram ordinaryProgram
    registry (scopes region member)

theorem wrapped_program_computed_round_live_masks [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program) (registry : WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, WrappedProgramComputedRoundRegionInputs data program region)
    (coverage : WrappedProgramRoundCallerCoverage data regions) :
    ∀ worker ∈ data.workers.rows, worker.family = .blakeRound →
      Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      ∃ round, Blake2Round.Memory.RoundMask worker.assignment round := by
  have covered := wrapped_program_computed_round_worker_coverage (by omega) clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram registry scopes coverage
  intro worker member family live
  obtain ⟨region, included, inside⟩ := (covered worker member family).mpr live
  exact (wrapped_program_computed_round_region_masks hp clockInverse accepted inputs registry
    (scopes region included)).2 worker inside

theorem wrapped_program_computed_protocol_inputs [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramComputedPreparedProtocolInputs data before ca oa cells program regions) :
    ComputedPreparedProtocolInputs data before ca oa cells program regions := by
  refine ⟨inputs.toProtocolContextInputs, ?_, inputs.coverage⟩
  intro region member
  exact wrapped_program_computed_round_region_inputs hp clockInverse inputs.setup accepted inputs.publicProgram
    inputs.ordinaryProgram inputs.registry (inputs.scopes region member)

theorem wrapped_program_computed_protocol_window_inputs [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {window : HashWindow}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (scope : WrappedProgramComputedProtocolWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0) :
    ComputedProtocolWindowInputs data program window := by
  have schedule := wrapped_program_hash_preparation_schedule hp clockInverse setup accepted publicProgram ordinaryProgram
    registry scope.preparation scope.region first last (by have := scope.duration; omega) scope.beforeTerminal
  refine ⟨schedule.family, scope.preparation, ?_, scope.duration, scope.beforeTerminal⟩
  rw [← schedule.workerCount, schedule.machineCount, scope.duration]
  omega

theorem wrapped_program_computed_protocol_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramComputedPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, WrappedProgramComputedProtocolWindowInputs data program window)
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
  have context := wrapped_program_computed_protocol_inputs (by omega) clockInverse accepted inputs
  apply computed_protocol_sequence hp clockInverse accepted context _ ordered
  intro window member
  exact wrapped_program_computed_protocol_window_inputs (by omega) clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.registry (scopes window member)
    (aligned ordered window member).1 (aligned ordered window member).2

end Airbender.UnifiedReduced.Caller.Proofs
