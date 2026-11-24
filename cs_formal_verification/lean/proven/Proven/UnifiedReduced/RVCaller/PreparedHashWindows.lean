module
public import Human.Trace.UnifiedReduced.RVPreparedHashWindows
public import Proven.UnifiedReduced.RVCaller.ControlPreparation
public import Proven.UnifiedReduced.RVCaller.SpanTarget

@[expose] public section

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_hash_preparation_value (span : Delegation.Caller.HashSpan) :
    (hashPreparation span).rvValue = span.controlStart := by
  cases span with
  | blakeG reduced => cases reduced <;> decide +kernel
  | blakeRound flags => fin_cases flags <;> decide +kernel
  | keccak => decide +kernel

theorem rv_hash_control_register_nonzero (span : Delegation.Caller.HashSpan) :
    span.controlRegister ≠ 0 := by
  cases span with
  | blakeG _ => change (12 : BitVec 5) ≠ 0; decide
  | blakeRound _ => change (12 : BitVec 5) ≠ 0; decide
  | keccak => change (10 : BitVec 5) ≠ 0; decide

theorem rv_prepared_hash_memory_inputs [Fact p.Prime]
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (inputs : RVPreparedHashWindowInputs data before ca oa cells program span lower upper) :
    RVMixedMemoryInputs data program before ca oa cells := by
  refine ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables, ?_⟩
  intro row member round
  exact False.elim (inputs.roundsAbsent row member round)

theorem rv_prepared_hash_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    RVJointHashWindowResult data before cells span lower upper := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have memory := rv_prepared_hash_memory_inputs inputs
  have floor := inputs.preparation.afterInitial
  have duration := inputs.duration
  have projection := rv_mixed_projected_window (by omega) clockInverse rotationInverse accepted memory first last
    (by omega) (by omega) (by omega) inputs.beforeTerminal (by simpa only [inputs.calls] using duration)
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, prefixMatching, _, startBoundary, finishBoundary,
    selected, initialized, finalBoundary, target⟩ := projection.execution
  have control := rv_preparation_at_boundary (by omega) clockInverse accepted memory inputs.preparation
    (rv_hash_control_register_nonzero span) first prefixMatching startBoundary
  have entry : (Cell.register span.controlRegister).readRV atStart = some span.controlStart := by
    simpa only [rv_hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.RVProtocol (data.windowProjection lower upper start finish) atStart span :=
    ⟨inputs.tables, inputs.family, entry, inputs.calls⟩
  have result := rv_hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target finalBoundary.1.addresses
  exact ⟨projection.requests,
    (Delegation.Caller.Proofs.window_call_count projection.requests).trans inputs.calls,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, startBoundary, finishBoundary, selected, initialized, result⟩

theorem rv_prepared_hash_reference_at_states [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before atStart atFinish : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    {start finish : List (MemoryToken p)} {spanEvents : List MemoryAccess}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0)
    (prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst))
    (matching : (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst))
    (startBoundary : RVNativeBoundary start atStart cells) (finishBoundary : RVNativeBoundary finish atFinish cells)
    (spanPerm : spanEvents.Perm ((data.windowSteps lower upper).map transferEvent))
    (spanHistory : RVHistory cells spanEvents atStart atFinish) :
    Delegation.Caller.HashSpan.RVResult span (data.windowProjection lower upper start finish) atStart atFinish (Delegation.Caller.workerCells cells) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := rv_prepared_hash_memory_inputs inputs
  have floor := inputs.preparation.afterInitial
  have duration := inputs.duration
  have schedule := rv_caller_window_schedule size clockInverse accepted.toRVRequestChecks inputs.publicProgram
    first last (by omega) (by omega) (by omega) inputs.beforeTerminal (by simpa only [inputs.calls] using duration)
  have requests := rv_request_binding size clockInverse accepted.toRVRequestChecks inputs.publicProgram
  obtain ⟨selected, initialized, terminal, target⟩ :=
    rv_mixed_worker_window_at_states accepted memory schedule requests matching startBoundary finishBoundary spanPerm spanHistory
      (rv_mixed_zero_writes size clockInverse accepted memory)
  have control := rv_preparation_at_boundary (by omega) clockInverse accepted memory inputs.preparation
    (rv_hash_control_register_nonzero span) first prefixMatching startBoundary
  have entry : (Cell.register span.controlRegister).readRV atStart = some span.controlStart := by
    simpa only [rv_hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.RVProtocol (data.windowProjection lower upper start finish) atStart span :=
    ⟨inputs.tables, inputs.family, entry, inputs.calls⟩
  exact rv_hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target terminal.1.addresses

theorem rv_prepared_hash_sequence_at_segments [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {windows : List HashWindow}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : ∀ window ∈ windows, RVPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
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
      have selectedInputs := inputs window (List.mem_cons_self ..)
      have result := rv_prepared_hash_reference_at_states hp clockInverse accepted selectedInputs first last
        prefixMatching matching startBoundary finishBoundary spanPerm spanHistory
      have floor := selectedInputs.preparation.afterInitial
      have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
      have requests := rv_request_windows size clockInverse accepted.toRVRequestChecks selectedInputs.publicProgram
        first last (by omega)
      exact .cons ⟨requests, (Delegation.Caller.Proofs.window_call_count requests).trans selectedInputs.calls, result⟩
        (ih (fun next member => inputs next (List.mem_cons_of_mem _ member)) restOrder tail)

theorem rv_prepared_hash_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.RVProgramEntry} {first : HashWindow} {rest : List HashWindow}
    (accepted : RVMixedMemoryAccepted data program)
    (firstInputs : RVPreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper)
    (restInputs : ∀ window ∈ rest, RVPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    RVPreparedHashSequenceResult data before cells first rest := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have aligned : first.lower % 4 = 0 := ordered.2.2.1
  have floor := firstInputs.preparation.afterInitial
  obtain ⟨sequence, actual⟩ := rv_mixed_window_sequence (by omega) clockInverse rotationInverse accepted
    (rv_prepared_hash_memory_inputs firstInputs) aligned (by omega) ordered
  have allInputs : ∀ window ∈ first :: rest, RVPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper := by
    intro window member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstInputs
    · exact restInputs window member
  exact ⟨sequence, actual, rv_prepared_hash_sequence_at_segments hp clockInverse accepted allInputs ordered actual.segments⟩

end Airbender.UnifiedReduced.Caller.Proofs
