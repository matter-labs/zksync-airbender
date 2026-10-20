import Human.Trace.UnifiedReduced.PreparedHashWindows
import Slop.UnifiedReduced.ControlPreparation
import Slop.Delegation.SpanTarget

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem hash_preparation_value (span : Delegation.Caller.HashSpan) :
    (hashPreparation span).value = span.controlStart := by
  cases span with
  | blakeG reduced => cases reduced <;> decide +kernel
  | blakeRound flags => fin_cases flags <;> decide +kernel
  | keccak => decide +kernel

theorem hash_control_register_nonzero (span : Delegation.Caller.HashSpan) :
    span.controlRegister ≠ 0 := by
  cases span with
  | blakeG _ => change (12 : BitVec 5) ≠ 0; decide
  | blakeRound _ => change (12 : BitVec 5) ≠ 0; decide
  | keccak => change (10 : BitVec 5) ≠ 0; decide

theorem prepared_hash_memory_inputs [Fact p.Prime]
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (inputs : PreparedHashWindowInputs data before ca oa cells program span lower upper) :
    MixedMemoryInputs data program before ca oa cells := by
  refine ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables, ?_⟩
  intro row member round
  exact False.elim (inputs.roundsAbsent row member round)

theorem prepared_hash_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    JointHashWindowResult data before cells span lower upper := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have memory := prepared_hash_memory_inputs inputs
  have floor := inputs.preparation.afterInitial
  have duration := inputs.duration
  have projection := mixed_projected_window (by omega) clockInverse rotationInverse accepted memory first last
    (by omega) (by omega) (by omega) inputs.beforeTerminal (by simpa only [inputs.calls] using duration)
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, prefixMatching, _, startBoundary, finishBoundary,
    selected, initialized, finalBoundary, target⟩ := projection.execution
  have control := preparation_at_boundary (by omega) clockInverse accepted memory inputs.preparation
    (hash_control_register_nonzero span) first prefixMatching startBoundary
  have entry : (Cell.register span.controlRegister).read atStart = .ok span.controlStart atStart := by
    simpa only [hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.Protocol (data.windowProjection lower upper start finish) atStart span :=
    ⟨inputs.tables, inputs.family, entry, inputs.calls⟩
  have result := Delegation.Caller.Proofs.hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target finalBoundary.1.addresses
  exact ⟨projection.requests,
    (Delegation.Caller.Proofs.window_call_count projection.requests).trans inputs.calls,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, startBoundary, finishBoundary, selected, initialized, result⟩

theorem prepared_hash_reference_at_states [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before atStart atFinish : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    {start finish : List (MemoryToken p)} {spanEvents : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0)
    (prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst))
    (matching : (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst))
    (startBoundary : NativeBoundary start atStart cells) (finishBoundary : NativeBoundary finish atFinish cells)
    (spanPerm : spanEvents.Perm ((data.windowSteps lower upper).map transferEvent))
    (spanHistory : SailHistory cells spanEvents atStart atFinish) :
    span.Result (data.windowProjection lower upper start finish) atStart atFinish (Delegation.Caller.workerCells cells) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := prepared_hash_memory_inputs inputs
  have floor := inputs.preparation.afterInitial
  have duration := inputs.duration
  have schedule := caller_window_schedule size clockInverse accepted.toRequestChecks inputs.publicProgram
    first last (by omega) (by omega) (by omega) inputs.beforeTerminal (by simpa only [inputs.calls] using duration)
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  obtain ⟨selected, initialized, terminal, target⟩ :=
    mixed_worker_window_at_states accepted memory schedule requests matching startBoundary finishBoundary spanPerm spanHistory
  have control := preparation_at_boundary (by omega) clockInverse accepted memory inputs.preparation
    (hash_control_register_nonzero span) first prefixMatching startBoundary
  have entry : (Cell.register span.controlRegister).read atStart = .ok span.controlStart atStart := by
    simpa only [hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.Protocol (data.windowProjection lower upper start finish) atStart span :=
    ⟨inputs.tables, inputs.family, entry, inputs.calls⟩
  exact Delegation.Caller.Proofs.hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target terminal.1.addresses

theorem prepared_hash_chain [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {firstSpan secondSpan : Delegation.Caller.HashSpan}
    {a b c d : Nat}
    (accepted : MixedMemoryAccepted data program)
    (firstInputs : PreparedHashWindowInputs data before ca oa cells program firstSpan a b)
    (secondInputs : PreparedHashWindowInputs data before ca oa cells program secondSpan c d)
    (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (gap : b ≤ c) :
    PreparedHashChainResult data before cells firstSpan secondSpan a b c d := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have floor := firstInputs.preparation.afterInitial
  have firstDuration := firstInputs.duration
  have secondDuration := secondInputs.duration
  obtain ⟨chain, history⟩ := mixed_window_chain (by omega) clockInverse rotationInverse accepted
    (prepared_hash_memory_inputs firstInputs) aa ba ca' da (by omega) (by omega) gap (by omega)
  have firstResult := prepared_hash_reference_at_states hp clockInverse accepted firstInputs aa ba
    history.firstPrefixMatching history.firstMatching history.firstStartBoundary history.firstFinishBoundary
    history.firstPerm history.firstHistory
  have secondResult := prepared_hash_reference_at_states hp clockInverse accepted secondInputs ca' da
    history.secondPrefixMatching history.secondMatching history.secondStartBoundary history.secondFinishBoundary
    history.secondPerm history.secondHistory
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have firstRequests := request_windows size clockInverse accepted.toRequestChecks firstInputs.publicProgram aa ba (by omega)
  have secondRequests := request_windows size clockInverse accepted.toRequestChecks secondInputs.publicProgram ca' da (by omega)
  exact ⟨firstRequests, secondRequests,
    (Delegation.Caller.Proofs.window_call_count firstRequests).trans firstInputs.calls,
    (Delegation.Caller.Proofs.window_call_count secondRequests).trans secondInputs.calls,
    chain, history, firstResult, secondResult⟩

theorem prepared_hash_sequence_at_segments [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {windows : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ∀ window ∈ windows, PreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
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
      have selectedInputs := inputs window (List.mem_cons_self ..)
      have result := prepared_hash_reference_at_states hp clockInverse accepted selectedInputs first last
        prefixMatching matching startBoundary finishBoundary spanPerm spanHistory
      have floor := selectedInputs.preparation.afterInitial
      have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
      have requests := request_windows size clockInverse accepted.toRequestChecks selectedInputs.publicProgram
        first last (by omega)
      exact .cons ⟨requests, (Delegation.Caller.Proofs.window_call_count requests).trans selectedInputs.calls, result⟩
        (ih (fun next member => inputs next (List.mem_cons_of_mem _ member)) restOrder tail)

theorem prepared_hash_sequence [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (firstInputs : PreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper)
    (restInputs : ∀ window ∈ rest, PreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    PreparedHashSequenceResult data before cells first rest := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have aligned : first.lower % 4 = 0 := ordered.2.2.1
  have floor := firstInputs.preparation.afterInitial
  obtain ⟨sequence, actual⟩ := mixed_window_sequence (by omega) clockInverse rotationInverse accepted
    (prepared_hash_memory_inputs firstInputs) aligned (by omega) ordered
  have allInputs : ∀ window ∈ first :: rest, PreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper := by
    intro window member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstInputs
    · exact restInputs window member
  exact ⟨sequence, actual, prepared_hash_sequence_at_segments hp clockInverse accepted allInputs ordered actual.segments⟩

end Airbender.UnifiedReduced.Caller.Proofs
