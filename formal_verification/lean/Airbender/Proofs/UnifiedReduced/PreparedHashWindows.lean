import Airbender.Review.UnifiedReduced.PreparedHashWindows
import Airbender.Proofs.UnifiedReduced.ControlPreparation
import Airbender.Proofs.Delegation.SpanTarget

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
  exact False.elim (inputs.profile ((inputs.family row member).symm.trans round))

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
    ⟨inputs.tables, fun row member => inputs.family row (List.mem_of_mem_filter member), entry, inputs.calls⟩
  have result := Delegation.Caller.Proofs.hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target finalBoundary.1.addresses
  exact ⟨projection.requests,
    (Delegation.Caller.Proofs.window_call_count projection.requests).trans inputs.calls,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, startBoundary, finishBoundary, selected, initialized, result⟩

end Airbender.UnifiedReduced.Caller.Proofs
