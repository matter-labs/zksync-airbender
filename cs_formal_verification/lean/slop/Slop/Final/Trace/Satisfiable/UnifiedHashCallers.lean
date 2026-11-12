module
public import Slop.NonVacuous.HashCallers.Unified
public import Slop.NonVacuous.HashCallers.Prepared
public import Human.Trace.UnifiedReduced.RVCallerTheorems

@[expose] public section

/-! The assumptions of the unified complete-span caller claims can be met: the caller-only trace of
    `Slop/NonVacuous/HashCallers/Unified.lean` (56 G callers at clocks `4 + 4 k`, the reduced G span invoked at
    `5 + 4 k`, window `(4, 228]`); those with a control preparation by the prepared trace of
    `Slop/NonVacuous/HashCallers/Prepared.lean` (`addi x12, x0, 128` at clock 4, then the 56 callers at clocks
    `8 + 4 k`, window `(8, 232]`). -/

namespace Airbender.UnifiedReduced.Caller
open NonVacuous.HashCallers NonVacuous.HashCallers.Unified
open NonVacuous.FamilyCallers (callerPCs)

theorem rv_shared_span_soundness_satisfiable : RVSharedSpanSoundnessSatisfiableClaim :=
  ⟨data, before, callerPCs 0 56, keys, .blakeG true, accepted, shared_span_inputs, callers_ne⟩

theorem rv_request_hash_window_soundness_satisfiable : RVRequestHashWindowSoundnessSatisfiableClaim :=
  ⟨data, before, callerPCs 0 56, NonVacuous.Blake2GSpan.cells, .blakeG true, 4, 228, checks,
    NonVacuous.Blake2GSpan.accepted_from start, request_inputs, window_inputs, NonVacuous.Blake2GSpan.aligned, rfl,
    rfl, by decide, callers_ne, window_ne⟩

theorem rv_joint_hash_window_soundness_satisfiable : RVJointHashWindowSoundnessSatisfiableClaim :=
  ⟨data, before, callerPCs 0 56, keys, .blakeG true, 4, 228, accepted, joint_inputs, rfl, rfl, by decide, by decide,
    callers_ne, window_ne⟩

theorem rv_prepared_hash_window_soundness_satisfiable : RVPreparedHashWindowSoundnessSatisfiableClaim :=
  ⟨Prepared.data, Prepared.before, callerPCs 4 56, [0], keys, Prepared.ordinary, .blakeG true, 8, 232,
    Prepared.accepted, Prepared.hash_window_inputs, rfl, rfl, Prepared.callers_ne, Prepared.window_ne⟩

theorem rv_prepared_hash_sequence_soundness_satisfiable : RVPreparedHashSequenceSoundnessSatisfiableClaim :=
  ⟨Prepared.data, Prepared.before, callerPCs 4 56, [0], keys, Prepared.ordinary, Prepared.hashWindow, [],
    Prepared.accepted, Prepared.hash_window_inputs, fun _ member => absurd member List.not_mem_nil, Prepared.ordered,
    Prepared.callers_ne, Prepared.window_ne⟩

theorem rv_prepared_protocol_sequence_soundness_satisfiable : RVPreparedProtocolSequenceSoundnessSatisfiableClaim :=
  ⟨Prepared.data, Prepared.before, callerPCs 4 56, [0], keys, Prepared.ordinary, [], Prepared.hashWindow, [],
    Prepared.accepted, Prepared.protocol_inputs, Prepared.protocol_window_inputs, Prepared.ordered,
    Prepared.callers_ne, Prepared.window_ne⟩

theorem rv_program_prepared_protocol_sequence_soundness_satisfiable :
    RVProgramPreparedProtocolSequenceSoundnessSatisfiableClaim :=
  ⟨Prepared.data, Prepared.before, callerPCs 4 56, [0], keys, Prepared.ordinary, [], Prepared.hashWindow, [],
    Prepared.accepted, Prepared.protocol_inputs, Prepared.sequential, Prepared.program_window_inputs,
    Prepared.ordered, Prepared.callers_ne, Prepared.window_ne⟩

end Airbender.UnifiedReduced.Caller
