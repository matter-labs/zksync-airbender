module
public import Proven.NonVacuous.UnifiedPrepared
public import Human.Trace.UnifiedReduced.RVCallerTheorems

@[expose] public section

/-! The assumptions of the unified caller claims with an ordinary program can be met: the trace of
    `Proven/NonVacuous/UnifiedPrepared.lean` (`LUI x10, 0x400` at clock 4, the bigint call at clock 8, `LUI x10, 0x400`
    again at clock 12; the worker written at clock 11; window `(8, 12]`, preparation cuts 8 and 16). -/

namespace Airbender.UnifiedReduced.Caller
open NonVacuous.UnifiedPrepared

theorem rv_control_preparation_soundness_satisfiable : RVControlPreparationSoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], cells, 8, 10, .lui 0x400, accepted, inputs, preparation, by decide, rfl,
    callers_ne⟩

theorem rv_control_preparation_window_soundness_satisfiable :
    RVControlPreparationWindowSoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], cells, 8, 16, 10, 10, .lui 0x400, .lui 0x400, accepted, inputs, preparation,
    preparation_again, by decide, by decide, rfl, rfl, by decide, callers_ne, window_ne⟩

theorem rv_mixed_memory_soundness_satisfiable : RVMixedMemorySoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], cells, accepted, inputs, callers_ne⟩

theorem rv_mixed_window_soundness_satisfiable : RVMixedWindowSoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], cells, 8, 12, accepted, inputs, rfl, rfl, by decide, by decide, callers_ne,
    call_window_ne⟩

theorem rv_mixed_window_projection_soundness_satisfiable : RVMixedWindowProjectionSoundnessSatisfiableClaim := by
  refine ⟨data, program, before, [4], [0, 8], cells, 8, 12, accepted, inputs, rfl, rfl, by decide, by decide,
    by decide +kernel, by decide +kernel, ?_, callers_ne, call_window_ne⟩
  rw [call_window]
  rfl

theorem rv_mixed_window_sequence_soundness_satisfiable : RVMixedWindowSequenceSoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], cells, 8, [(8, 12)], accepted, inputs, rfl, by decide,
    ⟨le_refl _, by decide, rfl, rfl, trivial⟩, callers_ne, (8, 12), List.mem_singleton_self _, call_window_ne⟩

theorem rv_caller_cycles_soundness_satisfiable : RVCallerCyclesSoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], cells, accepted, inputs, by decide +kernel, callers_ne⟩

theorem rv_program_window_schedule_soundness_satisfiable : RVProgramWindowScheduleSoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], .bigint, 8, 12, accepted, request_inputs, program_image, sequential,
    caller_region, rfl, rfl, by decide, by decide, by decide +kernel, by decide +kernel, callers_ne, call_window_ne⟩

end Airbender.UnifiedReduced.Caller
