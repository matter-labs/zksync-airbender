module
public import Slop.NonVacuous.UnifiedCaller
public import Human.Trace.UnifiedReduced.RVCallerTheorems

@[expose] public section

/-! The assumptions of the unified caller claims that need no complete hash span can be met: the caller trace of
    `Slop/NonVacuous/UnifiedCaller.lean` (one bigint caller at clock four, its worker written at clock seven, window
    `(4, 8]`). -/

namespace Airbender.UnifiedReduced.Caller
open NonVacuous.UnifiedCaller

theorem rv_mixed_memory_soundness_satisfiable : RVMixedMemorySoundnessSatisfiableClaim :=
  ⟨data, [], before, [0], [], cells, accepted, inputs, callers_ne⟩

theorem rv_request_window_soundness_satisfiable : RVRequestWindowSoundnessSatisfiableClaim :=
  ⟨data, before, [0], 4, 8, checks, request_inputs, rfl, rfl, by decide, callers_ne, window_ne⟩

theorem rv_mixed_window_soundness_satisfiable : RVMixedWindowSoundnessSatisfiableClaim :=
  ⟨data, [], before, [0], [], cells, 4, 8, accepted, inputs, rfl, rfl, by decide, by decide, callers_ne, window_ne⟩

theorem rv_window_projection_soundness_satisfiable : RVWindowProjectionSoundnessSatisfiableClaim :=
  ⟨data, before, [0], [], cells, 4, 8, accepted, inputs, rfl, rfl, by decide, by decide, callers_ne, window_ne⟩

theorem rv_window_schedule_soundness_satisfiable : RVWindowScheduleSoundnessSatisfiableClaim := by
  refine ⟨data, before, [0], 4, 8, checks, request_inputs, rfl, rfl, by decide, by decide, by decide +kernel,
    by decide +kernel, ?_, callers_ne, window_ne⟩
  rw [window_rows]
  rfl

theorem rv_mixed_window_projection_soundness_satisfiable : RVMixedWindowProjectionSoundnessSatisfiableClaim := by
  refine ⟨data, [], before, [0], [], cells, 4, 8, accepted, inputs, rfl, rfl, by decide, by decide,
    by decide +kernel, by decide +kernel, ?_, callers_ne, window_ne⟩
  rw [window_rows]
  rfl

theorem rv_mixed_window_sequence_soundness_satisfiable : RVMixedWindowSequenceSoundnessSatisfiableClaim :=
  ⟨data, [], before, [0], [], cells, 4, [(4, 8)], accepted, inputs, rfl, by decide, ⟨le_refl _, by decide, rfl, rfl, trivial⟩, callers_ne,
    (4, 8), List.mem_singleton_self _, window_ne⟩

theorem rv_caller_cycles_soundness_satisfiable : RVCallerCyclesSoundnessSatisfiableClaim :=
  ⟨data, [], before, [0], [], cells, accepted, inputs, by decide +kernel, callers_ne⟩

theorem rv_program_window_schedule_soundness_satisfiable : RVProgramWindowScheduleSoundnessSatisfiableClaim := by
  have registry : RVSequentialProgram [] := fun _ member => nomatch member
  have region : RVProgramCallerRegion data [] .bigint 4 8 := by
    refine ⟨fun _ member => (nomatch member), fun entry member _ => ?_⟩
    simp only [data, program, List.mem_singleton] at member
    subst entry
    rfl
  exact ⟨data, [], before, [0], [], .bigint, 4, 8, accepted, request_inputs, rfl, registry, region, rfl, rfl,
    by decide, by decide, by decide +kernel, by decide +kernel, callers_ne, window_ne⟩

end Airbender.UnifiedReduced.Caller
