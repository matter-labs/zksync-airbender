module
public import Slop.NonVacuous.CallerPool
public import Slop.NonVacuous.CallerPrepared
public import Human.Circuits.AddSub.RVCallerTheorems
public import Human.Trace.Delegation.RVCallerTheorems

@[expose] public section

/-! The assumptions of the delegation caller claims can be met: the selected ADD/SUB caller of
    `Slop/NonVacuous/CallerPool.lean` (`csrrw x0, 0x7CA, x0` at PC 0, clock four) and the one-row bigint worker it
    issues to. The hash-span claims (`RVSharedSpanSoundnessClaim`, `RVRequestHashWindowSoundnessClaim`) need a complete
    hash span and are not covered here. -/

namespace Airbender.Delegation.Caller
open NonVacuous.Caller

theorem rv_soundness_satisfiable : RVSoundnessSatisfiableClaim :=
  ⟨before, [0], program, assignment, by decide, core, image, query, selected⟩

theorem rv_pc_soundness_satisfiable : RVPcSoundnessSatisfiableClaim :=
  ⟨before, [0], program, assignment, core, image, query, selected⟩

theorem rv_requests_soundness_satisfiable : RVRequestsSoundnessSatisfiableClaim :=
  ⟨data, before, [0], accepted, inputs, callers_ne⟩

theorem rv_request_memory_soundness_satisfiable : RVRequestMemorySoundnessSatisfiableClaim :=
  ⟨data, before, [0], NonVacuous.Bigint.cells, accepted, memory_inputs, callers_ne⟩

theorem rv_operation_soundness_satisfiable : RVOperationSoundnessSatisfiableClaim :=
  ⟨data, before, [0], NonVacuous.Bigint.cells, accepted, operation_inputs, callers_ne⟩

theorem rv_shared_memory_soundness_satisfiable : RVSharedMemorySoundnessSatisfiableClaim :=
  ⟨data, before, [0], cells, shared_accepted, shared_inputs, callers_ne⟩

theorem rv_shared_operation_soundness_satisfiable : RVSharedOperationSoundnessSatisfiableClaim :=
  ⟨data, before, [0], cells, shared_accepted, shared_operation_inputs, callers_ne⟩

/-- With an ordinary row: `Slop/NonVacuous/CallerPrepared.lean` (an LUI preparing the worker's pointer). -/
theorem rv_mixed_memory_soundness_satisfiable : RVMixedMemorySoundnessSatisfiableClaim :=
  ⟨NonVacuous.CallerPrepared.data, NonVacuous.CallerPrepared.program, NonVacuous.CallerPrepared.before, [4], [0],
    NonVacuous.CallerPrepared.cells, NonVacuous.CallerPrepared.mixed_accepted,
    NonVacuous.CallerPrepared.mixed_inputs, NonVacuous.CallerPrepared.callers_ne⟩

theorem rv_worker_schedule_soundness_satisfiable : RVWorkerScheduleSoundnessSatisfiableClaim :=
  ⟨data, before, [0], checks, inputs, callers_ne⟩

theorem rv_request_window_soundness_satisfiable : RVRequestWindowSoundnessSatisfiableClaim :=
  ⟨data, before, [0], 4, 8, checks, inputs, rfl, rfl, by decide, window⟩

end Airbender.Delegation.Caller
