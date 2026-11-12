module
public import Proven.NonVacuous.RoundCallers.Prepared
public import Human.Trace.UnifiedReduced.RVCallerTheorems

@[expose] public section

/-! The assumptions of the prepared extended-round caller claims can be met: the prepared trace of
    `Proven/NonVacuous/RoundCallers/Prepared.lean` (`lui x12, 0x80` at clock 4, then ten callers `csrrw x0, 0x7C7, x0`
    at clocks `8 + 4 k`, fulfilled by the ten-round span (flags 0) invoked at `9 + 4 k`; window and controller region
    `(8, 48]`). -/

namespace Airbender.UnifiedReduced.Caller
open NonVacuous.RoundCallers NonVacuous.RoundCallers.Prepared

theorem rv_prepared_round_region_masks_soundness_satisfiable : RVPreparedRoundRegionMasksSoundnessSatisfiableClaim :=
  ⟨data, before, NonVacuous.FamilyCallers.callerPCs 4 10, [0], keys, ordinary, [region], region, accepted,
    protocol_inputs, region_inputs, callers_ne, region_ne⟩

theorem rv_prepared_round_masks_soundness_satisfiable : RVPreparedRoundMasksSoundnessSatisfiableClaim :=
  ⟨data, before, NonVacuous.FamilyCallers.callerPCs 4 10, [0], keys, ordinary, 0, 8, accepted, round_inputs, rfl,
    callers_ne, rows_ne⟩

theorem rv_prepared_round_window_soundness_satisfiable : RVPreparedRoundWindowSoundnessSatisfiableClaim :=
  ⟨data, before, NonVacuous.FamilyCallers.callerPCs 4 10, [0], keys, ordinary, 0, 8, 48, accepted, window_inputs, rfl,
    rfl, callers_ne, window_ne⟩

theorem rv_prepared_round_cycles_soundness_satisfiable : RVPreparedRoundCyclesSoundnessSatisfiableClaim :=
  ⟨data, ordinary, before, NonVacuous.FamilyCallers.callerPCs 4 10, [0], keys, 0, 8, accepted, round_inputs, rfl,
    started, callers_ne, rows_ne⟩

end Airbender.UnifiedReduced.Caller
