module
public import Proven.NonVacuous.UnifiedBoot
public import Human.Trace.UnifiedReduced.RVTheorems
public import Human.Trace.ZeroTimestamp
public import Human.Trace.WritesRangeChecked
public import Human.Trace.TeardownBounds

@[expose] public section

/-! The assumptions of the unified whole-trace claims can be met: the booted one-row trace of
    `Proven/NonVacuous/UnifiedBoot.lean` (`ADD x3, x1, x2` at PC 0, RAM seeded by an inline inits/teardowns
    instance). -/

namespace Airbender.UnifiedReduced
open NonVacuous.UnifiedBoot

theorem rv_execution_soundness_satisfiable : RVExecutionSoundnessSatisfiableClaim :=
  ⟨trace, initial, cells, program, inits, inputs, accepted, decoded, rows_ne⟩

theorem boot_ram_zero_satisfiable : BootRamZeroSatisfiableClaim :=
  ⟨trace, initial, cells, program, inits, inputs, ram_tracked⟩

theorem no_zero_timestamp_writes_satisfiable : NoZeroTimestampWritesSatisfiableClaim :=
  ⟨trace, accepted, rfl, writes_ne⟩

theorem writes_range_checked_satisfiable : WritesRangeCheckedSatisfiableClaim :=
  ⟨trace, accepted, reads_bounded⟩

theorem teardowns_bounded_satisfiable : TeardownsBoundedSatisfiableClaim :=
  ⟨trace, initial, cells, program, inits, inputs, accepted, teardowns⟩

end Airbender.UnifiedReduced
