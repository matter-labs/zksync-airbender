module
public import Proven.NonVacuous.PooledBoot
public import Human.Trace.RVSoundness
public import Human.Trace.ZeroTimestamp
public import Human.Trace.WritesRangeChecked
public import Human.Trace.TeardownBounds

@[expose] public section

/-! The assumptions of the pooled whole-trace claims can be met: the booted one-row trace of
    `Proven/NonVacuous/PooledBoot.lean` (`ADD x3, x1, x2` at PC 0, RAM seeded by a standalone inits/teardowns
    instance). -/

namespace Airbender.Trace
open NonVacuous.PooledBoot

theorem rv_pooled_native_soundness_satisfiable : RVPooledNativeSoundnessSatisfiableClaim :=
  ⟨trace, initial, cells, program, inits, inputs program_image, accepted, decoded, rows_ne⟩

theorem boot_ram_zero_satisfiable : BootRamZeroSatisfiableClaim :=
  ⟨trace, initial, cells, program, inits, _, inputs program_image, ram_tracked⟩

theorem no_zero_timestamp_writes_satisfiable : NoZeroTimestampWritesSatisfiableClaim :=
  ⟨trace, accepted, rfl, writes_ne⟩

theorem writes_range_checked_satisfiable : WritesRangeCheckedSatisfiableClaim :=
  ⟨trace, initial, cells, program, inits, _, .inl rfl, inputs program_image, accepted, decoded, reads_bounded⟩

theorem teardowns_bounded_satisfiable : TeardownsBoundedSatisfiableClaim :=
  ⟨trace, initial, cells, program, inits, _, .inl rfl, inputs program_image, accepted, decoded, teardowns⟩

end Airbender.Trace

namespace Airbender.Trace.NonDeterminism.Pooled
open NonVacuous.PooledBoot

theorem rv_native_soundness_satisfiable : RVNativeSoundnessSatisfiableClaim :=
  ⟨trace, initial, cells, program, inits, inputs program_image_extended, accepted, decoded, ports, rows_ne⟩

end Airbender.Trace.NonDeterminism.Pooled
