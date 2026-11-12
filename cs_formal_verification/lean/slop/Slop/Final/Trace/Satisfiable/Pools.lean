module
public import Slop.NonVacuous.BigintPool
public import Human.Trace.Delegation.RVTheorems
public import Human.Trace.ZeroTimestamp
public import Human.Trace.WritesRangeChecked
public import Human.Trace.Workers.Bigint.RVTheorems

@[expose] public section

/-! The assumptions of the delegation-pool and inits/teardowns claims can be met: the one-row bigint pool of
    `Slop/NonVacuous/BigintPool.lean`, a split-Keccak row with zero clocks, and an instance of the standalone
    inits/teardowns circuit. -/

namespace Airbender.Delegation
open NonVacuous.Bigint

theorem rv_native_memory_execution_satisfiable : RVNativeMemoryExecutionSatisfiableClaim :=
  ⟨data, before, cells, by decide, accepted, inputs, aligned, rows_ne⟩

theorem rv_operation_memory_soundness_satisfiable : RVOperationMemorySoundnessSatisfiableClaim :=
  ⟨data, before, cells, control, accepted, operation_inputs, rows_ne⟩

theorem rv_memory_soundness_satisfiable : RVMemorySoundnessSatisfiableClaim :=
  ⟨data, before, cells, by decide, accepted, inputs, rows_ne⟩

theorem no_zero_timestamp_writes_satisfiable : NoZeroTimestampWritesSatisfiableClaim :=
  ⟨data, inputs.clockRoom, inputs.invocationHigh, native, List.mem_singleton_self _,
    Bigint.importedConstraintsMemoryPorts[0], Array.getElem_mem (by decide)⟩

theorem writes_range_checked_satisfiable : WritesRangeCheckedSatisfiableClaim :=
  ⟨data, control, accepted, rfl, operation_inputs.rounds, operation_inputs.keccakActive, native,
    List.mem_singleton_self _, reads_bounded⟩

end Airbender.Delegation

namespace Airbender.Keccak.Split.Native
open Trace

theorem no_zero_timestamp_writes_satisfiable : NoZeroTimestampWritesSatisfiableClaim := by
  refine ⟨⟨[⟨.columnParity, fun _ => 0⟩], [], []⟩, ?_, ?_, ⟨.columnParity, fun _ => 0⟩, List.mem_singleton_self _,
    ColumnParity.importedConstraintsMemoryPorts[0], Array.getElem_mem (by decide)⟩ <;>
  · intro row member
    simp only [List.mem_singleton] at member
    subst row
    decide

end Airbender.Keccak.Split.Native

namespace Airbender.InitsTeardowns

theorem writes_range_checked_satisfiable : WritesRangeCheckedSatisfiableClaim :=
  ⟨⟨Vector.replicate _ 0, fun _ _ => 0⟩, initToken importedLayout 0 0,
    List.mem_flatMap.2 ⟨0, by simp [Vector.toList_replicate, show importedLayout.sets.size = 8 by rfl],
      List.mem_map.2 ⟨0, List.mem_range.2 (Nat.two_pow_pos _), rfl⟩⟩⟩

end Airbender.InitsTeardowns

namespace Airbender.Bigint.Native
open NonVacuous.Bigint

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, accepted, inputs, aligned, rfl, native, List.mem_singleton_self _, rfl⟩

end Airbender.Bigint.Native
