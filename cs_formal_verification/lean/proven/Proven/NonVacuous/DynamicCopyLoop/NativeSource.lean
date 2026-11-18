module
public import Proven.NonVacuous.DynamicCopyLoop.NativeSource.CpuFirst
public import Proven.NonVacuous.DynamicCopyLoop.NativeSource.CpuLast
public import Proven.NonVacuous.DynamicCopyLoop.NativeSource.WorkerFirst
public import Proven.NonVacuous.DynamicCopyLoop.NativeSource.WorkerMiddle
public import Proven.NonVacuous.DynamicCopyLoop.NativeSource.WorkerLast

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Airbender.Compiler NativeArithmetic
set_option warningAsError true

/-- Every CPU row satisfies the source polynomials of the current cached unified circuit. -/
theorem cpu_source_check (index : Fin 16) : FullArithmeticNative.UnifiedCached.native.artifact.source.all
    (fun polynomial => decide (evaluate (NativeExtension.Unified.inputValues (machineAssignment index)) polynomial = 0)) = true := by
  by_cases low : index.val < 8
  · exact cpu_source_check_first index low
  · exact cpu_source_check_last index (Nat.le_of_not_lt low)

/-- The source polynomial proposition follows from the complete CPU check. -/
theorem cpu_source_satisfied (index : Fin 16) :
    Satisfies FullArithmeticNative.UnifiedCached.native.artifact.source
      (NativeExtension.Unified.inputValues (machineAssignment index)) := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp (cpu_source_check index) polynomial member)

/-- Both COPY workers satisfy the source polynomials of the current cached bigint circuit. -/
theorem worker_source_check (index : Fin 2) : FullArithmeticNative.BigintCached.native.artifact.source.all
    (fun polynomial => decide (evaluate (NativeExtension.Bigint.inputValues (workerAssignment index)) polynomial = 0)) = true := by
  rw [← List.take_append_drop 33 FullArithmeticNative.BigintCached.native.artifact.source, List.all_append,
    ← List.take_append_drop 7 (FullArithmeticNative.BigintCached.native.artifact.source.drop 33), List.all_append,
    worker_source_check_first index, worker_source_check_middle index, worker_source_check_last index,
    Bool.and_self, Bool.and_self]

/-- The source polynomial proposition follows from the complete bigint check. -/
theorem worker_source_satisfied (index : Fin 2) :
    Satisfies FullArithmeticNative.BigintCached.native.artifact.source
      (NativeExtension.Bigint.inputValues (workerAssignment index)) := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp (worker_source_check index) polynomial member)

end Airbender.NonVacuous.DynamicCopyLoop
