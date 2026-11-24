module
public import Proven.NonVacuous.DynamicCopyLoop.Rows
public import Proven.Compiler.NativeExtension.Unified

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Airbender.Compiler NativeArithmetic
set_option warningAsError true

/-- CPU rows 8 to 15 satisfy the source polynomials of the current cached unified circuit. -/
theorem cpu_source_check_last (index : Fin 16) (high : 8 ≤ index.val) :
    FullArithmeticNative.UnifiedCached.native.artifact.source.all
      (fun polynomial => decide (evaluate (NativeExtension.Unified.inputValues (machineAssignment index)) polynomial = 0)) = true := by
  fin_cases index <;> first | exact absurd high (by decide) | kernel_rfl

end Airbender.NonVacuous.DynamicCopyLoop
