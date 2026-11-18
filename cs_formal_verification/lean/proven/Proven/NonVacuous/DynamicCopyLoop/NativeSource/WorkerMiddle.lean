module
public import Proven.NonVacuous.DynamicCopyLoop.Rows
public import Proven.Compiler.NativeExtension.Bigint

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Airbender.Compiler NativeArithmetic
set_option warningAsError true

/-- The bigint source polynomials 33 to 39 hold for both COPY workers. -/
theorem worker_source_check_middle (index : Fin 2) :
    ((FullArithmeticNative.BigintCached.native.artifact.source.drop 33).take 7).all
      (fun polynomial => decide (evaluate (NativeExtension.Bigint.inputValues (workerAssignment index)) polynomial = 0)) = true := by
  fin_cases index <;> kernel_rfl

end Airbender.NonVacuous.DynamicCopyLoop
