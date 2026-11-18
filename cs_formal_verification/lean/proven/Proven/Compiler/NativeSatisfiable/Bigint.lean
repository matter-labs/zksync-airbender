module
public import Proven.NonVacuous.BigintPool
public import Proven.Compiler.NativeExtension.Bigint

@[expose] public section
namespace Airbender.Compiler.NativeSatisfiable.Bigint
open Airbender Airbender.Compiler NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

/-- The existing accepted row supplies every source coordinate, including clock helpers. -/
noncomputable def inputValues (index : Fin 276) : F := NativeExtension.Bigint.inputValues Airbender.NonVacuous.Bigint.row index

/-- Kernel evaluation checks every source equation of this concrete witness. -/
theorem source_check : FullArithmeticNative.BigintCached.native.artifact.source.all
    (fun polynomial => decide (evaluate inputValues polynomial = 0)) = true := by kernel_rfl

theorem source_satisfied : Satisfies FullArithmeticNative.BigintCached.native.artifact.source inputValues := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp source_check polynomial member)

/-- A complete physical native assignment satisfies all scalar equations and public placements. -/
theorem witness : ∃ (physical : GKRAddress → F) (logical : Nat → F),
    Holds Captures.Bigint.imported.circuit physical ∧
      PlacementAgreement Captures.Bigint.imported.circuit physical logical := by
  obtain ⟨physical, accepted, placement⟩ := NativeExtension.Bigint.extension_preserves Airbender.NonVacuous.Bigint.row source_satisfied
  exact ⟨physical, Airbender.NonVacuous.Bigint.row, accepted, placement⟩
end Airbender.Compiler.NativeSatisfiable.Bigint
