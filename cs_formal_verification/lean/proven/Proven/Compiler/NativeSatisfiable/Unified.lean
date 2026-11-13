module
public import Proven.NonVacuous.UnifiedBoot
public import Proven.Compiler.NativeExtension.Unified

@[expose] public section
namespace Airbender.Compiler.NativeSatisfiable.Unified
open Airbender Airbender.Compiler NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

/-- The existing accepted row supplies every source coordinate, including clock helpers. -/
noncomputable def inputValues (index : Fin 137) : F := Airbender.NonVacuous.UnifiedBoot.assignment index.val

/-- Kernel evaluation checks every source equation of this concrete witness. -/
theorem source_check : FullArithmeticNative.UnifiedCached.native.artifact.source.all
    (fun polynomial => decide (evaluate inputValues polynomial = 0)) = true := by kernel_rfl

theorem source_satisfied : Satisfies FullArithmeticNative.UnifiedCached.native.artifact.source inputValues := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp source_check polynomial member)

/-- A complete physical native assignment satisfies all scalar equations and public placements. -/
theorem witness : ∃ (physical : GKRAddress → F) (logical : Nat → F),
    Holds Captures.Unified.imported.circuit physical ∧
      PlacementAgreement Captures.Unified.imported.circuit physical logical := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeExtension.Unified.extension Airbender.NonVacuous.UnifiedBoot.assignment source_satisfied
  exact ⟨physical, logical, accepted, placement⟩
end Airbender.Compiler.NativeSatisfiable.Unified
