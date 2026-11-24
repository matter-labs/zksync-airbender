module
public import Proven.AddSub.RVNonVacuous
public import Proven.Compiler.NativeExtension.AddSub

@[expose] public section
namespace Airbender.Compiler.NativeSatisfiable.AddSub
open Airbender Airbender.Compiler NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

/-- The existing accepted row supplies every source coordinate, including clock helpers. -/
noncomputable def inputValues (index : Fin 48) : F := NativeExtension.AddSub.inputValues Airbender.AddSub.Witness.assignment index

/-- Kernel evaluation checks every source equation of this concrete witness. -/
theorem source_check : FullArithmeticNative.AddSubCached.native.artifact.source.all
    (fun polynomial => decide (evaluate inputValues polynomial = 0)) = true := by kernel_rfl

theorem source_satisfied : Satisfies FullArithmeticNative.AddSubCached.native.artifact.source inputValues := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp source_check polynomial member)

/-- A complete physical native assignment satisfies all scalar equations and public placements. -/
theorem witness : ∃ (physical : GKRAddress → F) (logical : Nat → F),
    Holds Captures.AddSub.imported.circuit physical ∧
      PlacementAgreement Captures.AddSub.imported.circuit physical logical := by
  obtain ⟨physical, accepted, placement⟩ := NativeExtension.AddSub.extension_preserves Airbender.AddSub.Witness.assignment source_satisfied
  exact ⟨physical, Airbender.AddSub.Witness.assignment, accepted, placement⟩
end Airbender.Compiler.NativeSatisfiable.AddSub
