module
public import Proven.NonVacuous.Blake2GPool
public import Proven.Compiler.NativeExtension.BlakeG

@[expose] public section
namespace Airbender.Compiler.NativeSatisfiable.BlakeG
open Airbender Airbender.Compiler NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

/-- The existing accepted row supplies every source coordinate, including clock helpers. -/
noncomputable def inputValues (index : Fin 112) : F := Airbender.NonVacuous.Blake2G.row index.val

/-- Kernel evaluation checks every source equation of this concrete witness. -/
theorem source_check : FullArithmeticNative.BlakeGCached.native.artifact.source.all
    (fun polynomial => decide (evaluate inputValues polynomial = 0)) = true := by kernel_rfl

theorem source_satisfied : Satisfies FullArithmeticNative.BlakeGCached.native.artifact.source inputValues := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp source_check polynomial member)

/-- A complete physical native assignment satisfies all scalar equations and public placements. -/
theorem witness : ∃ (physical : GKRAddress → F) (logical : Nat → F),
    Holds Captures.BlakeG.imported.circuit physical ∧
      PlacementAgreement Captures.BlakeG.imported.circuit physical logical := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeExtension.BlakeG.extension Airbender.NonVacuous.Blake2G.row source_satisfied
  exact ⟨physical, logical, accepted, placement⟩
end Airbender.Compiler.NativeSatisfiable.BlakeG
