module
public import Proven.NonVacuous.Blake2RoundPool
public import Proven.Compiler.NativeExtension.BlakeRound

@[expose] public section
namespace Airbender.Compiler.NativeSatisfiable.BlakeRound
open Airbender Airbender.Compiler NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

/-- The existing accepted row supplies every source coordinate, including clock helpers. -/
noncomputable def inputValues (index : Fin 763) : F := Airbender.NonVacuous.Blake2Round.row index.val

/-- Kernel evaluation checks every source equation of this concrete witness. -/
theorem source_check : FullArithmeticNative.BlakeRoundCached.native.artifact.source.all
    (fun polynomial => decide (evaluate inputValues polynomial = 0)) = true := by kernel_rfl

theorem source_satisfied : Satisfies FullArithmeticNative.BlakeRoundCached.native.artifact.source inputValues := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp source_check polynomial member)

/-- A complete physical native assignment satisfies all scalar equations and public placements. -/
theorem witness : ∃ (physical : GKRAddress → F) (logical : Nat → F),
    Holds Captures.BlakeRound.imported.circuit physical ∧
      PlacementAgreement Captures.BlakeRound.imported.circuit physical logical := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeExtension.BlakeRound.extension Airbender.NonVacuous.Blake2Round.row source_satisfied
  exact ⟨physical, logical, accepted, placement⟩
end Airbender.Compiler.NativeSatisfiable.BlakeRound
