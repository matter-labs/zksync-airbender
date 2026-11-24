module
public import Proven.Compiler.CPUWitnesses.MulDiv.Queries003

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.MulDiv
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand24.input.fields physical = sourceFields24 logical := by
  have p50 : physical (.InnerLayer 1 11) = logical 50 :=
    placed agreement (position := 50) (by kernel_rfl)
  have p61 : physical (.InnerLayer 1 22) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  simp only [operand24, NativeLookups.Input.fields, sourceFields24, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p50, p61]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled24 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand24.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.MulDiv
