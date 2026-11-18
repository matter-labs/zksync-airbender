module
public import Proven.Compiler.CPUWitnesses.JumpBranch.Queries002

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.JumpBranch
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p3 : physical (.BaseLayerMemory 21) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p33 : physical (.BaseLayerMemory 11) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  have p51 : physical (.BaseLayerWitness 25) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p33, p51]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled16 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand16.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.JumpBranch
