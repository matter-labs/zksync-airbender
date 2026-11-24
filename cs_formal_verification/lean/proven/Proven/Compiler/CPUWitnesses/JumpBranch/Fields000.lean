module
public import Proven.Compiler.CPUWitnesses.JumpBranch.Queries000

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.JumpBranch
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p34 : physical (.BaseLayerWitness 8) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  change [physical (.BaseLayerWitness 8)] = [logical 34]
  exact congrArg (fun value => [value]) p34


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled0 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand0.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p35 : physical (.BaseLayerWitness 9) = logical 35 :=
    placed agreement (position := 35) (by kernel_rfl)
  change [physical (.BaseLayerWitness 9)] = [logical 35]
  exact congrArg (fun value => [value]) p35


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled1 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand1.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p1 : physical (.BaseLayerMemory 19) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  change [physical (.BaseLayerMemory 19)] = [logical 1]
  exact congrArg (fun value => [value]) p1


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled2 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand2.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p18 : physical (.BaseLayerMemory 24) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  change [physical (.BaseLayerMemory 24)] = [logical 18]
  exact congrArg (fun value => [value]) p18


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled3 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand3.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p19 : physical (.BaseLayerMemory 25) = logical 19 :=
    placed agreement (position := 19) (by kernel_rfl)
  change [physical (.BaseLayerMemory 25)] = [logical 19]
  exact congrArg (fun value => [value]) p19


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled4 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand4.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p2 : physical (.BaseLayerMemory 20) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p20 : physical (.BaseLayerMemory 0) = logical 20 :=
    placed agreement (position := 20) (by kernel_rfl)
  have p49 : physical (.BaseLayerWitness 23) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p20, p49]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled5 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand5.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p3 : physical (.BaseLayerMemory 21) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p21 : physical (.BaseLayerMemory 1) = logical 21 :=
    placed agreement (position := 21) (by kernel_rfl)
  have p49 : physical (.BaseLayerWitness 23) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p21, p49]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled6 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand6.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p2 : physical (.BaseLayerMemory 20) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p24 : physical (.BaseLayerMemory 5) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p50 : physical (.BaseLayerWitness 24) = logical 50 :=
    placed agreement (position := 50) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p24, p50]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled7 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand7.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.JumpBranch
