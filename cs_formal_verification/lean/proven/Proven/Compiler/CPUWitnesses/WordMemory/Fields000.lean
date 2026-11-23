module
public import Proven.Compiler.CPUWitnesses.WordMemory.Queries000

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.WordMemory
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p11 : physical (.BaseLayerMemory 25) = logical 11 :=
    placed agreement (position := 11) (by kernel_rfl)
  change [physical (.BaseLayerMemory 25)] = [logical 11]
  exact congrArg (fun value => [value]) p11


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled0 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand0.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p13 : physical (.BaseLayerMemory 27) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  change [physical (.BaseLayerMemory 27)] = [logical 13]
  exact congrArg (fun value => [value]) p13


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled1 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand1.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p14 : physical (.BaseLayerMemory 28) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  change [physical (.BaseLayerMemory 28)] = [logical 14]
  exact congrArg (fun value => [value]) p14


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled2 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand2.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p2 : physical (.BaseLayerMemory 23) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p15 : physical (.BaseLayerMemory 0) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  have p46 : physical (.BaseLayerWitness 5) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  simp only [operand3, NativeLookups.Input.fields, sourceFields3]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p15, p46]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled3 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand3.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p3 : physical (.BaseLayerMemory 24) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p16 : physical (.BaseLayerMemory 1) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  have p46 : physical (.BaseLayerWitness 5) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  simp only [operand4, NativeLookups.Input.fields, sourceFields4]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p16, p46]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled4 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand4.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p2 : physical (.BaseLayerMemory 23) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p21 : physical (.BaseLayerMemory 5) = logical 21 :=
    placed agreement (position := 21) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 6) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p21, p47]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled5 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand5.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p3 : physical (.BaseLayerMemory 24) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p22 : physical (.BaseLayerMemory 6) = logical 22 :=
    placed agreement (position := 22) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 6) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p22, p47]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled6 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand6.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p2 : physical (.BaseLayerMemory 23) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p27 : physical (.BaseLayerMemory 12) = logical 27 :=
    placed agreement (position := 27) (by kernel_rfl)
  have p48 : physical (.BaseLayerWitness 7) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p27, p48]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled7 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand7.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.WordMemory
