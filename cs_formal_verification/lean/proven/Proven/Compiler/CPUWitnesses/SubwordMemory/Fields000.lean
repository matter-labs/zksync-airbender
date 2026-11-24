module
public import Proven.Compiler.CPUWitnesses.SubwordMemory.Queries000

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.SubwordMemory
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.SubwordMemory.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p40 : physical (.BaseLayerWitness 8) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  change [physical (.BaseLayerWitness 8)] = [logical 40]
  exact congrArg (fun value => [value]) p40


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled0 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand0.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.SubwordMemory.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p13 : physical (.BaseLayerMemory 25) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  change [physical (.BaseLayerMemory 25)] = [logical 13]
  exact congrArg (fun value => [value]) p13


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled1 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand1.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.SubwordMemory.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p14 : physical (.BaseLayerMemory 26) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  change [physical (.BaseLayerMemory 26)] = [logical 14]
  exact congrArg (fun value => [value]) p14


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled2 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand2.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.SubwordMemory.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p15 : physical (.BaseLayerMemory 27) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  change [physical (.BaseLayerMemory 27)] = [logical 15]
  exact congrArg (fun value => [value]) p15


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled3 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand3.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.SubwordMemory.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p16 : physical (.BaseLayerMemory 28) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  change [physical (.BaseLayerMemory 28)] = [logical 16]
  exact congrArg (fun value => [value]) p16


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled4 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand4.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.SubwordMemory.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p2 : physical (.BaseLayerMemory 23) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p17 : physical (.BaseLayerMemory 0) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  have p62 : physical (.BaseLayerWitness 11) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p17, p62]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled5 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand5.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.SubwordMemory.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p3 : physical (.BaseLayerMemory 24) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p18 : physical (.BaseLayerMemory 1) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  have p62 : physical (.BaseLayerWitness 11) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p18, p62]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled6 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand6.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.SubwordMemory.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p2 : physical (.BaseLayerMemory 23) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p23 : physical (.BaseLayerMemory 5) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p63 : physical (.BaseLayerWitness 12) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p23, p63]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled7 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand7.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.SubwordMemory
