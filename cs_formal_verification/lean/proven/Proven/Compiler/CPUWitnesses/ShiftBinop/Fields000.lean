module
public import Proven.Compiler.CPUWitnesses.ShiftBinop.Queries000

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.ShiftBinop
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p13 : physical (.BaseLayerMemory 26) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  change [physical (.BaseLayerMemory 26)] = [logical 13]
  exact congrArg (fun value => [value]) p13


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled0 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand0.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p15 : physical (.BaseLayerMemory 28) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  change [physical (.BaseLayerMemory 28)] = [logical 15]
  exact congrArg (fun value => [value]) p15


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled1 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand1.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p16 : physical (.BaseLayerMemory 29) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  change [physical (.BaseLayerMemory 29)] = [logical 16]
  exact congrArg (fun value => [value]) p16


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled2 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand2.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p2 : physical (.BaseLayerMemory 24) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p17 : physical (.BaseLayerMemory 0) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  have p92 : physical (.BaseLayerWitness 22) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  simp only [operand3, NativeLookups.Input.fields, sourceFields3]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p17, p92]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled3 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand3.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p3 : physical (.BaseLayerMemory 25) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p18 : physical (.BaseLayerMemory 1) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  have p92 : physical (.BaseLayerWitness 22) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  simp only [operand4, NativeLookups.Input.fields, sourceFields4]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p18, p92]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled4 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand4.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p2 : physical (.BaseLayerMemory 24) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p23 : physical (.BaseLayerMemory 7) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p93 : physical (.BaseLayerWitness 23) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p23, p93]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled5 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand5.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p3 : physical (.BaseLayerMemory 25) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p24 : physical (.BaseLayerMemory 8) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p93 : physical (.BaseLayerWitness 23) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p24, p93]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled6 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand6.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p2 : physical (.BaseLayerMemory 24) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p33 : physical (.BaseLayerMemory 14) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  have p94 : physical (.BaseLayerWitness 24) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p33, p94]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled7 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand7.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.ShiftBinop
