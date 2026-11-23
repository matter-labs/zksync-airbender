module
public import Proven.Compiler.CPUWitnesses.MulDiv.Queries002

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.MulDiv
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p24 : physical (.BaseLayerMemory 7) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p33 : physical (.BaseLayerWitness 7) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p24, p33]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled16 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand16.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand17.input.fields physical = sourceFields17 logical := by
  have p25 : physical (.BaseLayerMemory 8) = logical 25 :=
    placed agreement (position := 25) (by kernel_rfl)
  have p34 : physical (.BaseLayerWitness 8) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  simp only [operand17, NativeLookups.Input.fields, sourceFields17, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p25, p34]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled17 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand17.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand18.input.fields physical = sourceFields18 logical := by
  have p41 : physical (.BaseLayerWitness 15) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  simp only [operand18, NativeLookups.Input.fields, sourceFields18, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p41]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled18 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand18.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand19.input.fields physical = sourceFields19 logical := by
  have p42 : physical (.BaseLayerWitness 16) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  simp only [operand19, NativeLookups.Input.fields, sourceFields19, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p42]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled19 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand19.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand20.input.fields physical = sourceFields20 logical := by
  have p43 : physical (.BaseLayerWitness 17) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  simp only [operand20, NativeLookups.Input.fields, sourceFields20, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p43]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled20 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand20.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand21.input.fields physical = sourceFields21 logical := by
  have p15 : physical (.BaseLayerMemory 23) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  change [physical (.BaseLayerMemory 23)] = [logical 15]
  exact congrArg (fun value => [value]) p15


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled21 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand21.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand22.input.fields physical = sourceFields22 logical := by
  have p3 : physical (.BaseLayerMemory 21) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p31 : physical (.BaseLayerMemory 11) = logical 31 :=
    placed agreement (position := 31) (by kernel_rfl)
  have p67 : physical (.BaseLayerWitness 20) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  simp only [operand22, NativeLookups.Input.fields, sourceFields22]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p31, p67]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled22 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand22.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand23.input.fields physical = sourceFields23 logical := by
  have p49 : physical (.InnerLayer 1 10) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  have p60 : physical (.InnerLayer 1 21) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  simp only [operand23, NativeLookups.Input.fields, sourceFields23, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p49, p60]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled23 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand23.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.MulDiv
