module
public import Proven.Compiler.CPUWitnesses.WordMemory.Queries001

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.WordMemory
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p0 : physical (.BaseLayerMemory 21) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p1 : physical (.BaseLayerMemory 22) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p5 : physical (.BaseLayerMemory 4) = logical 5 :=
    placed agreement (position := 5) (by kernel_rfl)
  have p6 : physical (.BaseLayerWitness 0) = logical 6 :=
    placed agreement (position := 6) (by kernel_rfl)
  have p7 : physical (.BaseLayerWitness 1) = logical 7 :=
    placed agreement (position := 7) (by kernel_rfl)
  have p8 : physical (.BaseLayerWitness 2) = logical 8 :=
    placed agreement (position := 8) (by kernel_rfl)
  have p9 : physical (.BaseLayerWitness 3) = logical 9 :=
    placed agreement (position := 9) (by kernel_rfl)
  have p10 : physical (.BaseLayerMemory 9) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  simp only [operand8, NativeLookups.Input.fields, sourceFields8, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p0, p1, p5, p6, p7, p8, p9, p10]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (active : logical 4 = 1) : operand8.weight.value physical ≠ 0 := by
  have placed : physical (.BaseLayerMemory 20) = logical 4 :=
    WorkerConstraints.placed agreement (position := 4) (by kernel_rfl)
  change physical (.BaseLayerMemory 20) ≠ 0
  rw [placed, active]
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p12 : physical (.BaseLayerMemory 26) = logical 12 :=
    placed agreement (position := 12) (by kernel_rfl)
  change [physical (.BaseLayerMemory 26)] = [logical 12]
  exact congrArg (fun value => [value]) p12


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled9 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand9.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p3 : physical (.BaseLayerMemory 24) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p28 : physical (.BaseLayerMemory 13) = logical 28 :=
    placed agreement (position := 28) (by kernel_rfl)
  have p48 : physical (.BaseLayerWitness 7) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  simp only [operand10, NativeLookups.Input.fields, sourceFields10]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p28, p48]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled10 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand10.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p36 : physical (.InnerLayer 1 7) = logical 36 :=
    placed agreement (position := 36) (by kernel_rfl)
  change [physical (.InnerLayer 1 7)] = [logical 36]
  exact congrArg (fun value => [value]) p36


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled11 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand11.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.WordMemory.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p39 : physical (.InnerLayer 2 0) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p41 : physical (.InnerLayer 2 1) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p43 : physical (.InnerLayer 2 2) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p45 : physical (.InnerLayer 2 3) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p39, p41, p43, p45]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled12 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.WordMemory.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand12.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.WordMemory
