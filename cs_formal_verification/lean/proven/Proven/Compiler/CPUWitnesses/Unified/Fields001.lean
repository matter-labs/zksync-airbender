module
public import Proven.Compiler.CPUWitnesses.Unified.Queries001

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p44 : physical (.BaseLayerMemory 17) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  change [physical (.BaseLayerMemory 17)] = [logical 44]
  exact congrArg (fun value => [value]) p44


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled8 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand8.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p45 : physical (.BaseLayerMemory 18) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  change [physical (.BaseLayerMemory 18)] = [logical 45]
  exact congrArg (fun value => [value]) p45


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled9 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand9.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p30 : physical (.BaseLayerMemory 26) = logical 30 :=
    placed agreement (position := 30) (by kernel_rfl)
  change [physical (.BaseLayerMemory 26)] = [logical 30]
  exact congrArg (fun value => [value]) p30


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled10 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand10.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p32 : physical (.BaseLayerMemory 28) = logical 32 :=
    placed agreement (position := 32) (by kernel_rfl)
  change [physical (.BaseLayerMemory 28)] = [logical 32]
  exact congrArg (fun value => [value]) p32


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled11 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand11.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p33 : physical (.BaseLayerMemory 29) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  change [physical (.BaseLayerMemory 29)] = [logical 33]
  exact congrArg (fun value => [value]) p33


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled12 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand12.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p2 : physical (.BaseLayerMemory 24) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p34 : physical (.BaseLayerMemory 0) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  have p123 : physical (.BaseLayerWitness 52) = logical 123 :=
    placed agreement (position := 123) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p34, p123]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled13 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand13.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p3 : physical (.BaseLayerMemory 25) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p35 : physical (.BaseLayerMemory 1) = logical 35 :=
    placed agreement (position := 35) (by kernel_rfl)
  have p123 : physical (.BaseLayerWitness 52) = logical 123 :=
    placed agreement (position := 123) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p35, p123]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled14 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand14.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p2 : physical (.BaseLayerMemory 24) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p40 : physical (.BaseLayerMemory 5) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p124 : physical (.BaseLayerWitness 53) = logical 124 :=
    placed agreement (position := 124) (by kernel_rfl)
  simp only [operand15, NativeLookups.Input.fields, sourceFields15]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p40, p124]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled15 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand15.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.Unified
