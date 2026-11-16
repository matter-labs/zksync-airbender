module
public import Proven.Compiler.CPUWitnesses.MulDiv.Queries001

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.MulDiv
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p17 : physical (.BaseLayerMemory 25) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  change [physical (.BaseLayerMemory 25)] = [logical 17]
  exact congrArg (fun value => [value]) p17


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled8 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand8.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p2 : physical (.BaseLayerMemory 20) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p18 : physical (.BaseLayerMemory 0) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  have p65 : physical (.BaseLayerWitness 18) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  simp only [operand9, NativeLookups.Input.fields, sourceFields9]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p18, p65]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled9 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand9.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p3 : physical (.BaseLayerMemory 21) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p19 : physical (.BaseLayerMemory 1) = logical 19 :=
    placed agreement (position := 19) (by kernel_rfl)
  have p65 : physical (.BaseLayerWitness 18) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  simp only [operand10, NativeLookups.Input.fields, sourceFields10]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p19, p65]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled10 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand10.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p2 : physical (.BaseLayerMemory 20) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p22 : physical (.BaseLayerMemory 5) = logical 22 :=
    placed agreement (position := 22) (by kernel_rfl)
  have p66 : physical (.BaseLayerWitness 19) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  simp only [operand11, NativeLookups.Input.fields, sourceFields11]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p22, p66]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled11 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand11.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p3 : physical (.BaseLayerMemory 21) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p23 : physical (.BaseLayerMemory 6) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p66 : physical (.BaseLayerWitness 19) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p23, p66]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled12 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand12.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p2 : physical (.BaseLayerMemory 20) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p30 : physical (.BaseLayerMemory 10) = logical 30 :=
    placed agreement (position := 30) (by kernel_rfl)
  have p67 : physical (.BaseLayerWitness 20) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p30, p67]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled13 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand13.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p0 : physical (.BaseLayerMemory 18) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p1 : physical (.BaseLayerMemory 19) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p5 : physical (.BaseLayerMemory 4) = logical 5 :=
    placed agreement (position := 5) (by kernel_rfl)
  have p6 : physical (.BaseLayerMemory 9) = logical 6 :=
    placed agreement (position := 6) (by kernel_rfl)
  have p7 : physical (.BaseLayerMemory 14) = logical 7 :=
    placed agreement (position := 7) (by kernel_rfl)
  have p8 : physical (.BaseLayerWitness 0) = logical 8 :=
    placed agreement (position := 8) (by kernel_rfl)
  have p9 : physical (.BaseLayerWitness 1) = logical 9 :=
    placed agreement (position := 9) (by kernel_rfl)
  have p10 : physical (.BaseLayerWitness 2) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p11 : physical (.BaseLayerWitness 3) = logical 11 :=
    placed agreement (position := 11) (by kernel_rfl)
  have p12 : physical (.BaseLayerWitness 4) = logical 12 :=
    placed agreement (position := 12) (by kernel_rfl)
  have p13 : physical (.BaseLayerWitness 5) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p0, p1, p5, p6, p7, p8, p9, p10, p11, p12, p13]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (active : logical 4 = 1) : operand14.weight.value physical ≠ 0 := by
  have placed : physical (.BaseLayerMemory 17) = logical 4 :=
    WorkerConstraints.placed agreement (position := 4) (by kernel_rfl)
  change physical (.BaseLayerMemory 17) ≠ 0
  rw [placed, active]
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p24 : physical (.BaseLayerMemory 7) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p25 : physical (.BaseLayerMemory 8) = logical 25 :=
    placed agreement (position := 25) (by kernel_rfl)
  have p32 : physical (.BaseLayerWitness 6) = logical 32 :=
    placed agreement (position := 32) (by kernel_rfl)
  simp only [operand15, NativeLookups.Input.fields, sourceFields15, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p24, p25, p32]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled15 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand15.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.MulDiv
