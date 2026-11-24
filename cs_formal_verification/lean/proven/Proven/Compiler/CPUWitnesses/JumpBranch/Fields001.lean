module
public import Proven.Compiler.CPUWitnesses.JumpBranch.Queries001

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.JumpBranch
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p3 : physical (.BaseLayerMemory 21) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p25 : physical (.BaseLayerMemory 6) = logical 25 :=
    placed agreement (position := 25) (by kernel_rfl)
  have p50 : physical (.BaseLayerWitness 24) = logical 50 :=
    placed agreement (position := 50) (by kernel_rfl)
  simp only [operand8, NativeLookups.Input.fields, sourceFields8]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p25, p50]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled8 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand8.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p2 : physical (.BaseLayerMemory 20) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p32 : physical (.BaseLayerMemory 10) = logical 32 :=
    placed agreement (position := 32) (by kernel_rfl)
  have p51 : physical (.BaseLayerWitness 25) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  simp only [operand9, NativeLookups.Input.fields, sourceFields9]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p32, p51]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled9 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand9.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
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
  have p14 : physical (.BaseLayerWitness 6) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  have p15 : physical (.BaseLayerWitness 7) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  simp only [operand10, NativeLookups.Input.fields, sourceFields10, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p0, p1, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (active : logical 4 = 1) : operand10.weight.value physical ≠ 0 := by
  have placed : physical (.BaseLayerMemory 17) = logical 4 :=
    WorkerConstraints.placed agreement (position := 4) (by kernel_rfl)
  change physical (.BaseLayerMemory 17) ≠ 0
  rw [placed, active]
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p34 : physical (.BaseLayerWitness 8) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  have p35 : physical (.BaseLayerWitness 9) = logical 35 :=
    placed agreement (position := 35) (by kernel_rfl)
  have p41 : physical (.BaseLayerWitness 15) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  simp only [operand11, NativeLookups.Input.fields, sourceFields11, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p34, p35, p41]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled11 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand11.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p23 : physical (.BaseLayerMemory 3) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p42 : physical (.BaseLayerWitness 16) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p23, p42]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled12 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand12.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p10 : physical (.BaseLayerWitness 2) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p38 : physical (.BaseLayerWitness 12) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  have p41 : physical (.BaseLayerWitness 15) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p42 : physical (.BaseLayerWitness 16) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  have p43 : physical (.BaseLayerWitness 17) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p44 : physical (.BaseLayerWitness 18) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p10, p38, p41, p42, p43, p44]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled13 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand13.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p36 : physical (.BaseLayerWitness 10) = logical 36 :=
    placed agreement (position := 36) (by kernel_rfl)
  have p46 : physical (.BaseLayerWitness 20) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  have p16 : physical (.BaseLayerMemory 22) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p36, p46, p16]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled14 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand14.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.JumpBranch.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p36 : physical (.BaseLayerWitness 10) = logical 36 :=
    placed agreement (position := 36) (by kernel_rfl)
  change [physical (.BaseLayerWitness 10)] = [logical 36]
  exact congrArg (fun value => [value]) p36


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled15 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.JumpBranch.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand15.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.JumpBranch
