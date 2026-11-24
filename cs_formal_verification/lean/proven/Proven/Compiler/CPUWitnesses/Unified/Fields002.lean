module
public import Proven.Compiler.CPUWitnesses.Unified.Queries002

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p3 : physical (.BaseLayerMemory 25) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p41 : physical (.BaseLayerMemory 6) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p124 : physical (.BaseLayerWitness 53) = logical 124 :=
    placed agreement (position := 124) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p41, p124]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled16 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand16.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand17.input.fields physical = sourceFields17 logical := by
  have p2 : physical (.BaseLayerMemory 24) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p46 : physical (.BaseLayerMemory 12) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  have p125 : physical (.BaseLayerWitness 54) = logical 125 :=
    placed agreement (position := 125) (by kernel_rfl)
  simp only [operand17, NativeLookups.Input.fields, sourceFields17]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p46, p125]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled17 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand17.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand18.input.fields physical = sourceFields18 logical := by
  have p0 : physical (.BaseLayerMemory 22) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p1 : physical (.BaseLayerMemory 23) = logical 1 :=
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
  have p10 : physical (.BaseLayerWitness 4) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p11 : physical (.BaseLayerWitness 5) = logical 11 :=
    placed agreement (position := 11) (by kernel_rfl)
  have p12 : physical (.BaseLayerWitness 6) = logical 12 :=
    placed agreement (position := 12) (by kernel_rfl)
  have p13 : physical (.BaseLayerWitness 7) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  have p14 : physical (.BaseLayerWitness 8) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  have p15 : physical (.BaseLayerWitness 9) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  have p16 : physical (.BaseLayerWitness 10) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  have p17 : physical (.BaseLayerWitness 11) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  have p18 : physical (.BaseLayerWitness 12) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  have p19 : physical (.BaseLayerWitness 13) = logical 19 :=
    placed agreement (position := 19) (by kernel_rfl)
  have p20 : physical (.BaseLayerWitness 14) = logical 20 :=
    placed agreement (position := 20) (by kernel_rfl)
  have p21 : physical (.BaseLayerWitness 15) = logical 21 :=
    placed agreement (position := 21) (by kernel_rfl)
  have p22 : physical (.BaseLayerWitness 16) = logical 22 :=
    placed agreement (position := 22) (by kernel_rfl)
  have p23 : physical (.BaseLayerWitness 17) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p24 : physical (.BaseLayerWitness 18) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p25 : physical (.BaseLayerWitness 19) = logical 25 :=
    placed agreement (position := 25) (by kernel_rfl)
  have p26 : physical (.BaseLayerWitness 20) = logical 26 :=
    placed agreement (position := 26) (by kernel_rfl)
  have p27 : physical (.BaseLayerWitness 21) = logical 27 :=
    placed agreement (position := 27) (by kernel_rfl)
  have p28 : physical (.BaseLayerMemory 9) = logical 28 :=
    placed agreement (position := 28) (by kernel_rfl)
  have p29 : physical (.BaseLayerMemory 16) = logical 29 :=
    placed agreement (position := 29) (by kernel_rfl)
  simp only [operand18, NativeLookups.Input.fields, sourceFields18, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p0, p1, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (active : logical 4 = 1) : operand18.weight.value physical ≠ 0 := by
  have placed : physical (.BaseLayerMemory 21) = logical 4 :=
    WorkerConstraints.placed agreement (position := 4) (by kernel_rfl)
  change physical (.BaseLayerMemory 21) ≠ 0
  rw [placed, active]
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand19.input.fields physical = sourceFields19 logical := by
  have p31 : physical (.BaseLayerMemory 27) = logical 31 :=
    placed agreement (position := 31) (by kernel_rfl)
  change [physical (.BaseLayerMemory 27)] = [logical 31]
  exact congrArg (fun value => [value]) p31


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled19 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand19.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand20.input.fields physical = sourceFields20 logical := by
  have p80 : physical (.InnerLayer 1 7) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  change [physical (.InnerLayer 1 7)] = [logical 80]
  exact congrArg (fun value => [value]) p80


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled20 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand20.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand21.input.fields physical = sourceFields21 logical := by
  have p3 : physical (.BaseLayerMemory 25) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p47 : physical (.BaseLayerMemory 13) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p125 : physical (.BaseLayerWitness 54) = logical 125 :=
    placed agreement (position := 125) (by kernel_rfl)
  simp only [operand21, NativeLookups.Input.fields, sourceFields21]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p47, p125]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled21 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand21.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand22.input.fields physical = sourceFields22 logical := by
  have p83 : physical (.InnerLayer 1 9) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p84 : physical (.InnerLayer 1 10) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.InnerLayer 1 11) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p82 : physical (.InnerLayer 1 8) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  simp only [operand22, NativeLookups.Input.fields, sourceFields22, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p83, p84, p85, p82]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled22 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand22.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand23.input.fields physical = sourceFields23 logical := by
  have p87 : physical (.InnerLayer 1 13) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.InnerLayer 1 14) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p89 : physical (.InnerLayer 1 15) = logical 89 :=
    placed agreement (position := 89) (by kernel_rfl)
  have p90 : physical (.InnerLayer 1 16) = logical 90 :=
    placed agreement (position := 90) (by kernel_rfl)
  have p91 : physical (.InnerLayer 1 17) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p92 : physical (.InnerLayer 1 18) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p93 : physical (.InnerLayer 1 19) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  have p94 : physical (.InnerLayer 1 20) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  have p86 : physical (.InnerLayer 1 12) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  simp only [operand23, NativeLookups.Input.fields, sourceFields23, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p87, p88, p89, p90, p91, p92, p93, p94, p86]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled23 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand23.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.Unified
