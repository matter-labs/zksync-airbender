module
public import Proven.Compiler.WorkerConstraints.BlakeG.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p2 : physical (.BaseLayerMemory 54) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p105 : physical (.BaseLayerMemory 42) = logical 105 :=
    placed agreement (position := 105) (by kernel_rfl)
  have p106 : physical (.BaseLayerWitness 53) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p105, p106]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields16 physical logical agreement]
  exact source_semantics16 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand17.input.fields physical = sourceFields17 logical := by
  have p1 : physical (.BaseLayerMemory 53) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p107 : physical (.BaseLayerMemory 46) = logical 107 :=
    placed agreement (position := 107) (by kernel_rfl)
  have p109 : physical (.BaseLayerWitness 54) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  simp only [operand17, NativeLookups.Input.fields, sourceFields17]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p107, p109]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields17 physical logical agreement]
  exact source_semantics17 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand18.input.fields physical = sourceFields18 logical := by
  have p2 : physical (.BaseLayerMemory 54) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p108 : physical (.BaseLayerMemory 47) = logical 108 :=
    placed agreement (position := 108) (by kernel_rfl)
  have p109 : physical (.BaseLayerWitness 54) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  simp only [operand18, NativeLookups.Input.fields, sourceFields18]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p108, p109]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields18 physical logical agreement]
  exact source_semantics18 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand19.input.fields physical = sourceFields19 logical := by
  have p13 : physical (.BaseLayerMemory 2) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  simp only [operand19, NativeLookups.Input.fields, sourceFields19]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p13]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup19).Contains (Verification.environment logical) ↔
      ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields19 physical logical agreement]
  exact source_semantics19 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand20.input.fields physical = sourceFields20 logical := by
  have p31 : physical (.BaseLayerMemory 34) = logical 31 :=
    placed agreement (position := 31) (by kernel_rfl)
  simp only [operand20, NativeLookups.Input.fields, sourceFields20]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p31]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup20).Contains (Verification.environment logical) ↔
      ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields20 physical logical agreement]
  exact source_semantics20 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand21.input.fields physical = sourceFields21 logical := by
  have p0 : physical (.BaseLayerMemory 52) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p3 : physical (.BaseLayerMemory 48) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p5 : physical (.BaseLayerMemory 50) = logical 5 :=
    placed agreement (position := 5) (by kernel_rfl)
  have p7 : physical (.BaseLayerMemory 8) = logical 7 :=
    placed agreement (position := 7) (by kernel_rfl)
  have p8 : physical (.BaseLayerMemory 15) = logical 8 :=
    placed agreement (position := 8) (by kernel_rfl)
  have p9 : physical (.BaseLayerMemory 22) = logical 9 :=
    placed agreement (position := 9) (by kernel_rfl)
  have p10 : physical (.BaseLayerMemory 29) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p11 : physical (.BaseLayerMemory 40) = logical 11 :=
    placed agreement (position := 11) (by kernel_rfl)
  have p12 : physical (.BaseLayerMemory 45) = logical 12 :=
    placed agreement (position := 12) (by kernel_rfl)
  simp only [operand21, NativeLookups.Input.fields, sourceFields21, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p0, p3, p5, p7, p8, p9, p10, p11, p12]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup21).Contains (Verification.environment logical) ↔
      ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields21 physical logical agreement]
  exact source_semantics21 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand22.input.fields physical = sourceFields22 logical := by
  have p43 : physical (.BaseLayerWitness 6) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p41 : physical (.BaseLayerWitness 4) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p44 : physical (.BaseLayerWitness 7) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  simp only [operand22, NativeLookups.Input.fields, sourceFields22, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p43, p41, p44]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup22).Contains (Verification.environment logical) ↔
      ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields22 physical logical agreement]
  exact source_semantics22 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand23.input.fields physical = sourceFields23 logical := by
  have p27 : physical (.BaseLayerMemory 27) = logical 27 :=
    placed agreement (position := 27) (by kernel_rfl)
  have p43 : physical (.BaseLayerWitness 6) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p15 : physical (.BaseLayerMemory 6) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  have p19 : physical (.BaseLayerMemory 13) = logical 19 :=
    placed agreement (position := 19) (by kernel_rfl)
  have p33 : physical (.BaseLayerMemory 38) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  have p37 : physical (.BaseLayerWitness 0) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  have p38 : physical (.BaseLayerWitness 1) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  have p41 : physical (.BaseLayerWitness 4) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p45 : physical (.BaseLayerWitness 8) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  simp only [operand23, NativeLookups.Input.fields, sourceFields23, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p27, p43, p15, p19, p33, p37, p38, p41, p45]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup23).Contains (Verification.environment logical) ↔
      ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields23 physical logical agreement]
  exact source_semantics23 logical


end Airbender.Compiler.WorkerConstraints.BlakeG
