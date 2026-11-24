module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p216 : physical (.BaseLayerMemory 0) = logical 216 :=
    placed agreement (position := 216) (by kernel_rfl)
  have p218 : physical (.BaseLayerWitness 138) = logical 218 :=
    placed agreement (position := 218) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p216, p218]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields16 physical logical agreement]
  exact source_semantics16 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand17.input.fields physical = sourceFields17 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p217 : physical (.BaseLayerMemory 1) = logical 217 :=
    placed agreement (position := 217) (by kernel_rfl)
  have p218 : physical (.BaseLayerWitness 138) = logical 218 :=
    placed agreement (position := 218) (by kernel_rfl)
  simp only [operand17, NativeLookups.Input.fields, sourceFields17]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p217, p218]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields17 physical logical agreement]
  exact source_semantics17 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand18.input.fields physical = sourceFields18 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p219 : physical (.BaseLayerMemory 4) = logical 219 :=
    placed agreement (position := 219) (by kernel_rfl)
  have p221 : physical (.BaseLayerWitness 139) = logical 221 :=
    placed agreement (position := 221) (by kernel_rfl)
  simp only [operand18, NativeLookups.Input.fields, sourceFields18]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p219, p221]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields18 physical logical agreement]
  exact source_semantics18 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand19.input.fields physical = sourceFields19 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p220 : physical (.BaseLayerMemory 5) = logical 220 :=
    placed agreement (position := 220) (by kernel_rfl)
  have p221 : physical (.BaseLayerWitness 139) = logical 221 :=
    placed agreement (position := 221) (by kernel_rfl)
  simp only [operand19, NativeLookups.Input.fields, sourceFields19]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p220, p221]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup19).Contains (Verification.environment logical) ↔
      ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields19 physical logical agreement]
  exact source_semantics19 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand20.input.fields physical = sourceFields20 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p222 : physical (.BaseLayerMemory 10) = logical 222 :=
    placed agreement (position := 222) (by kernel_rfl)
  have p224 : physical (.BaseLayerWitness 140) = logical 224 :=
    placed agreement (position := 224) (by kernel_rfl)
  simp only [operand20, NativeLookups.Input.fields, sourceFields20]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p222, p224]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup20).Contains (Verification.environment logical) ↔
      ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields20 physical logical agreement]
  exact source_semantics20 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand21.input.fields physical = sourceFields21 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p223 : physical (.BaseLayerMemory 11) = logical 223 :=
    placed agreement (position := 223) (by kernel_rfl)
  have p224 : physical (.BaseLayerWitness 140) = logical 224 :=
    placed agreement (position := 224) (by kernel_rfl)
  simp only [operand21, NativeLookups.Input.fields, sourceFields21]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p223, p224]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup21).Contains (Verification.environment logical) ↔
      ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields21 physical logical agreement]
  exact source_semantics21 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand22.input.fields physical = sourceFields22 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p225 : physical (.BaseLayerMemory 16) = logical 225 :=
    placed agreement (position := 225) (by kernel_rfl)
  have p227 : physical (.BaseLayerWitness 141) = logical 227 :=
    placed agreement (position := 227) (by kernel_rfl)
  simp only [operand22, NativeLookups.Input.fields, sourceFields22]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p225, p227]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup22).Contains (Verification.environment logical) ↔
      ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields22 physical logical agreement]
  exact source_semantics22 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand23.input.fields physical = sourceFields23 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p226 : physical (.BaseLayerMemory 17) = logical 226 :=
    placed agreement (position := 226) (by kernel_rfl)
  have p227 : physical (.BaseLayerWitness 141) = logical 227 :=
    placed agreement (position := 227) (by kernel_rfl)
  simp only [operand23, NativeLookups.Input.fields, sourceFields23]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p226, p227]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup23).Contains (Verification.environment logical) ↔
      ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields23 physical logical agreement]
  exact source_semantics23 logical


end Airbender.Compiler.WorkerConstraints.Bigint
