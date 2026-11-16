module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand48.input.fields physical = sourceFields48 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p264 : physical (.BaseLayerMemory 80) = logical 264 :=
    placed agreement (position := 264) (by kernel_rfl)
  have p266 : physical (.BaseLayerWitness 154) = logical 266 :=
    placed agreement (position := 266) (by kernel_rfl)
  simp only [operand48, NativeLookups.Input.fields, sourceFields48]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p264, p266]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup48).Contains (Verification.environment logical) ↔
      ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields48 physical logical agreement]
  exact source_semantics48 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand49.input.fields physical = sourceFields49 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p265 : physical (.BaseLayerMemory 81) = logical 265 :=
    placed agreement (position := 265) (by kernel_rfl)
  have p266 : physical (.BaseLayerWitness 154) = logical 266 :=
    placed agreement (position := 266) (by kernel_rfl)
  simp only [operand49, NativeLookups.Input.fields, sourceFields49]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p265, p266]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup49).Contains (Verification.environment logical) ↔
      ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields49 physical logical agreement]
  exact source_semantics49 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand50.input.fields physical = sourceFields50 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p267 : physical (.BaseLayerMemory 84) = logical 267 :=
    placed agreement (position := 267) (by kernel_rfl)
  have p269 : physical (.BaseLayerWitness 155) = logical 269 :=
    placed agreement (position := 269) (by kernel_rfl)
  simp only [operand50, NativeLookups.Input.fields, sourceFields50]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p267, p269]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup50).Contains (Verification.environment logical) ↔
      ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields50 physical logical agreement]
  exact source_semantics50 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand51.input.fields physical = sourceFields51 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p268 : physical (.BaseLayerMemory 85) = logical 268 :=
    placed agreement (position := 268) (by kernel_rfl)
  have p269 : physical (.BaseLayerWitness 155) = logical 269 :=
    placed agreement (position := 269) (by kernel_rfl)
  simp only [operand51, NativeLookups.Input.fields, sourceFields51]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p268, p269]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup51).Contains (Verification.environment logical) ↔
      ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields51 physical logical agreement]
  exact source_semantics51 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields52 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand52.input.fields physical = sourceFields52 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p270 : physical (.BaseLayerMemory 88) = logical 270 :=
    placed agreement (position := 270) (by kernel_rfl)
  have p272 : physical (.BaseLayerWitness 156) = logical 272 :=
    placed agreement (position := 272) (by kernel_rfl)
  simp only [operand52, NativeLookups.Input.fields, sourceFields52]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p270, p272]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement52 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup52).Contains (Verification.environment logical) ↔
      ∃ index, operand52.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields52 physical logical agreement]
  exact source_semantics52 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields53 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand53.input.fields physical = sourceFields53 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p271 : physical (.BaseLayerMemory 89) = logical 271 :=
    placed agreement (position := 271) (by kernel_rfl)
  have p272 : physical (.BaseLayerWitness 156) = logical 272 :=
    placed agreement (position := 272) (by kernel_rfl)
  simp only [operand53, NativeLookups.Input.fields, sourceFields53]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p271, p272]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement53 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup53).Contains (Verification.environment logical) ↔
      ∃ index, operand53.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields53 physical logical agreement]
  exact source_semantics53 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields54 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand54.input.fields physical = sourceFields54 logical := by
  have p3 : physical (.BaseLayerMemory 2) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  simp only [operand54, NativeLookups.Input.fields, sourceFields54]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement54 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup54).Contains (Verification.environment logical) ↔
      ∃ index, operand54.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields54 physical logical agreement]
  exact source_semantics54 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields55 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand55.input.fields physical = sourceFields55 logical := by
  have p37 : physical (.BaseLayerMemory 54) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  simp only [operand55, NativeLookups.Input.fields, sourceFields55]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p37]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement55 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup55).Contains (Verification.environment logical) ↔
      ∃ index, operand55.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields55 physical logical agreement]
  exact source_semantics55 logical


end Airbender.Compiler.WorkerConstraints.Bigint
