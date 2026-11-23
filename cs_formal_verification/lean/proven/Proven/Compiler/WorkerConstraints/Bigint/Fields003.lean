module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand24.input.fields physical = sourceFields24 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p228 : physical (.BaseLayerMemory 22) = logical 228 :=
    placed agreement (position := 228) (by kernel_rfl)
  have p230 : physical (.BaseLayerWitness 142) = logical 230 :=
    placed agreement (position := 230) (by kernel_rfl)
  simp only [operand24, NativeLookups.Input.fields, sourceFields24]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p228, p230]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields24 physical logical agreement]
  exact source_semantics24 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand25.input.fields physical = sourceFields25 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p229 : physical (.BaseLayerMemory 23) = logical 229 :=
    placed agreement (position := 229) (by kernel_rfl)
  have p230 : physical (.BaseLayerWitness 142) = logical 230 :=
    placed agreement (position := 230) (by kernel_rfl)
  simp only [operand25, NativeLookups.Input.fields, sourceFields25]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p229, p230]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields25 physical logical agreement]
  exact source_semantics25 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand26.input.fields physical = sourceFields26 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p231 : physical (.BaseLayerMemory 28) = logical 231 :=
    placed agreement (position := 231) (by kernel_rfl)
  have p233 : physical (.BaseLayerWitness 143) = logical 233 :=
    placed agreement (position := 233) (by kernel_rfl)
  simp only [operand26, NativeLookups.Input.fields, sourceFields26]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p231, p233]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields26 physical logical agreement]
  exact source_semantics26 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand27.input.fields physical = sourceFields27 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p232 : physical (.BaseLayerMemory 29) = logical 232 :=
    placed agreement (position := 232) (by kernel_rfl)
  have p233 : physical (.BaseLayerWitness 143) = logical 233 :=
    placed agreement (position := 233) (by kernel_rfl)
  simp only [operand27, NativeLookups.Input.fields, sourceFields27]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p232, p233]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields27 physical logical agreement]
  exact source_semantics27 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand28.input.fields physical = sourceFields28 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p234 : physical (.BaseLayerMemory 34) = logical 234 :=
    placed agreement (position := 234) (by kernel_rfl)
  have p236 : physical (.BaseLayerWitness 144) = logical 236 :=
    placed agreement (position := 236) (by kernel_rfl)
  simp only [operand28, NativeLookups.Input.fields, sourceFields28]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p234, p236]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields28 physical logical agreement]
  exact source_semantics28 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand29.input.fields physical = sourceFields29 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p235 : physical (.BaseLayerMemory 35) = logical 235 :=
    placed agreement (position := 235) (by kernel_rfl)
  have p236 : physical (.BaseLayerWitness 144) = logical 236 :=
    placed agreement (position := 236) (by kernel_rfl)
  simp only [operand29, NativeLookups.Input.fields, sourceFields29]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p235, p236]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields29 physical logical agreement]
  exact source_semantics29 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand30.input.fields physical = sourceFields30 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p237 : physical (.BaseLayerMemory 40) = logical 237 :=
    placed agreement (position := 237) (by kernel_rfl)
  have p239 : physical (.BaseLayerWitness 145) = logical 239 :=
    placed agreement (position := 239) (by kernel_rfl)
  simp only [operand30, NativeLookups.Input.fields, sourceFields30]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p237, p239]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields30 physical logical agreement]
  exact source_semantics30 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand31.input.fields physical = sourceFields31 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p238 : physical (.BaseLayerMemory 41) = logical 238 :=
    placed agreement (position := 238) (by kernel_rfl)
  have p239 : physical (.BaseLayerWitness 145) = logical 239 :=
    placed agreement (position := 239) (by kernel_rfl)
  simp only [operand31, NativeLookups.Input.fields, sourceFields31]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p238, p239]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields31 physical logical agreement]
  exact source_semantics31 logical


end Airbender.Compiler.WorkerConstraints.Bigint
