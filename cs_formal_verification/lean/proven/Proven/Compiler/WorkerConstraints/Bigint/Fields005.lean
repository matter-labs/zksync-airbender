module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand40.input.fields physical = sourceFields40 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p252 : physical (.BaseLayerMemory 64) = logical 252 :=
    placed agreement (position := 252) (by kernel_rfl)
  have p254 : physical (.BaseLayerWitness 150) = logical 254 :=
    placed agreement (position := 254) (by kernel_rfl)
  simp only [operand40, NativeLookups.Input.fields, sourceFields40]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p252, p254]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup40).Contains (Verification.environment logical) ↔
      ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields40 physical logical agreement]
  exact source_semantics40 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand41.input.fields physical = sourceFields41 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p253 : physical (.BaseLayerMemory 65) = logical 253 :=
    placed agreement (position := 253) (by kernel_rfl)
  have p254 : physical (.BaseLayerWitness 150) = logical 254 :=
    placed agreement (position := 254) (by kernel_rfl)
  simp only [operand41, NativeLookups.Input.fields, sourceFields41]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p253, p254]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup41).Contains (Verification.environment logical) ↔
      ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields41 physical logical agreement]
  exact source_semantics41 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand42.input.fields physical = sourceFields42 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p255 : physical (.BaseLayerMemory 68) = logical 255 :=
    placed agreement (position := 255) (by kernel_rfl)
  have p257 : physical (.BaseLayerWitness 151) = logical 257 :=
    placed agreement (position := 257) (by kernel_rfl)
  simp only [operand42, NativeLookups.Input.fields, sourceFields42]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p255, p257]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup42).Contains (Verification.environment logical) ↔
      ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields42 physical logical agreement]
  exact source_semantics42 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand43.input.fields physical = sourceFields43 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p256 : physical (.BaseLayerMemory 69) = logical 256 :=
    placed agreement (position := 256) (by kernel_rfl)
  have p257 : physical (.BaseLayerWitness 151) = logical 257 :=
    placed agreement (position := 257) (by kernel_rfl)
  simp only [operand43, NativeLookups.Input.fields, sourceFields43]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p256, p257]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup43).Contains (Verification.environment logical) ↔
      ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields43 physical logical agreement]
  exact source_semantics43 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand44.input.fields physical = sourceFields44 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p258 : physical (.BaseLayerMemory 72) = logical 258 :=
    placed agreement (position := 258) (by kernel_rfl)
  have p260 : physical (.BaseLayerWitness 152) = logical 260 :=
    placed agreement (position := 260) (by kernel_rfl)
  simp only [operand44, NativeLookups.Input.fields, sourceFields44]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p258, p260]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup44).Contains (Verification.environment logical) ↔
      ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields44 physical logical agreement]
  exact source_semantics44 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand45.input.fields physical = sourceFields45 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p259 : physical (.BaseLayerMemory 73) = logical 259 :=
    placed agreement (position := 259) (by kernel_rfl)
  have p260 : physical (.BaseLayerWitness 152) = logical 260 :=
    placed agreement (position := 260) (by kernel_rfl)
  simp only [operand45, NativeLookups.Input.fields, sourceFields45]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p259, p260]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup45).Contains (Verification.environment logical) ↔
      ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields45 physical logical agreement]
  exact source_semantics45 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand46.input.fields physical = sourceFields46 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p261 : physical (.BaseLayerMemory 76) = logical 261 :=
    placed agreement (position := 261) (by kernel_rfl)
  have p263 : physical (.BaseLayerWitness 153) = logical 263 :=
    placed agreement (position := 263) (by kernel_rfl)
  simp only [operand46, NativeLookups.Input.fields, sourceFields46]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p261, p263]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup46).Contains (Verification.environment logical) ↔
      ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields46 physical logical agreement]
  exact source_semantics46 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand47.input.fields physical = sourceFields47 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p262 : physical (.BaseLayerMemory 77) = logical 262 :=
    placed agreement (position := 262) (by kernel_rfl)
  have p263 : physical (.BaseLayerWitness 153) = logical 263 :=
    placed agreement (position := 263) (by kernel_rfl)
  simp only [operand47, NativeLookups.Input.fields, sourceFields47]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p262, p263]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup47).Contains (Verification.environment logical) ↔
      ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields47 physical logical agreement]
  exact source_semantics47 logical


end Airbender.Compiler.WorkerConstraints.Bigint
