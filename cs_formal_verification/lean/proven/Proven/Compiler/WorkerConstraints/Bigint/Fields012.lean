module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries008

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields96 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand96.input.fields physical = sourceFields96 logical := by
  have p137 : physical (.BaseLayerWitness 78) = logical 137 :=
    placed agreement (position := 137) (by kernel_rfl)
  have p169 : physical (.BaseLayerWitness 110) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  simp only [operand96, NativeLookups.Input.fields, sourceFields96, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p137, p169]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement96 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup96).Contains (Verification.environment logical) ↔
      ∃ index, operand96.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields96 physical logical agreement]
  exact source_semantics96 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields97 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand97.input.fields physical = sourceFields97 logical := by
  have p138 : physical (.BaseLayerWitness 79) = logical 138 :=
    placed agreement (position := 138) (by kernel_rfl)
  have p170 : physical (.BaseLayerWitness 111) = logical 170 :=
    placed agreement (position := 170) (by kernel_rfl)
  simp only [operand97, NativeLookups.Input.fields, sourceFields97, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p138, p170]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement97 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup97).Contains (Verification.environment logical) ↔
      ∃ index, operand97.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields97 physical logical agreement]
  exact source_semantics97 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields98 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand98.input.fields physical = sourceFields98 logical := by
  have p154 : physical (.BaseLayerWitness 95) = logical 154 :=
    placed agreement (position := 154) (by kernel_rfl)
  have p186 : physical (.BaseLayerWitness 127) = logical 186 :=
    placed agreement (position := 186) (by kernel_rfl)
  simp only [operand98, NativeLookups.Input.fields, sourceFields98, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p154, p186]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement98 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup98).Contains (Verification.environment logical) ↔
      ∃ index, operand98.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields98 physical logical agreement]
  exact source_semantics98 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields99 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand99.input.fields physical = sourceFields99 logical := by
  have p155 : physical (.BaseLayerWitness 96) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  have p187 : physical (.BaseLayerWitness 128) = logical 187 :=
    placed agreement (position := 187) (by kernel_rfl)
  simp only [operand99, NativeLookups.Input.fields, sourceFields99, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p155, p187]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement99 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup99).Contains (Verification.environment logical) ↔
      ∃ index, operand99.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields99 physical logical agreement]
  exact source_semantics99 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields100 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand100.input.fields physical = sourceFields100 logical := by
  have p156 : physical (.BaseLayerWitness 97) = logical 156 :=
    placed agreement (position := 156) (by kernel_rfl)
  have p188 : physical (.BaseLayerWitness 129) = logical 188 :=
    placed agreement (position := 188) (by kernel_rfl)
  simp only [operand100, NativeLookups.Input.fields, sourceFields100, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p156, p188]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement100 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup100).Contains (Verification.environment logical) ↔
      ∃ index, operand100.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields100 physical logical agreement]
  exact source_semantics100 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields101 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand101.input.fields physical = sourceFields101 logical := by
  have p157 : physical (.BaseLayerWitness 98) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p189 : physical (.BaseLayerWitness 130) = logical 189 :=
    placed agreement (position := 189) (by kernel_rfl)
  simp only [operand101, NativeLookups.Input.fields, sourceFields101, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p157, p189]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement101 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup101).Contains (Verification.environment logical) ↔
      ∃ index, operand101.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields101 physical logical agreement]
  exact source_semantics101 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields102 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand102.input.fields physical = sourceFields102 logical := by
  have p139 : physical (.BaseLayerWitness 80) = logical 139 :=
    placed agreement (position := 139) (by kernel_rfl)
  have p171 : physical (.BaseLayerWitness 112) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  simp only [operand102, NativeLookups.Input.fields, sourceFields102, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p139, p171]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement102 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup102).Contains (Verification.environment logical) ↔
      ∃ index, operand102.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields102 physical logical agreement]
  exact source_semantics102 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields103 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand103.input.fields physical = sourceFields103 logical := by
  have p140 : physical (.BaseLayerWitness 81) = logical 140 :=
    placed agreement (position := 140) (by kernel_rfl)
  have p172 : physical (.BaseLayerWitness 113) = logical 172 :=
    placed agreement (position := 172) (by kernel_rfl)
  simp only [operand103, NativeLookups.Input.fields, sourceFields103, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p140, p172]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement103 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup103).Contains (Verification.environment logical) ↔
      ∃ index, operand103.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields103 physical logical agreement]
  exact source_semantics103 logical


end Airbender.Compiler.WorkerConstraints.Bigint
