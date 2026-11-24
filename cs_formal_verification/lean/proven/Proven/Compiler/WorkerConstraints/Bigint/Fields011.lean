module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries007

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields88 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand88.input.fields physical = sourceFields88 logical := by
  have p131 : physical (.BaseLayerWitness 72) = logical 131 :=
    placed agreement (position := 131) (by kernel_rfl)
  have p163 : physical (.BaseLayerWitness 104) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 102) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  have p193 : physical (.BaseLayerWitness 134) = logical 193 :=
    placed agreement (position := 193) (by kernel_rfl)
  simp only [operand88, NativeLookups.Input.fields, sourceFields88, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p131, p163, p161, p193]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement88 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup88).Contains (Verification.environment logical) ↔
      ∃ index, operand88.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields88 physical logical agreement]
  exact source_semantics88 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields89 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand89.input.fields physical = sourceFields89 logical := by
  have p132 : physical (.BaseLayerWitness 73) = logical 132 :=
    placed agreement (position := 132) (by kernel_rfl)
  have p164 : physical (.BaseLayerWitness 105) = logical 164 :=
    placed agreement (position := 164) (by kernel_rfl)
  have p160 : physical (.BaseLayerWitness 101) = logical 160 :=
    placed agreement (position := 160) (by kernel_rfl)
  have p192 : physical (.BaseLayerWitness 133) = logical 192 :=
    placed agreement (position := 192) (by kernel_rfl)
  simp only [operand89, NativeLookups.Input.fields, sourceFields89, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p132, p164, p160, p192]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement89 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup89).Contains (Verification.environment logical) ↔
      ∃ index, operand89.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields89 physical logical agreement]
  exact source_semantics89 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields90 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand90.input.fields physical = sourceFields90 logical := by
  have p133 : physical (.BaseLayerWitness 74) = logical 133 :=
    placed agreement (position := 133) (by kernel_rfl)
  have p165 : physical (.BaseLayerWitness 106) = logical 165 :=
    placed agreement (position := 165) (by kernel_rfl)
  simp only [operand90, NativeLookups.Input.fields, sourceFields90, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p133, p165]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement90 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup90).Contains (Verification.environment logical) ↔
      ∃ index, operand90.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields90 physical logical agreement]
  exact source_semantics90 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields91 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand91.input.fields physical = sourceFields91 logical := by
  have p134 : physical (.BaseLayerWitness 75) = logical 134 :=
    placed agreement (position := 134) (by kernel_rfl)
  have p166 : physical (.BaseLayerWitness 107) = logical 166 :=
    placed agreement (position := 166) (by kernel_rfl)
  simp only [operand91, NativeLookups.Input.fields, sourceFields91, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p134, p166]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement91 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup91).Contains (Verification.environment logical) ↔
      ∃ index, operand91.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields91 physical logical agreement]
  exact source_semantics91 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields92 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand92.input.fields physical = sourceFields92 logical := by
  have p158 : physical (.BaseLayerWitness 99) = logical 158 :=
    placed agreement (position := 158) (by kernel_rfl)
  have p190 : physical (.BaseLayerWitness 131) = logical 190 :=
    placed agreement (position := 190) (by kernel_rfl)
  simp only [operand92, NativeLookups.Input.fields, sourceFields92, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p158, p190]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement92 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup92).Contains (Verification.environment logical) ↔
      ∃ index, operand92.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields92 physical logical agreement]
  exact source_semantics92 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields93 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand93.input.fields physical = sourceFields93 logical := by
  have p159 : physical (.BaseLayerWitness 100) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p191 : physical (.BaseLayerWitness 132) = logical 191 :=
    placed agreement (position := 191) (by kernel_rfl)
  simp only [operand93, NativeLookups.Input.fields, sourceFields93, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p159, p191]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement93 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup93).Contains (Verification.environment logical) ↔
      ∃ index, operand93.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields93 physical logical agreement]
  exact source_semantics93 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields94 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand94.input.fields physical = sourceFields94 logical := by
  have p135 : physical (.BaseLayerWitness 76) = logical 135 :=
    placed agreement (position := 135) (by kernel_rfl)
  have p167 : physical (.BaseLayerWitness 108) = logical 167 :=
    placed agreement (position := 167) (by kernel_rfl)
  simp only [operand94, NativeLookups.Input.fields, sourceFields94, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p135, p167]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement94 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup94).Contains (Verification.environment logical) ↔
      ∃ index, operand94.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields94 physical logical agreement]
  exact source_semantics94 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields95 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand95.input.fields physical = sourceFields95 logical := by
  have p136 : physical (.BaseLayerWitness 77) = logical 136 :=
    placed agreement (position := 136) (by kernel_rfl)
  have p168 : physical (.BaseLayerWitness 109) = logical 168 :=
    placed agreement (position := 168) (by kernel_rfl)
  simp only [operand95, NativeLookups.Input.fields, sourceFields95, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p136, p168]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement95 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup95).Contains (Verification.environment logical) ↔
      ∃ index, operand95.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields95 physical logical agreement]
  exact source_semantics95 logical


end Airbender.Compiler.WorkerConstraints.Bigint
