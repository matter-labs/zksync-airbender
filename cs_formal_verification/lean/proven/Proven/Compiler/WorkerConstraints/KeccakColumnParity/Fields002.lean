module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p145 : physical (.BaseLayerMemory 38) = logical 145 :=
    placed agreement (position := 145) (by kernel_rfl)
  have p146 : physical (.BaseLayerWitness 83) = logical 146 :=
    placed agreement (position := 146) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p145, p146]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields16 physical logical agreement]
  exact source_semantics16 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand17.input.fields physical = sourceFields17 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p147 : physical (.BaseLayerMemory 41) = logical 147 :=
    placed agreement (position := 147) (by kernel_rfl)
  have p149 : physical (.BaseLayerWitness 84) = logical 149 :=
    placed agreement (position := 149) (by kernel_rfl)
  simp only [operand17, NativeLookups.Input.fields, sourceFields17]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p147, p149]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields17 physical logical agreement]
  exact source_semantics17 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand18.input.fields physical = sourceFields18 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p148 : physical (.BaseLayerMemory 42) = logical 148 :=
    placed agreement (position := 148) (by kernel_rfl)
  have p149 : physical (.BaseLayerWitness 84) = logical 149 :=
    placed agreement (position := 149) (by kernel_rfl)
  simp only [operand18, NativeLookups.Input.fields, sourceFields18]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p148, p149]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields18 physical logical agreement]
  exact source_semantics18 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand19.input.fields physical = sourceFields19 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p150 : physical (.BaseLayerMemory 46) = logical 150 :=
    placed agreement (position := 150) (by kernel_rfl)
  have p152 : physical (.BaseLayerWitness 85) = logical 152 :=
    placed agreement (position := 152) (by kernel_rfl)
  simp only [operand19, NativeLookups.Input.fields, sourceFields19]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p150, p152]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup19).Contains (Verification.environment logical) ↔
      ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields19 physical logical agreement]
  exact source_semantics19 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand20.input.fields physical = sourceFields20 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p151 : physical (.BaseLayerMemory 47) = logical 151 :=
    placed agreement (position := 151) (by kernel_rfl)
  have p152 : physical (.BaseLayerWitness 85) = logical 152 :=
    placed agreement (position := 152) (by kernel_rfl)
  simp only [operand20, NativeLookups.Input.fields, sourceFields20]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p151, p152]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup20).Contains (Verification.environment logical) ↔
      ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields20 physical logical agreement]
  exact source_semantics20 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand21.input.fields physical = sourceFields21 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p153 : physical (.BaseLayerMemory 50) = logical 153 :=
    placed agreement (position := 153) (by kernel_rfl)
  have p155 : physical (.BaseLayerWitness 86) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  simp only [operand21, NativeLookups.Input.fields, sourceFields21]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p153, p155]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup21).Contains (Verification.environment logical) ↔
      ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields21 physical logical agreement]
  exact source_semantics21 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand22.input.fields physical = sourceFields22 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p154 : physical (.BaseLayerMemory 51) = logical 154 :=
    placed agreement (position := 154) (by kernel_rfl)
  have p155 : physical (.BaseLayerWitness 86) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  simp only [operand22, NativeLookups.Input.fields, sourceFields22]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p154, p155]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup22).Contains (Verification.environment logical) ↔
      ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields22 physical logical agreement]
  exact source_semantics22 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand23.input.fields physical = sourceFields23 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p156 : physical (.BaseLayerMemory 55) = logical 156 :=
    placed agreement (position := 156) (by kernel_rfl)
  have p158 : physical (.BaseLayerWitness 87) = logical 158 :=
    placed agreement (position := 158) (by kernel_rfl)
  simp only [operand23, NativeLookups.Input.fields, sourceFields23]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p156, p158]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup23).Contains (Verification.environment logical) ↔
      ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields23 physical logical agreement]
  exact source_semantics23 logical


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
