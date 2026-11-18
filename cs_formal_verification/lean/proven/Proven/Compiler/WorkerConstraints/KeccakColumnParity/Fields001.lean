module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries000
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p133 : physical (.BaseLayerMemory 18) = logical 133 :=
    placed agreement (position := 133) (by kernel_rfl)
  have p134 : physical (.BaseLayerWitness 79) = logical 134 :=
    placed agreement (position := 134) (by kernel_rfl)
  simp only [operand8, NativeLookups.Input.fields, sourceFields8]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p133, p134]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields8 physical logical agreement]
  exact source_semantics8 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p135 : physical (.BaseLayerMemory 23) = logical 135 :=
    placed agreement (position := 135) (by kernel_rfl)
  have p137 : physical (.BaseLayerWitness 80) = logical 137 :=
    placed agreement (position := 137) (by kernel_rfl)
  simp only [operand9, NativeLookups.Input.fields, sourceFields9]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p135, p137]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields9 physical logical agreement]
  exact source_semantics9 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p136 : physical (.BaseLayerMemory 24) = logical 136 :=
    placed agreement (position := 136) (by kernel_rfl)
  have p137 : physical (.BaseLayerWitness 80) = logical 137 :=
    placed agreement (position := 137) (by kernel_rfl)
  simp only [operand10, NativeLookups.Input.fields, sourceFields10]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p136, p137]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields10 physical logical agreement]
  exact source_semantics10 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p138 : physical (.BaseLayerMemory 28) = logical 138 :=
    placed agreement (position := 138) (by kernel_rfl)
  have p140 : physical (.BaseLayerWitness 81) = logical 140 :=
    placed agreement (position := 140) (by kernel_rfl)
  simp only [operand11, NativeLookups.Input.fields, sourceFields11]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p138, p140]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields11 physical logical agreement]
  exact source_semantics11 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p139 : physical (.BaseLayerMemory 29) = logical 139 :=
    placed agreement (position := 139) (by kernel_rfl)
  have p140 : physical (.BaseLayerWitness 81) = logical 140 :=
    placed agreement (position := 140) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p139, p140]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields12 physical logical agreement]
  exact source_semantics12 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p141 : physical (.BaseLayerMemory 32) = logical 141 :=
    placed agreement (position := 141) (by kernel_rfl)
  have p143 : physical (.BaseLayerWitness 82) = logical 143 :=
    placed agreement (position := 143) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p141, p143]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields13 physical logical agreement]
  exact source_semantics13 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p142 : physical (.BaseLayerMemory 33) = logical 142 :=
    placed agreement (position := 142) (by kernel_rfl)
  have p143 : physical (.BaseLayerWitness 82) = logical 143 :=
    placed agreement (position := 143) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p142, p143]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields14 physical logical agreement]
  exact source_semantics14 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p144 : physical (.BaseLayerMemory 37) = logical 144 :=
    placed agreement (position := 144) (by kernel_rfl)
  have p146 : physical (.BaseLayerWitness 83) = logical 146 :=
    placed agreement (position := 146) (by kernel_rfl)
  simp only [operand15, NativeLookups.Input.fields, sourceFields15]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p144, p146]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields15 physical logical agreement]
  exact source_semantics15 logical


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
