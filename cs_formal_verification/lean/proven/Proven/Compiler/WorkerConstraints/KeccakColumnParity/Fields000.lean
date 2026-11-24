module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries000

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p0 : physical (.BaseLayerMemory 72) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  simp only [operand0, NativeLookups.Input.fields, sourceFields0]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p0]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup0).Contains (Verification.environment logical) ↔
      ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields0 physical logical agreement]
  exact source_semantics0 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p123 : physical (.BaseLayerMemory 0) = logical 123 :=
    placed agreement (position := 123) (by kernel_rfl)
  have p125 : physical (.BaseLayerWitness 76) = logical 125 :=
    placed agreement (position := 125) (by kernel_rfl)
  simp only [operand1, NativeLookups.Input.fields, sourceFields1]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p123, p125]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields1 physical logical agreement]
  exact source_semantics1 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p124 : physical (.BaseLayerMemory 1) = logical 124 :=
    placed agreement (position := 124) (by kernel_rfl)
  have p125 : physical (.BaseLayerWitness 76) = logical 125 :=
    placed agreement (position := 125) (by kernel_rfl)
  simp only [operand2, NativeLookups.Input.fields, sourceFields2]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p124, p125]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields2 physical logical agreement]
  exact source_semantics2 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p126 : physical (.BaseLayerMemory 6) = logical 126 :=
    placed agreement (position := 126) (by kernel_rfl)
  have p128 : physical (.BaseLayerWitness 77) = logical 128 :=
    placed agreement (position := 128) (by kernel_rfl)
  simp only [operand3, NativeLookups.Input.fields, sourceFields3]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p126, p128]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields3 physical logical agreement]
  exact source_semantics3 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p127 : physical (.BaseLayerMemory 7) = logical 127 :=
    placed agreement (position := 127) (by kernel_rfl)
  have p128 : physical (.BaseLayerWitness 77) = logical 128 :=
    placed agreement (position := 128) (by kernel_rfl)
  simp only [operand4, NativeLookups.Input.fields, sourceFields4]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p127, p128]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields4 physical logical agreement]
  exact source_semantics4 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p129 : physical (.BaseLayerMemory 10) = logical 129 :=
    placed agreement (position := 129) (by kernel_rfl)
  have p131 : physical (.BaseLayerWitness 78) = logical 131 :=
    placed agreement (position := 131) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p129, p131]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields5 physical logical agreement]
  exact source_semantics5 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p130 : physical (.BaseLayerMemory 11) = logical 130 :=
    placed agreement (position := 130) (by kernel_rfl)
  have p131 : physical (.BaseLayerWitness 78) = logical 131 :=
    placed agreement (position := 131) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p130, p131]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields6 physical logical agreement]
  exact source_semantics6 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p132 : physical (.BaseLayerMemory 17) = logical 132 :=
    placed agreement (position := 132) (by kernel_rfl)
  have p134 : physical (.BaseLayerWitness 79) = logical 134 :=
    placed agreement (position := 134) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p132, p134]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields7 physical logical agreement]
  exact source_semantics7 logical


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
