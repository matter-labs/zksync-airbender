module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries000
public import Proven.Compiler.WorkerConstraints.Bigint.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p155 : physical (.BaseLayerWitness 96) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  simp only [operand8, NativeLookups.Input.fields, sourceFields8]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p155]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields8 physical logical agreement]
  exact source_semantics8 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p156 : physical (.BaseLayerWitness 97) = logical 156 :=
    placed agreement (position := 156) (by kernel_rfl)
  simp only [operand9, NativeLookups.Input.fields, sourceFields9]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p156]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields9 physical logical agreement]
  exact source_semantics9 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p157 : physical (.BaseLayerWitness 98) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  simp only [operand10, NativeLookups.Input.fields, sourceFields10]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p157]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields10 physical logical agreement]
  exact source_semantics10 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p158 : physical (.BaseLayerWitness 99) = logical 158 :=
    placed agreement (position := 158) (by kernel_rfl)
  simp only [operand11, NativeLookups.Input.fields, sourceFields11]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p158]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields11 physical logical agreement]
  exact source_semantics11 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p159 : physical (.BaseLayerWitness 100) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p159]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields12 physical logical agreement]
  exact source_semantics12 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p160 : physical (.BaseLayerWitness 101) = logical 160 :=
    placed agreement (position := 160) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p160]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields13 physical logical agreement]
  exact source_semantics13 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p161 : physical (.BaseLayerWitness 102) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p161]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields14 physical logical agreement]
  exact source_semantics14 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p0 : physical (.BaseLayerMemory 94) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  simp only [operand15, NativeLookups.Input.fields, sourceFields15]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p0]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields15 physical logical agreement]
  exact source_semantics15 logical


end Airbender.Compiler.WorkerConstraints.Bigint
