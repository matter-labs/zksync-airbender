module
public import Proven.Compiler.WorkerConstraints.BlakeG.Queries000
public import Proven.Compiler.WorkerConstraints.BlakeG.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p2 : physical (.BaseLayerMemory 54) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p93 : physical (.BaseLayerMemory 19) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  have p94 : physical (.BaseLayerWitness 49) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  simp only [operand8, NativeLookups.Input.fields, sourceFields8]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p93, p94]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields8 physical logical agreement]
  exact source_semantics8 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p1 : physical (.BaseLayerMemory 53) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p95 : physical (.BaseLayerMemory 25) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p97 : physical (.BaseLayerWitness 50) = logical 97 :=
    placed agreement (position := 97) (by kernel_rfl)
  simp only [operand9, NativeLookups.Input.fields, sourceFields9]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p95, p97]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields9 physical logical agreement]
  exact source_semantics9 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p2 : physical (.BaseLayerMemory 54) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p96 : physical (.BaseLayerMemory 26) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p97 : physical (.BaseLayerWitness 50) = logical 97 :=
    placed agreement (position := 97) (by kernel_rfl)
  simp only [operand10, NativeLookups.Input.fields, sourceFields10]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p96, p97]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields10 physical logical agreement]
  exact source_semantics10 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p1 : physical (.BaseLayerMemory 53) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p98 : physical (.BaseLayerMemory 32) = logical 98 :=
    placed agreement (position := 98) (by kernel_rfl)
  have p100 : physical (.BaseLayerWitness 51) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  simp only [operand11, NativeLookups.Input.fields, sourceFields11]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p98, p100]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields11 physical logical agreement]
  exact source_semantics11 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p2 : physical (.BaseLayerMemory 54) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p99 : physical (.BaseLayerMemory 33) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p100 : physical (.BaseLayerWitness 51) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p99, p100]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields12 physical logical agreement]
  exact source_semantics12 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p1 : physical (.BaseLayerMemory 53) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p101 : physical (.BaseLayerMemory 36) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  have p103 : physical (.BaseLayerWitness 52) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p101, p103]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields13 physical logical agreement]
  exact source_semantics13 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p2 : physical (.BaseLayerMemory 54) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p102 : physical (.BaseLayerMemory 37) = logical 102 :=
    placed agreement (position := 102) (by kernel_rfl)
  have p103 : physical (.BaseLayerWitness 52) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p102, p103]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields14 physical logical agreement]
  exact source_semantics14 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p1 : physical (.BaseLayerMemory 53) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p104 : physical (.BaseLayerMemory 41) = logical 104 :=
    placed agreement (position := 104) (by kernel_rfl)
  have p106 : physical (.BaseLayerWitness 53) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  simp only [operand15, NativeLookups.Input.fields, sourceFields15]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p104, p106]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  rw [fields15 physical logical agreement]
  exact source_semantics15 logical


end Airbender.Compiler.WorkerConstraints.BlakeG
