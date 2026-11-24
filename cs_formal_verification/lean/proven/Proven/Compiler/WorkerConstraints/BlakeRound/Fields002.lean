module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p654 : physical (.BaseLayerMemory 41) = logical 654 :=
    placed agreement (position := 654) (by kernel_rfl)
  have p655 : physical (.BaseLayerWitness 500) = logical 655 :=
    placed agreement (position := 655) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p654, p655]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields16 physical logical agreement]
  exact source_semantics16 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand17.input.fields physical = sourceFields17 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p656 : physical (.BaseLayerMemory 46) = logical 656 :=
    placed agreement (position := 656) (by kernel_rfl)
  have p658 : physical (.BaseLayerWitness 501) = logical 658 :=
    placed agreement (position := 658) (by kernel_rfl)
  simp only [operand17, NativeLookups.Input.fields, sourceFields17]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p656, p658]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields17 physical logical agreement]
  exact source_semantics17 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand18.input.fields physical = sourceFields18 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p657 : physical (.BaseLayerMemory 47) = logical 657 :=
    placed agreement (position := 657) (by kernel_rfl)
  have p658 : physical (.BaseLayerWitness 501) = logical 658 :=
    placed agreement (position := 658) (by kernel_rfl)
  simp only [operand18, NativeLookups.Input.fields, sourceFields18]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p657, p658]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields18 physical logical agreement]
  exact source_semantics18 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand19.input.fields physical = sourceFields19 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p659 : physical (.BaseLayerMemory 52) = logical 659 :=
    placed agreement (position := 659) (by kernel_rfl)
  have p661 : physical (.BaseLayerWitness 502) = logical 661 :=
    placed agreement (position := 661) (by kernel_rfl)
  simp only [operand19, NativeLookups.Input.fields, sourceFields19]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p659, p661]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup19).Contains (Verification.environment logical) ↔
      ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields19 physical logical agreement]
  exact source_semantics19 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand20.input.fields physical = sourceFields20 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p660 : physical (.BaseLayerMemory 53) = logical 660 :=
    placed agreement (position := 660) (by kernel_rfl)
  have p661 : physical (.BaseLayerWitness 502) = logical 661 :=
    placed agreement (position := 661) (by kernel_rfl)
  simp only [operand20, NativeLookups.Input.fields, sourceFields20]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p660, p661]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup20).Contains (Verification.environment logical) ↔
      ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields20 physical logical agreement]
  exact source_semantics20 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand21.input.fields physical = sourceFields21 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p662 : physical (.BaseLayerMemory 58) = logical 662 :=
    placed agreement (position := 662) (by kernel_rfl)
  have p664 : physical (.BaseLayerWitness 503) = logical 664 :=
    placed agreement (position := 664) (by kernel_rfl)
  simp only [operand21, NativeLookups.Input.fields, sourceFields21]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p662, p664]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup21).Contains (Verification.environment logical) ↔
      ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields21 physical logical agreement]
  exact source_semantics21 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand22.input.fields physical = sourceFields22 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p663 : physical (.BaseLayerMemory 59) = logical 663 :=
    placed agreement (position := 663) (by kernel_rfl)
  have p664 : physical (.BaseLayerWitness 503) = logical 664 :=
    placed agreement (position := 664) (by kernel_rfl)
  simp only [operand22, NativeLookups.Input.fields, sourceFields22]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p663, p664]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup22).Contains (Verification.environment logical) ↔
      ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields22 physical logical agreement]
  exact source_semantics22 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand23.input.fields physical = sourceFields23 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p665 : physical (.BaseLayerMemory 64) = logical 665 :=
    placed agreement (position := 665) (by kernel_rfl)
  have p667 : physical (.BaseLayerWitness 504) = logical 667 :=
    placed agreement (position := 667) (by kernel_rfl)
  simp only [operand23, NativeLookups.Input.fields, sourceFields23]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p665, p667]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup23).Contains (Verification.environment logical) ↔
      ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields23 physical logical agreement]
  exact source_semantics23 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
