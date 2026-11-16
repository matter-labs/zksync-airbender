module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries000

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p0 : physical (.BaseLayerMemory 222) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  simp only [operand0, NativeLookups.Input.fields, sourceFields0]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p0]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup0).Contains (Verification.environment logical) ↔
      ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields0 physical logical agreement]
  exact source_semantics0 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p632 : physical (.BaseLayerMemory 0) = logical 632 :=
    placed agreement (position := 632) (by kernel_rfl)
  have p634 : physical (.BaseLayerWitness 493) = logical 634 :=
    placed agreement (position := 634) (by kernel_rfl)
  simp only [operand1, NativeLookups.Input.fields, sourceFields1]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p632, p634]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields1 physical logical agreement]
  exact source_semantics1 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p633 : physical (.BaseLayerMemory 1) = logical 633 :=
    placed agreement (position := 633) (by kernel_rfl)
  have p634 : physical (.BaseLayerWitness 493) = logical 634 :=
    placed agreement (position := 634) (by kernel_rfl)
  simp only [operand2, NativeLookups.Input.fields, sourceFields2]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p633, p634]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields2 physical logical agreement]
  exact source_semantics2 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p635 : physical (.BaseLayerMemory 4) = logical 635 :=
    placed agreement (position := 635) (by kernel_rfl)
  have p637 : physical (.BaseLayerWitness 494) = logical 637 :=
    placed agreement (position := 637) (by kernel_rfl)
  simp only [operand3, NativeLookups.Input.fields, sourceFields3]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p635, p637]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields3 physical logical agreement]
  exact source_semantics3 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p636 : physical (.BaseLayerMemory 5) = logical 636 :=
    placed agreement (position := 636) (by kernel_rfl)
  have p637 : physical (.BaseLayerWitness 494) = logical 637 :=
    placed agreement (position := 637) (by kernel_rfl)
  simp only [operand4, NativeLookups.Input.fields, sourceFields4]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p636, p637]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields4 physical logical agreement]
  exact source_semantics4 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p638 : physical (.BaseLayerMemory 10) = logical 638 :=
    placed agreement (position := 638) (by kernel_rfl)
  have p640 : physical (.BaseLayerWitness 495) = logical 640 :=
    placed agreement (position := 640) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p638, p640]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields5 physical logical agreement]
  exact source_semantics5 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p639 : physical (.BaseLayerMemory 11) = logical 639 :=
    placed agreement (position := 639) (by kernel_rfl)
  have p640 : physical (.BaseLayerWitness 495) = logical 640 :=
    placed agreement (position := 640) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p639, p640]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields6 physical logical agreement]
  exact source_semantics6 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p641 : physical (.BaseLayerMemory 16) = logical 641 :=
    placed agreement (position := 641) (by kernel_rfl)
  have p643 : physical (.BaseLayerWitness 496) = logical 643 :=
    placed agreement (position := 643) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p641, p643]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields7 physical logical agreement]
  exact source_semantics7 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
