module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand40.input.fields physical = sourceFields40 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p690 : physical (.BaseLayerMemory 113) = logical 690 :=
    placed agreement (position := 690) (by kernel_rfl)
  have p691 : physical (.BaseLayerWitness 512) = logical 691 :=
    placed agreement (position := 691) (by kernel_rfl)
  simp only [operand40, NativeLookups.Input.fields, sourceFields40]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p690, p691]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup40).Contains (Verification.environment logical) ↔
      ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields40 physical logical agreement]
  exact source_semantics40 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand41.input.fields physical = sourceFields41 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p692 : physical (.BaseLayerMemory 118) = logical 692 :=
    placed agreement (position := 692) (by kernel_rfl)
  have p694 : physical (.BaseLayerWitness 513) = logical 694 :=
    placed agreement (position := 694) (by kernel_rfl)
  simp only [operand41, NativeLookups.Input.fields, sourceFields41]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p692, p694]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup41).Contains (Verification.environment logical) ↔
      ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields41 physical logical agreement]
  exact source_semantics41 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand42.input.fields physical = sourceFields42 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p693 : physical (.BaseLayerMemory 119) = logical 693 :=
    placed agreement (position := 693) (by kernel_rfl)
  have p694 : physical (.BaseLayerWitness 513) = logical 694 :=
    placed agreement (position := 694) (by kernel_rfl)
  simp only [operand42, NativeLookups.Input.fields, sourceFields42]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p693, p694]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup42).Contains (Verification.environment logical) ↔
      ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields42 physical logical agreement]
  exact source_semantics42 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand43.input.fields physical = sourceFields43 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p695 : physical (.BaseLayerMemory 124) = logical 695 :=
    placed agreement (position := 695) (by kernel_rfl)
  have p697 : physical (.BaseLayerWitness 514) = logical 697 :=
    placed agreement (position := 697) (by kernel_rfl)
  simp only [operand43, NativeLookups.Input.fields, sourceFields43]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p695, p697]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup43).Contains (Verification.environment logical) ↔
      ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields43 physical logical agreement]
  exact source_semantics43 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand44.input.fields physical = sourceFields44 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p696 : physical (.BaseLayerMemory 125) = logical 696 :=
    placed agreement (position := 696) (by kernel_rfl)
  have p697 : physical (.BaseLayerWitness 514) = logical 697 :=
    placed agreement (position := 697) (by kernel_rfl)
  simp only [operand44, NativeLookups.Input.fields, sourceFields44]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p696, p697]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup44).Contains (Verification.environment logical) ↔
      ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields44 physical logical agreement]
  exact source_semantics44 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand45.input.fields physical = sourceFields45 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p698 : physical (.BaseLayerMemory 130) = logical 698 :=
    placed agreement (position := 698) (by kernel_rfl)
  have p700 : physical (.BaseLayerWitness 515) = logical 700 :=
    placed agreement (position := 700) (by kernel_rfl)
  simp only [operand45, NativeLookups.Input.fields, sourceFields45]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p698, p700]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup45).Contains (Verification.environment logical) ↔
      ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields45 physical logical agreement]
  exact source_semantics45 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand46.input.fields physical = sourceFields46 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p699 : physical (.BaseLayerMemory 131) = logical 699 :=
    placed agreement (position := 699) (by kernel_rfl)
  have p700 : physical (.BaseLayerWitness 515) = logical 700 :=
    placed agreement (position := 700) (by kernel_rfl)
  simp only [operand46, NativeLookups.Input.fields, sourceFields46]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p699, p700]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup46).Contains (Verification.environment logical) ↔
      ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields46 physical logical agreement]
  exact source_semantics46 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand47.input.fields physical = sourceFields47 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p701 : physical (.BaseLayerMemory 136) = logical 701 :=
    placed agreement (position := 701) (by kernel_rfl)
  have p703 : physical (.BaseLayerWitness 516) = logical 703 :=
    placed agreement (position := 703) (by kernel_rfl)
  simp only [operand47, NativeLookups.Input.fields, sourceFields47]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p701, p703]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup47).Contains (Verification.environment logical) ↔
      ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields47 physical logical agreement]
  exact source_semantics47 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
