module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand24.input.fields physical = sourceFields24 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p666 : physical (.BaseLayerMemory 65) = logical 666 :=
    placed agreement (position := 666) (by kernel_rfl)
  have p667 : physical (.BaseLayerWitness 504) = logical 667 :=
    placed agreement (position := 667) (by kernel_rfl)
  simp only [operand24, NativeLookups.Input.fields, sourceFields24]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p666, p667]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields24 physical logical agreement]
  exact source_semantics24 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand25.input.fields physical = sourceFields25 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p668 : physical (.BaseLayerMemory 70) = logical 668 :=
    placed agreement (position := 668) (by kernel_rfl)
  have p670 : physical (.BaseLayerWitness 505) = logical 670 :=
    placed agreement (position := 670) (by kernel_rfl)
  simp only [operand25, NativeLookups.Input.fields, sourceFields25]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p668, p670]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields25 physical logical agreement]
  exact source_semantics25 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand26.input.fields physical = sourceFields26 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p669 : physical (.BaseLayerMemory 71) = logical 669 :=
    placed agreement (position := 669) (by kernel_rfl)
  have p670 : physical (.BaseLayerWitness 505) = logical 670 :=
    placed agreement (position := 670) (by kernel_rfl)
  simp only [operand26, NativeLookups.Input.fields, sourceFields26]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p669, p670]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields26 physical logical agreement]
  exact source_semantics26 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand27.input.fields physical = sourceFields27 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p671 : physical (.BaseLayerMemory 76) = logical 671 :=
    placed agreement (position := 671) (by kernel_rfl)
  have p673 : physical (.BaseLayerWitness 506) = logical 673 :=
    placed agreement (position := 673) (by kernel_rfl)
  simp only [operand27, NativeLookups.Input.fields, sourceFields27]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p671, p673]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields27 physical logical agreement]
  exact source_semantics27 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand28.input.fields physical = sourceFields28 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p672 : physical (.BaseLayerMemory 77) = logical 672 :=
    placed agreement (position := 672) (by kernel_rfl)
  have p673 : physical (.BaseLayerWitness 506) = logical 673 :=
    placed agreement (position := 673) (by kernel_rfl)
  simp only [operand28, NativeLookups.Input.fields, sourceFields28]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p672, p673]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields28 physical logical agreement]
  exact source_semantics28 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand29.input.fields physical = sourceFields29 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p674 : physical (.BaseLayerMemory 82) = logical 674 :=
    placed agreement (position := 674) (by kernel_rfl)
  have p676 : physical (.BaseLayerWitness 507) = logical 676 :=
    placed agreement (position := 676) (by kernel_rfl)
  simp only [operand29, NativeLookups.Input.fields, sourceFields29]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p674, p676]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields29 physical logical agreement]
  exact source_semantics29 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand30.input.fields physical = sourceFields30 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p675 : physical (.BaseLayerMemory 83) = logical 675 :=
    placed agreement (position := 675) (by kernel_rfl)
  have p676 : physical (.BaseLayerWitness 507) = logical 676 :=
    placed agreement (position := 676) (by kernel_rfl)
  simp only [operand30, NativeLookups.Input.fields, sourceFields30]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p675, p676]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields30 physical logical agreement]
  exact source_semantics30 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand31.input.fields physical = sourceFields31 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p677 : physical (.BaseLayerMemory 88) = logical 677 :=
    placed agreement (position := 677) (by kernel_rfl)
  have p679 : physical (.BaseLayerWitness 508) = logical 679 :=
    placed agreement (position := 679) (by kernel_rfl)
  simp only [operand31, NativeLookups.Input.fields, sourceFields31]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p677, p679]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields31 physical logical agreement]
  exact source_semantics31 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
