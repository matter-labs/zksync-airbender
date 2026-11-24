module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries002
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand32.input.fields physical = sourceFields32 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p678 : physical (.BaseLayerMemory 89) = logical 678 :=
    placed agreement (position := 678) (by kernel_rfl)
  have p679 : physical (.BaseLayerWitness 508) = logical 679 :=
    placed agreement (position := 679) (by kernel_rfl)
  simp only [operand32, NativeLookups.Input.fields, sourceFields32]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p678, p679]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields32 physical logical agreement]
  exact source_semantics32 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand33.input.fields physical = sourceFields33 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p680 : physical (.BaseLayerMemory 94) = logical 680 :=
    placed agreement (position := 680) (by kernel_rfl)
  have p682 : physical (.BaseLayerWitness 509) = logical 682 :=
    placed agreement (position := 682) (by kernel_rfl)
  simp only [operand33, NativeLookups.Input.fields, sourceFields33]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p680, p682]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields33 physical logical agreement]
  exact source_semantics33 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand34.input.fields physical = sourceFields34 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p681 : physical (.BaseLayerMemory 95) = logical 681 :=
    placed agreement (position := 681) (by kernel_rfl)
  have p682 : physical (.BaseLayerWitness 509) = logical 682 :=
    placed agreement (position := 682) (by kernel_rfl)
  simp only [operand34, NativeLookups.Input.fields, sourceFields34]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p681, p682]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields34 physical logical agreement]
  exact source_semantics34 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand35.input.fields physical = sourceFields35 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p683 : physical (.BaseLayerMemory 100) = logical 683 :=
    placed agreement (position := 683) (by kernel_rfl)
  have p685 : physical (.BaseLayerWitness 510) = logical 685 :=
    placed agreement (position := 685) (by kernel_rfl)
  simp only [operand35, NativeLookups.Input.fields, sourceFields35]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p683, p685]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields35 physical logical agreement]
  exact source_semantics35 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand36.input.fields physical = sourceFields36 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p684 : physical (.BaseLayerMemory 101) = logical 684 :=
    placed agreement (position := 684) (by kernel_rfl)
  have p685 : physical (.BaseLayerWitness 510) = logical 685 :=
    placed agreement (position := 685) (by kernel_rfl)
  simp only [operand36, NativeLookups.Input.fields, sourceFields36]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p684, p685]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields36 physical logical agreement]
  exact source_semantics36 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand37.input.fields physical = sourceFields37 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p686 : physical (.BaseLayerMemory 106) = logical 686 :=
    placed agreement (position := 686) (by kernel_rfl)
  have p688 : physical (.BaseLayerWitness 511) = logical 688 :=
    placed agreement (position := 688) (by kernel_rfl)
  simp only [operand37, NativeLookups.Input.fields, sourceFields37]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p686, p688]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields37 physical logical agreement]
  exact source_semantics37 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand38.input.fields physical = sourceFields38 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p687 : physical (.BaseLayerMemory 107) = logical 687 :=
    placed agreement (position := 687) (by kernel_rfl)
  have p688 : physical (.BaseLayerWitness 511) = logical 688 :=
    placed agreement (position := 688) (by kernel_rfl)
  simp only [operand38, NativeLookups.Input.fields, sourceFields38]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p687, p688]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields38 physical logical agreement]
  exact source_semantics38 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand39.input.fields physical = sourceFields39 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p689 : physical (.BaseLayerMemory 112) = logical 689 :=
    placed agreement (position := 689) (by kernel_rfl)
  have p691 : physical (.BaseLayerWitness 512) = logical 691 :=
    placed agreement (position := 691) (by kernel_rfl)
  simp only [operand39, NativeLookups.Input.fields, sourceFields39]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p689, p691]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields39 physical logical agreement]
  exact source_semantics39 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
