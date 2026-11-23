module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields72 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand72.input.fields physical = sourceFields72 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p738 : physical (.BaseLayerMemory 189) = logical 738 :=
    placed agreement (position := 738) (by kernel_rfl)
  have p739 : physical (.BaseLayerWitness 528) = logical 739 :=
    placed agreement (position := 739) (by kernel_rfl)
  simp only [operand72, NativeLookups.Input.fields, sourceFields72]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p738, p739]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement72 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup72).Contains (Verification.environment logical) ↔
      ∃ index, operand72.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields72 physical logical agreement]
  exact source_semantics72 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields73 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand73.input.fields physical = sourceFields73 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p740 : physical (.BaseLayerMemory 192) = logical 740 :=
    placed agreement (position := 740) (by kernel_rfl)
  have p742 : physical (.BaseLayerWitness 529) = logical 742 :=
    placed agreement (position := 742) (by kernel_rfl)
  simp only [operand73, NativeLookups.Input.fields, sourceFields73]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p740, p742]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement73 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup73).Contains (Verification.environment logical) ↔
      ∃ index, operand73.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields73 physical logical agreement]
  exact source_semantics73 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields74 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand74.input.fields physical = sourceFields74 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p741 : physical (.BaseLayerMemory 193) = logical 741 :=
    placed agreement (position := 741) (by kernel_rfl)
  have p742 : physical (.BaseLayerWitness 529) = logical 742 :=
    placed agreement (position := 742) (by kernel_rfl)
  simp only [operand74, NativeLookups.Input.fields, sourceFields74]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p741, p742]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement74 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup74).Contains (Verification.environment logical) ↔
      ∃ index, operand74.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields74 physical logical agreement]
  exact source_semantics74 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields75 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand75.input.fields physical = sourceFields75 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p743 : physical (.BaseLayerMemory 196) = logical 743 :=
    placed agreement (position := 743) (by kernel_rfl)
  have p745 : physical (.BaseLayerWitness 530) = logical 745 :=
    placed agreement (position := 745) (by kernel_rfl)
  simp only [operand75, NativeLookups.Input.fields, sourceFields75]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p743, p745]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement75 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup75).Contains (Verification.environment logical) ↔
      ∃ index, operand75.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields75 physical logical agreement]
  exact source_semantics75 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields76 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand76.input.fields physical = sourceFields76 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p744 : physical (.BaseLayerMemory 197) = logical 744 :=
    placed agreement (position := 744) (by kernel_rfl)
  have p745 : physical (.BaseLayerWitness 530) = logical 745 :=
    placed agreement (position := 745) (by kernel_rfl)
  simp only [operand76, NativeLookups.Input.fields, sourceFields76]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p744, p745]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement76 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup76).Contains (Verification.environment logical) ↔
      ∃ index, operand76.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields76 physical logical agreement]
  exact source_semantics76 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields77 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand77.input.fields physical = sourceFields77 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p746 : physical (.BaseLayerMemory 200) = logical 746 :=
    placed agreement (position := 746) (by kernel_rfl)
  have p748 : physical (.BaseLayerWitness 531) = logical 748 :=
    placed agreement (position := 748) (by kernel_rfl)
  simp only [operand77, NativeLookups.Input.fields, sourceFields77]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p746, p748]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement77 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup77).Contains (Verification.environment logical) ↔
      ∃ index, operand77.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields77 physical logical agreement]
  exact source_semantics77 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields78 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand78.input.fields physical = sourceFields78 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p747 : physical (.BaseLayerMemory 201) = logical 747 :=
    placed agreement (position := 747) (by kernel_rfl)
  have p748 : physical (.BaseLayerWitness 531) = logical 748 :=
    placed agreement (position := 748) (by kernel_rfl)
  simp only [operand78, NativeLookups.Input.fields, sourceFields78]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p747, p748]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement78 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup78).Contains (Verification.environment logical) ↔
      ∃ index, operand78.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields78 physical logical agreement]
  exact source_semantics78 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields79 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand79.input.fields physical = sourceFields79 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p749 : physical (.BaseLayerMemory 204) = logical 749 :=
    placed agreement (position := 749) (by kernel_rfl)
  have p751 : physical (.BaseLayerWitness 532) = logical 751 :=
    placed agreement (position := 751) (by kernel_rfl)
  simp only [operand79, NativeLookups.Input.fields, sourceFields79]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p749, p751]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement79 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup79).Contains (Verification.environment logical) ↔
      ∃ index, operand79.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields79 physical logical agreement]
  exact source_semantics79 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
