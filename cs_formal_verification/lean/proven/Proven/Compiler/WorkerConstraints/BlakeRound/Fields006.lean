module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand48.input.fields physical = sourceFields48 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p702 : physical (.BaseLayerMemory 137) = logical 702 :=
    placed agreement (position := 702) (by kernel_rfl)
  have p703 : physical (.BaseLayerWitness 516) = logical 703 :=
    placed agreement (position := 703) (by kernel_rfl)
  simp only [operand48, NativeLookups.Input.fields, sourceFields48]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p702, p703]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup48).Contains (Verification.environment logical) ↔
      ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields48 physical logical agreement]
  exact source_semantics48 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand49.input.fields physical = sourceFields49 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p704 : physical (.BaseLayerMemory 142) = logical 704 :=
    placed agreement (position := 704) (by kernel_rfl)
  have p706 : physical (.BaseLayerWitness 517) = logical 706 :=
    placed agreement (position := 706) (by kernel_rfl)
  simp only [operand49, NativeLookups.Input.fields, sourceFields49]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p704, p706]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup49).Contains (Verification.environment logical) ↔
      ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields49 physical logical agreement]
  exact source_semantics49 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand50.input.fields physical = sourceFields50 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p705 : physical (.BaseLayerMemory 143) = logical 705 :=
    placed agreement (position := 705) (by kernel_rfl)
  have p706 : physical (.BaseLayerWitness 517) = logical 706 :=
    placed agreement (position := 706) (by kernel_rfl)
  simp only [operand50, NativeLookups.Input.fields, sourceFields50]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p705, p706]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup50).Contains (Verification.environment logical) ↔
      ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields50 physical logical agreement]
  exact source_semantics50 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand51.input.fields physical = sourceFields51 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p707 : physical (.BaseLayerMemory 148) = logical 707 :=
    placed agreement (position := 707) (by kernel_rfl)
  have p709 : physical (.BaseLayerWitness 518) = logical 709 :=
    placed agreement (position := 709) (by kernel_rfl)
  simp only [operand51, NativeLookups.Input.fields, sourceFields51]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p707, p709]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup51).Contains (Verification.environment logical) ↔
      ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields51 physical logical agreement]
  exact source_semantics51 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields52 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand52.input.fields physical = sourceFields52 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p708 : physical (.BaseLayerMemory 149) = logical 708 :=
    placed agreement (position := 708) (by kernel_rfl)
  have p709 : physical (.BaseLayerWitness 518) = logical 709 :=
    placed agreement (position := 709) (by kernel_rfl)
  simp only [operand52, NativeLookups.Input.fields, sourceFields52]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p708, p709]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement52 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup52).Contains (Verification.environment logical) ↔
      ∃ index, operand52.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields52 physical logical agreement]
  exact source_semantics52 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields53 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand53.input.fields physical = sourceFields53 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p710 : physical (.BaseLayerMemory 152) = logical 710 :=
    placed agreement (position := 710) (by kernel_rfl)
  have p712 : physical (.BaseLayerWitness 519) = logical 712 :=
    placed agreement (position := 712) (by kernel_rfl)
  simp only [operand53, NativeLookups.Input.fields, sourceFields53]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p710, p712]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement53 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup53).Contains (Verification.environment logical) ↔
      ∃ index, operand53.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields53 physical logical agreement]
  exact source_semantics53 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields54 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand54.input.fields physical = sourceFields54 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p711 : physical (.BaseLayerMemory 153) = logical 711 :=
    placed agreement (position := 711) (by kernel_rfl)
  have p712 : physical (.BaseLayerWitness 519) = logical 712 :=
    placed agreement (position := 712) (by kernel_rfl)
  simp only [operand54, NativeLookups.Input.fields, sourceFields54]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p711, p712]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement54 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup54).Contains (Verification.environment logical) ↔
      ∃ index, operand54.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields54 physical logical agreement]
  exact source_semantics54 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields55 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand55.input.fields physical = sourceFields55 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p713 : physical (.BaseLayerMemory 156) = logical 713 :=
    placed agreement (position := 713) (by kernel_rfl)
  have p715 : physical (.BaseLayerWitness 520) = logical 715 :=
    placed agreement (position := 715) (by kernel_rfl)
  simp only [operand55, NativeLookups.Input.fields, sourceFields55]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p713, p715]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement55 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup55).Contains (Verification.environment logical) ↔
      ∃ index, operand55.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields55 physical logical agreement]
  exact source_semantics55 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
