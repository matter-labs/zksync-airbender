module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields64 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand64.input.fields physical = sourceFields64 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p726 : physical (.BaseLayerMemory 173) = logical 726 :=
    placed agreement (position := 726) (by kernel_rfl)
  have p727 : physical (.BaseLayerWitness 524) = logical 727 :=
    placed agreement (position := 727) (by kernel_rfl)
  simp only [operand64, NativeLookups.Input.fields, sourceFields64]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p726, p727]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement64 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup64).Contains (Verification.environment logical) ↔
      ∃ index, operand64.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields64 physical logical agreement]
  exact source_semantics64 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields65 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand65.input.fields physical = sourceFields65 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p728 : physical (.BaseLayerMemory 176) = logical 728 :=
    placed agreement (position := 728) (by kernel_rfl)
  have p730 : physical (.BaseLayerWitness 525) = logical 730 :=
    placed agreement (position := 730) (by kernel_rfl)
  simp only [operand65, NativeLookups.Input.fields, sourceFields65]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p728, p730]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement65 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup65).Contains (Verification.environment logical) ↔
      ∃ index, operand65.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields65 physical logical agreement]
  exact source_semantics65 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields66 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand66.input.fields physical = sourceFields66 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p729 : physical (.BaseLayerMemory 177) = logical 729 :=
    placed agreement (position := 729) (by kernel_rfl)
  have p730 : physical (.BaseLayerWitness 525) = logical 730 :=
    placed agreement (position := 730) (by kernel_rfl)
  simp only [operand66, NativeLookups.Input.fields, sourceFields66]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p729, p730]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement66 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup66).Contains (Verification.environment logical) ↔
      ∃ index, operand66.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields66 physical logical agreement]
  exact source_semantics66 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields67 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand67.input.fields physical = sourceFields67 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p731 : physical (.BaseLayerMemory 180) = logical 731 :=
    placed agreement (position := 731) (by kernel_rfl)
  have p733 : physical (.BaseLayerWitness 526) = logical 733 :=
    placed agreement (position := 733) (by kernel_rfl)
  simp only [operand67, NativeLookups.Input.fields, sourceFields67]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p731, p733]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement67 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup67).Contains (Verification.environment logical) ↔
      ∃ index, operand67.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields67 physical logical agreement]
  exact source_semantics67 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields68 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand68.input.fields physical = sourceFields68 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p732 : physical (.BaseLayerMemory 181) = logical 732 :=
    placed agreement (position := 732) (by kernel_rfl)
  have p733 : physical (.BaseLayerWitness 526) = logical 733 :=
    placed agreement (position := 733) (by kernel_rfl)
  simp only [operand68, NativeLookups.Input.fields, sourceFields68]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p732, p733]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement68 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup68).Contains (Verification.environment logical) ↔
      ∃ index, operand68.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields68 physical logical agreement]
  exact source_semantics68 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields69 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand69.input.fields physical = sourceFields69 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p734 : physical (.BaseLayerMemory 184) = logical 734 :=
    placed agreement (position := 734) (by kernel_rfl)
  have p736 : physical (.BaseLayerWitness 527) = logical 736 :=
    placed agreement (position := 736) (by kernel_rfl)
  simp only [operand69, NativeLookups.Input.fields, sourceFields69]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p734, p736]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement69 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup69).Contains (Verification.environment logical) ↔
      ∃ index, operand69.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields69 physical logical agreement]
  exact source_semantics69 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields70 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand70.input.fields physical = sourceFields70 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p735 : physical (.BaseLayerMemory 185) = logical 735 :=
    placed agreement (position := 735) (by kernel_rfl)
  have p736 : physical (.BaseLayerWitness 527) = logical 736 :=
    placed agreement (position := 736) (by kernel_rfl)
  simp only [operand70, NativeLookups.Input.fields, sourceFields70]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p735, p736]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement70 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup70).Contains (Verification.environment logical) ↔
      ∃ index, operand70.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields70 physical logical agreement]
  exact source_semantics70 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields71 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand71.input.fields physical = sourceFields71 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p737 : physical (.BaseLayerMemory 188) = logical 737 :=
    placed agreement (position := 737) (by kernel_rfl)
  have p739 : physical (.BaseLayerWitness 528) = logical 739 :=
    placed agreement (position := 739) (by kernel_rfl)
  simp only [operand71, NativeLookups.Input.fields, sourceFields71]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p737, p739]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement71 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup71).Contains (Verification.environment logical) ↔
      ∃ index, operand71.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields71 physical logical agreement]
  exact source_semantics71 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
