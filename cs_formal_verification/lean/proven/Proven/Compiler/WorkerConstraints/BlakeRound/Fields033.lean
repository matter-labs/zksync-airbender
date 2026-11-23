module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries022

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields264 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand264.input.fields physical = sourceFields264 logical := by
  have p92 : physical (.BaseLayerMemory 135) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p501 : physical (.BaseLayerWitness 362) = logical 501 :=
    placed agreement (position := 501) (by kernel_rfl)
  have p604 : physical (.BaseLayerWitness 465) = logical 604 :=
    placed agreement (position := 604) (by kernel_rfl)
  have p605 : physical (.BaseLayerWitness 466) = logical 605 :=
    placed agreement (position := 605) (by kernel_rfl)
  have p607 : physical (.BaseLayerWitness 468) = logical 607 :=
    placed agreement (position := 607) (by kernel_rfl)
  simp only [operand264, NativeLookups.Input.fields, sourceFields264, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p92, p501, p604, p605, p607]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement264 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup264).Contains (Verification.environment logical) ↔
      ∃ index, operand264.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields264 physical logical agreement]
  exact source_semantics264 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields265 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand265.input.fields physical = sourceFields265 logical := by
  have p474 : physical (.BaseLayerWitness 335) = logical 474 :=
    placed agreement (position := 474) (by kernel_rfl)
  have p608 : physical (.BaseLayerWitness 469) = logical 608 :=
    placed agreement (position := 608) (by kernel_rfl)
  have p609 : physical (.BaseLayerWitness 470) = logical 609 :=
    placed agreement (position := 609) (by kernel_rfl)
  simp only [operand265, NativeLookups.Input.fields, sourceFields265, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p474, p608, p609]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement265 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup265).Contains (Verification.environment logical) ↔
      ∃ index, operand265.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields265 physical logical agreement]
  exact source_semantics265 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields266 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand266.input.fields physical = sourceFields266 logical := by
  have p63 : physical (.BaseLayerMemory 92) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p474 : physical (.BaseLayerWitness 335) = logical 474 :=
    placed agreement (position := 474) (by kernel_rfl)
  have p178 : physical (.BaseLayerWitness 39) = logical 178 :=
    placed agreement (position := 178) (by kernel_rfl)
  have p608 : physical (.BaseLayerWitness 469) = logical 608 :=
    placed agreement (position := 608) (by kernel_rfl)
  have p610 : physical (.BaseLayerWitness 471) = logical 610 :=
    placed agreement (position := 610) (by kernel_rfl)
  simp only [operand266, NativeLookups.Input.fields, sourceFields266, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p63, p474, p178, p608, p610]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement266 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup266).Contains (Verification.environment logical) ↔
      ∃ index, operand266.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields266 physical logical agreement]
  exact source_semantics266 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields267 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand267.input.fields physical = sourceFields267 logical := by
  have p530 : physical (.BaseLayerWitness 391) = logical 530 :=
    placed agreement (position := 530) (by kernel_rfl)
  have p609 : physical (.BaseLayerWitness 470) = logical 609 :=
    placed agreement (position := 609) (by kernel_rfl)
  have p611 : physical (.BaseLayerWitness 472) = logical 611 :=
    placed agreement (position := 611) (by kernel_rfl)
  have p612 : physical (.BaseLayerWitness 473) = logical 612 :=
    placed agreement (position := 612) (by kernel_rfl)
  simp only [operand267, NativeLookups.Input.fields, sourceFields267, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p530, p609, p611, p612]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement267 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup267).Contains (Verification.environment logical) ↔
      ∃ index, operand267.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields267 physical logical agreement]
  exact source_semantics267 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields268 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand268.input.fields physical = sourceFields268 logical := by
  have p95 : physical (.BaseLayerMemory 140) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p530 : physical (.BaseLayerWitness 391) = logical 530 :=
    placed agreement (position := 530) (by kernel_rfl)
  have p610 : physical (.BaseLayerWitness 471) = logical 610 :=
    placed agreement (position := 610) (by kernel_rfl)
  have p611 : physical (.BaseLayerWitness 472) = logical 611 :=
    placed agreement (position := 611) (by kernel_rfl)
  have p613 : physical (.BaseLayerWitness 474) = logical 613 :=
    placed agreement (position := 613) (by kernel_rfl)
  simp only [operand268, NativeLookups.Input.fields, sourceFields268, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p95, p530, p610, p611, p613]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement268 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup268).Contains (Verification.environment logical) ↔
      ∃ index, operand268.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields268 physical logical agreement]
  exact source_semantics268 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields269 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand269.input.fields physical = sourceFields269 logical := by
  have p475 : physical (.BaseLayerWitness 336) = logical 475 :=
    placed agreement (position := 475) (by kernel_rfl)
  have p614 : physical (.BaseLayerWitness 475) = logical 614 :=
    placed agreement (position := 614) (by kernel_rfl)
  have p615 : physical (.BaseLayerWitness 476) = logical 615 :=
    placed agreement (position := 615) (by kernel_rfl)
  simp only [operand269, NativeLookups.Input.fields, sourceFields269, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p475, p614, p615]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement269 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup269).Contains (Verification.environment logical) ↔
      ∃ index, operand269.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields269 physical logical agreement]
  exact source_semantics269 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields270 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand270.input.fields physical = sourceFields270 logical := by
  have p64 : physical (.BaseLayerMemory 93) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p475 : physical (.BaseLayerWitness 336) = logical 475 :=
    placed agreement (position := 475) (by kernel_rfl)
  have p180 : physical (.BaseLayerWitness 41) = logical 180 :=
    placed agreement (position := 180) (by kernel_rfl)
  have p614 : physical (.BaseLayerWitness 475) = logical 614 :=
    placed agreement (position := 614) (by kernel_rfl)
  have p616 : physical (.BaseLayerWitness 477) = logical 616 :=
    placed agreement (position := 616) (by kernel_rfl)
  simp only [operand270, NativeLookups.Input.fields, sourceFields270, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p64, p475, p180, p614, p616]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement270 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup270).Contains (Verification.environment logical) ↔
      ∃ index, operand270.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields270 physical logical agreement]
  exact source_semantics270 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields271 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand271.input.fields physical = sourceFields271 logical := by
  have p531 : physical (.BaseLayerWitness 392) = logical 531 :=
    placed agreement (position := 531) (by kernel_rfl)
  have p615 : physical (.BaseLayerWitness 476) = logical 615 :=
    placed agreement (position := 615) (by kernel_rfl)
  have p617 : physical (.BaseLayerWitness 478) = logical 617 :=
    placed agreement (position := 617) (by kernel_rfl)
  have p618 : physical (.BaseLayerWitness 479) = logical 618 :=
    placed agreement (position := 618) (by kernel_rfl)
  simp only [operand271, NativeLookups.Input.fields, sourceFields271, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p531, p615, p617, p618]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement271 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup271).Contains (Verification.environment logical) ↔
      ∃ index, operand271.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields271 physical logical agreement]
  exact source_semantics271 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
