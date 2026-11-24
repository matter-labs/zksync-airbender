module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries018
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries019

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields224 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand224.input.fields physical = sourceFields224 logical := by
  have p544 : physical (.BaseLayerWitness 405) = logical 544 :=
    placed agreement (position := 544) (by kernel_rfl)
  have p40 : physical (.BaseLayerMemory 57) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p439 : physical (.BaseLayerWitness 300) = logical 439 :=
    placed agreement (position := 439) (by kernel_rfl)
  have p545 : physical (.BaseLayerWitness 406) = logical 545 :=
    placed agreement (position := 545) (by kernel_rfl)
  have p547 : physical (.BaseLayerWitness 408) = logical 547 :=
    placed agreement (position := 547) (by kernel_rfl)
  simp only [operand224, NativeLookups.Input.fields, sourceFields224, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p544, p40, p439, p545, p547]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement224 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup224).Contains (Verification.environment logical) ↔
      ∃ index, operand224.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields224 physical logical agreement]
  exact source_semantics224 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields225 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand225.input.fields physical = sourceFields225 logical := by
  have p548 : physical (.BaseLayerWitness 409) = logical 548 :=
    placed agreement (position := 548) (by kernel_rfl)
  have p532 : physical (.BaseLayerWitness 393) = logical 532 :=
    placed agreement (position := 532) (by kernel_rfl)
  have p549 : physical (.BaseLayerWitness 410) = logical 549 :=
    placed agreement (position := 549) (by kernel_rfl)
  simp only [operand225, NativeLookups.Input.fields, sourceFields225, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p548, p532, p549]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement225 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup225).Contains (Verification.environment logical) ↔
      ∃ index, operand225.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields225 physical logical agreement]
  exact source_semantics225 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields226 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand226.input.fields physical = sourceFields226 logical := by
  have p158 : physical (.BaseLayerWitness 19) = logical 158 :=
    placed agreement (position := 158) (by kernel_rfl)
  have p548 : physical (.BaseLayerWitness 409) = logical 548 :=
    placed agreement (position := 548) (by kernel_rfl)
  have p75 : physical (.BaseLayerMemory 110) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p532 : physical (.BaseLayerWitness 393) = logical 532 :=
    placed agreement (position := 532) (by kernel_rfl)
  have p550 : physical (.BaseLayerWitness 411) = logical 550 :=
    placed agreement (position := 550) (by kernel_rfl)
  simp only [operand226, NativeLookups.Input.fields, sourceFields226, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p158, p548, p75, p532, p550]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement226 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup226).Contains (Verification.environment logical) ↔
      ∃ index, operand226.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields226 physical logical agreement]
  exact source_semantics226 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields227 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand227.input.fields physical = sourceFields227 logical := by
  have p549 : physical (.BaseLayerWitness 410) = logical 549 :=
    placed agreement (position := 549) (by kernel_rfl)
  have p468 : physical (.BaseLayerWitness 329) = logical 468 :=
    placed agreement (position := 468) (by kernel_rfl)
  have p551 : physical (.BaseLayerWitness 412) = logical 551 :=
    placed agreement (position := 551) (by kernel_rfl)
  have p552 : physical (.BaseLayerWitness 413) = logical 552 :=
    placed agreement (position := 552) (by kernel_rfl)
  simp only [operand227, NativeLookups.Input.fields, sourceFields227, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p549, p468, p551, p552]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement227 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup227).Contains (Verification.environment logical) ↔
      ∃ index, operand227.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields227 physical logical agreement]
  exact source_semantics227 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields228 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand228.input.fields physical = sourceFields228 logical := by
  have p550 : physical (.BaseLayerWitness 411) = logical 550 :=
    placed agreement (position := 550) (by kernel_rfl)
  have p43 : physical (.BaseLayerMemory 62) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p468 : physical (.BaseLayerWitness 329) = logical 468 :=
    placed agreement (position := 468) (by kernel_rfl)
  have p551 : physical (.BaseLayerWitness 412) = logical 551 :=
    placed agreement (position := 551) (by kernel_rfl)
  have p553 : physical (.BaseLayerWitness 414) = logical 553 :=
    placed agreement (position := 553) (by kernel_rfl)
  simp only [operand228, NativeLookups.Input.fields, sourceFields228, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p550, p43, p468, p551, p553]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement228 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup228).Contains (Verification.environment logical) ↔
      ∃ index, operand228.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields228 physical logical agreement]
  exact source_semantics228 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields229 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand229.input.fields physical = sourceFields229 logical := by
  have p554 : physical (.BaseLayerWitness 415) = logical 554 :=
    placed agreement (position := 554) (by kernel_rfl)
  have p533 : physical (.BaseLayerWitness 394) = logical 533 :=
    placed agreement (position := 533) (by kernel_rfl)
  have p555 : physical (.BaseLayerWitness 416) = logical 555 :=
    placed agreement (position := 555) (by kernel_rfl)
  simp only [operand229, NativeLookups.Input.fields, sourceFields229, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p554, p533, p555]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement229 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup229).Contains (Verification.environment logical) ↔
      ∃ index, operand229.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields229 physical logical agreement]
  exact source_semantics229 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields230 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand230.input.fields physical = sourceFields230 logical := by
  have p160 : physical (.BaseLayerWitness 21) = logical 160 :=
    placed agreement (position := 160) (by kernel_rfl)
  have p554 : physical (.BaseLayerWitness 415) = logical 554 :=
    placed agreement (position := 554) (by kernel_rfl)
  have p76 : physical (.BaseLayerMemory 111) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p533 : physical (.BaseLayerWitness 394) = logical 533 :=
    placed agreement (position := 533) (by kernel_rfl)
  have p556 : physical (.BaseLayerWitness 417) = logical 556 :=
    placed agreement (position := 556) (by kernel_rfl)
  simp only [operand230, NativeLookups.Input.fields, sourceFields230, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p160, p554, p76, p533, p556]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement230 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup230).Contains (Verification.environment logical) ↔
      ∃ index, operand230.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields230 physical logical agreement]
  exact source_semantics230 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields231 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand231.input.fields physical = sourceFields231 logical := by
  have p555 : physical (.BaseLayerWitness 416) = logical 555 :=
    placed agreement (position := 555) (by kernel_rfl)
  have p469 : physical (.BaseLayerWitness 330) = logical 469 :=
    placed agreement (position := 469) (by kernel_rfl)
  have p557 : physical (.BaseLayerWitness 418) = logical 557 :=
    placed agreement (position := 557) (by kernel_rfl)
  have p558 : physical (.BaseLayerWitness 419) = logical 558 :=
    placed agreement (position := 558) (by kernel_rfl)
  simp only [operand231, NativeLookups.Input.fields, sourceFields231, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p555, p469, p557, p558]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement231 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup231).Contains (Verification.environment logical) ↔
      ∃ index, operand231.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields231 physical logical agreement]
  exact source_semantics231 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
