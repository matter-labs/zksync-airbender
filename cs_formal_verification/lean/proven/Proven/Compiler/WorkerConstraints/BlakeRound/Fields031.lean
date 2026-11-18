module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries020
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries021

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields248 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand248.input.fields physical = sourceFields248 logical := by
  have p580 : physical (.BaseLayerWitness 441) = logical 580 :=
    placed agreement (position := 580) (by kernel_rfl)
  have p52 : physical (.BaseLayerMemory 75) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p529 : physical (.BaseLayerWitness 390) = logical 529 :=
    placed agreement (position := 529) (by kernel_rfl)
  have p581 : physical (.BaseLayerWitness 442) = logical 581 :=
    placed agreement (position := 581) (by kernel_rfl)
  have p583 : physical (.BaseLayerWitness 444) = logical 583 :=
    placed agreement (position := 583) (by kernel_rfl)
  simp only [operand248, NativeLookups.Input.fields, sourceFields248, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p580, p52, p529, p581, p583]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement248 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup248).Contains (Verification.environment logical) ↔
      ∃ index, operand248.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields248 physical logical agreement]
  exact source_semantics248 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields249 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand249.input.fields physical = sourceFields249 logical := by
  have p534 : physical (.BaseLayerWitness 395) = logical 534 :=
    placed agreement (position := 534) (by kernel_rfl)
  have p584 : physical (.BaseLayerWitness 445) = logical 584 :=
    placed agreement (position := 584) (by kernel_rfl)
  have p585 : physical (.BaseLayerWitness 446) = logical 585 :=
    placed agreement (position := 585) (by kernel_rfl)
  simp only [operand249, NativeLookups.Input.fields, sourceFields249, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p534, p584, p585]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement249 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup249).Contains (Verification.environment logical) ↔
      ∃ index, operand249.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields249 physical logical agreement]
  exact source_semantics249 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields250 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand250.input.fields physical = sourceFields250 logical := by
  have p55 : physical (.BaseLayerMemory 80) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  have p534 : physical (.BaseLayerWitness 395) = logical 534 :=
    placed agreement (position := 534) (by kernel_rfl)
  have p170 : physical (.BaseLayerWitness 31) = logical 170 :=
    placed agreement (position := 170) (by kernel_rfl)
  have p584 : physical (.BaseLayerWitness 445) = logical 584 :=
    placed agreement (position := 584) (by kernel_rfl)
  have p586 : physical (.BaseLayerWitness 447) = logical 586 :=
    placed agreement (position := 586) (by kernel_rfl)
  simp only [operand250, NativeLookups.Input.fields, sourceFields250, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p55, p534, p170, p584, p586]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement250 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup250).Contains (Verification.environment logical) ↔
      ∃ index, operand250.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields250 physical logical agreement]
  exact source_semantics250 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields251 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand251.input.fields physical = sourceFields251 logical := by
  have p470 : physical (.BaseLayerWitness 331) = logical 470 :=
    placed agreement (position := 470) (by kernel_rfl)
  have p585 : physical (.BaseLayerWitness 446) = logical 585 :=
    placed agreement (position := 585) (by kernel_rfl)
  have p587 : physical (.BaseLayerWitness 448) = logical 587 :=
    placed agreement (position := 587) (by kernel_rfl)
  have p588 : physical (.BaseLayerWitness 449) = logical 588 :=
    placed agreement (position := 588) (by kernel_rfl)
  simp only [operand251, NativeLookups.Input.fields, sourceFields251, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p470, p585, p587, p588]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement251 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup251).Contains (Verification.environment logical) ↔
      ∃ index, operand251.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields251 physical logical agreement]
  exact source_semantics251 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields252 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand252.input.fields physical = sourceFields252 logical := by
  have p87 : physical (.BaseLayerMemory 128) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p470 : physical (.BaseLayerWitness 331) = logical 470 :=
    placed agreement (position := 470) (by kernel_rfl)
  have p586 : physical (.BaseLayerWitness 447) = logical 586 :=
    placed agreement (position := 586) (by kernel_rfl)
  have p587 : physical (.BaseLayerWitness 448) = logical 587 :=
    placed agreement (position := 587) (by kernel_rfl)
  have p589 : physical (.BaseLayerWitness 450) = logical 589 :=
    placed agreement (position := 589) (by kernel_rfl)
  simp only [operand252, NativeLookups.Input.fields, sourceFields252, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p87, p470, p586, p587, p589]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement252 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup252).Contains (Verification.environment logical) ↔
      ∃ index, operand252.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields252 physical logical agreement]
  exact source_semantics252 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields253 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand253.input.fields physical = sourceFields253 logical := by
  have p535 : physical (.BaseLayerWitness 396) = logical 535 :=
    placed agreement (position := 535) (by kernel_rfl)
  have p590 : physical (.BaseLayerWitness 451) = logical 590 :=
    placed agreement (position := 590) (by kernel_rfl)
  have p591 : physical (.BaseLayerWitness 452) = logical 591 :=
    placed agreement (position := 591) (by kernel_rfl)
  simp only [operand253, NativeLookups.Input.fields, sourceFields253, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p535, p590, p591]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement253 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup253).Contains (Verification.environment logical) ↔
      ∃ index, operand253.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields253 physical logical agreement]
  exact source_semantics253 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields254 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand254.input.fields physical = sourceFields254 logical := by
  have p56 : physical (.BaseLayerMemory 81) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p535 : physical (.BaseLayerWitness 396) = logical 535 :=
    placed agreement (position := 535) (by kernel_rfl)
  have p172 : physical (.BaseLayerWitness 33) = logical 172 :=
    placed agreement (position := 172) (by kernel_rfl)
  have p590 : physical (.BaseLayerWitness 451) = logical 590 :=
    placed agreement (position := 590) (by kernel_rfl)
  have p592 : physical (.BaseLayerWitness 453) = logical 592 :=
    placed agreement (position := 592) (by kernel_rfl)
  simp only [operand254, NativeLookups.Input.fields, sourceFields254, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p56, p535, p172, p590, p592]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement254 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup254).Contains (Verification.environment logical) ↔
      ∃ index, operand254.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields254 physical logical agreement]
  exact source_semantics254 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields255 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand255.input.fields physical = sourceFields255 logical := by
  have p471 : physical (.BaseLayerWitness 332) = logical 471 :=
    placed agreement (position := 471) (by kernel_rfl)
  have p591 : physical (.BaseLayerWitness 452) = logical 591 :=
    placed agreement (position := 591) (by kernel_rfl)
  have p593 : physical (.BaseLayerWitness 454) = logical 593 :=
    placed agreement (position := 593) (by kernel_rfl)
  have p594 : physical (.BaseLayerWitness 455) = logical 594 :=
    placed agreement (position := 594) (by kernel_rfl)
  simp only [operand255, NativeLookups.Input.fields, sourceFields255, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p471, p591, p593, p594]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement255 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup255).Contains (Verification.environment logical) ↔
      ∃ index, operand255.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields255 physical logical agreement]
  exact source_semantics255 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
