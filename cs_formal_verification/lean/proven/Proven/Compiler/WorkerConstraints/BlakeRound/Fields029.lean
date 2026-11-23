module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries019

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields232 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand232.input.fields physical = sourceFields232 logical := by
  have p556 : physical (.BaseLayerWitness 417) = logical 556 :=
    placed agreement (position := 556) (by kernel_rfl)
  have p44 : physical (.BaseLayerMemory 63) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  have p469 : physical (.BaseLayerWitness 330) = logical 469 :=
    placed agreement (position := 469) (by kernel_rfl)
  have p557 : physical (.BaseLayerWitness 418) = logical 557 :=
    placed agreement (position := 557) (by kernel_rfl)
  have p559 : physical (.BaseLayerWitness 420) = logical 559 :=
    placed agreement (position := 559) (by kernel_rfl)
  simp only [operand232, NativeLookups.Input.fields, sourceFields232, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p556, p44, p469, p557, p559]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement232 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup232).Contains (Verification.environment logical) ↔
      ∃ index, operand232.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields232 physical logical agreement]
  exact source_semantics232 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields233 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand233.input.fields physical = sourceFields233 logical := by
  have p560 : physical (.BaseLayerWitness 421) = logical 560 :=
    placed agreement (position := 560) (by kernel_rfl)
  have p442 : physical (.BaseLayerWitness 303) = logical 442 :=
    placed agreement (position := 442) (by kernel_rfl)
  have p561 : physical (.BaseLayerWitness 422) = logical 561 :=
    placed agreement (position := 561) (by kernel_rfl)
  simp only [operand233, NativeLookups.Input.fields, sourceFields233, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p560, p442, p561]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement233 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup233).Contains (Verification.environment logical) ↔
      ∃ index, operand233.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields233 physical logical agreement]
  exact source_semantics233 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields234 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand234.input.fields physical = sourceFields234 logical := by
  have p162 : physical (.BaseLayerWitness 23) = logical 162 :=
    placed agreement (position := 162) (by kernel_rfl)
  have p560 : physical (.BaseLayerWitness 421) = logical 560 :=
    placed agreement (position := 560) (by kernel_rfl)
  have p79 : physical (.BaseLayerMemory 116) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p442 : physical (.BaseLayerWitness 303) = logical 442 :=
    placed agreement (position := 442) (by kernel_rfl)
  have p562 : physical (.BaseLayerWitness 423) = logical 562 :=
    placed agreement (position := 562) (by kernel_rfl)
  simp only [operand234, NativeLookups.Input.fields, sourceFields234, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p162, p560, p79, p442, p562]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement234 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup234).Contains (Verification.environment logical) ↔
      ∃ index, operand234.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields234 physical logical agreement]
  exact source_semantics234 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields235 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand235.input.fields physical = sourceFields235 logical := by
  have p561 : physical (.BaseLayerWitness 422) = logical 561 :=
    placed agreement (position := 561) (by kernel_rfl)
  have p498 : physical (.BaseLayerWitness 359) = logical 498 :=
    placed agreement (position := 498) (by kernel_rfl)
  have p563 : physical (.BaseLayerWitness 424) = logical 563 :=
    placed agreement (position := 563) (by kernel_rfl)
  have p564 : physical (.BaseLayerWitness 425) = logical 564 :=
    placed agreement (position := 564) (by kernel_rfl)
  simp only [operand235, NativeLookups.Input.fields, sourceFields235, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p561, p498, p563, p564]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement235 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup235).Contains (Verification.environment logical) ↔
      ∃ index, operand235.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields235 physical logical agreement]
  exact source_semantics235 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields236 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand236.input.fields physical = sourceFields236 logical := by
  have p562 : physical (.BaseLayerWitness 423) = logical 562 :=
    placed agreement (position := 562) (by kernel_rfl)
  have p47 : physical (.BaseLayerMemory 68) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p498 : physical (.BaseLayerWitness 359) = logical 498 :=
    placed agreement (position := 498) (by kernel_rfl)
  have p563 : physical (.BaseLayerWitness 424) = logical 563 :=
    placed agreement (position := 563) (by kernel_rfl)
  have p565 : physical (.BaseLayerWitness 426) = logical 565 :=
    placed agreement (position := 565) (by kernel_rfl)
  simp only [operand236, NativeLookups.Input.fields, sourceFields236, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p562, p47, p498, p563, p565]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement236 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup236).Contains (Verification.environment logical) ↔
      ∃ index, operand236.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields236 physical logical agreement]
  exact source_semantics236 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields237 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand237.input.fields physical = sourceFields237 logical := by
  have p566 : physical (.BaseLayerWitness 427) = logical 566 :=
    placed agreement (position := 566) (by kernel_rfl)
  have p443 : physical (.BaseLayerWitness 304) = logical 443 :=
    placed agreement (position := 443) (by kernel_rfl)
  have p567 : physical (.BaseLayerWitness 428) = logical 567 :=
    placed agreement (position := 567) (by kernel_rfl)
  simp only [operand237, NativeLookups.Input.fields, sourceFields237, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p566, p443, p567]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement237 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup237).Contains (Verification.environment logical) ↔
      ∃ index, operand237.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields237 physical logical agreement]
  exact source_semantics237 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields238 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand238.input.fields physical = sourceFields238 logical := by
  have p164 : physical (.BaseLayerWitness 25) = logical 164 :=
    placed agreement (position := 164) (by kernel_rfl)
  have p566 : physical (.BaseLayerWitness 427) = logical 566 :=
    placed agreement (position := 566) (by kernel_rfl)
  have p80 : physical (.BaseLayerMemory 117) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p443 : physical (.BaseLayerWitness 304) = logical 443 :=
    placed agreement (position := 443) (by kernel_rfl)
  have p568 : physical (.BaseLayerWitness 429) = logical 568 :=
    placed agreement (position := 568) (by kernel_rfl)
  simp only [operand238, NativeLookups.Input.fields, sourceFields238, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p164, p566, p80, p443, p568]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement238 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup238).Contains (Verification.environment logical) ↔
      ∃ index, operand238.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields238 physical logical agreement]
  exact source_semantics238 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields239 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand239.input.fields physical = sourceFields239 logical := by
  have p567 : physical (.BaseLayerWitness 428) = logical 567 :=
    placed agreement (position := 567) (by kernel_rfl)
  have p499 : physical (.BaseLayerWitness 360) = logical 499 :=
    placed agreement (position := 499) (by kernel_rfl)
  have p569 : physical (.BaseLayerWitness 430) = logical 569 :=
    placed agreement (position := 569) (by kernel_rfl)
  have p570 : physical (.BaseLayerWitness 431) = logical 570 :=
    placed agreement (position := 570) (by kernel_rfl)
  simp only [operand239, NativeLookups.Input.fields, sourceFields239, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p567, p499, p569, p570]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement239 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup239).Contains (Verification.environment logical) ↔
      ∃ index, operand239.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields239 physical logical agreement]
  exact source_semantics239 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
