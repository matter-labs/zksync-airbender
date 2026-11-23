module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries020

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields240 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand240.input.fields physical = sourceFields240 logical := by
  have p568 : physical (.BaseLayerWitness 429) = logical 568 :=
    placed agreement (position := 568) (by kernel_rfl)
  have p48 : physical (.BaseLayerMemory 69) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p499 : physical (.BaseLayerWitness 360) = logical 499 :=
    placed agreement (position := 499) (by kernel_rfl)
  have p569 : physical (.BaseLayerWitness 430) = logical 569 :=
    placed agreement (position := 569) (by kernel_rfl)
  have p571 : physical (.BaseLayerWitness 432) = logical 571 :=
    placed agreement (position := 571) (by kernel_rfl)
  simp only [operand240, NativeLookups.Input.fields, sourceFields240, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p568, p48, p499, p569, p571]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement240 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup240).Contains (Verification.environment logical) ↔
      ∃ index, operand240.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields240 physical logical agreement]
  exact source_semantics240 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields241 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand241.input.fields physical = sourceFields241 logical := by
  have p572 : physical (.BaseLayerWitness 433) = logical 572 :=
    placed agreement (position := 572) (by kernel_rfl)
  have p472 : physical (.BaseLayerWitness 333) = logical 472 :=
    placed agreement (position := 472) (by kernel_rfl)
  have p573 : physical (.BaseLayerWitness 434) = logical 573 :=
    placed agreement (position := 573) (by kernel_rfl)
  simp only [operand241, NativeLookups.Input.fields, sourceFields241, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p572, p472, p573]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement241 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup241).Contains (Verification.environment logical) ↔
      ∃ index, operand241.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields241 physical logical agreement]
  exact source_semantics241 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields242 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand242.input.fields physical = sourceFields242 logical := by
  have p166 : physical (.BaseLayerWitness 27) = logical 166 :=
    placed agreement (position := 166) (by kernel_rfl)
  have p572 : physical (.BaseLayerWitness 433) = logical 572 :=
    placed agreement (position := 572) (by kernel_rfl)
  have p83 : physical (.BaseLayerMemory 122) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p472 : physical (.BaseLayerWitness 333) = logical 472 :=
    placed agreement (position := 472) (by kernel_rfl)
  have p574 : physical (.BaseLayerWitness 435) = logical 574 :=
    placed agreement (position := 574) (by kernel_rfl)
  simp only [operand242, NativeLookups.Input.fields, sourceFields242, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p166, p572, p83, p472, p574]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement242 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup242).Contains (Verification.environment logical) ↔
      ∃ index, operand242.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields242 physical logical agreement]
  exact source_semantics242 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields243 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand243.input.fields physical = sourceFields243 logical := by
  have p573 : physical (.BaseLayerWitness 434) = logical 573 :=
    placed agreement (position := 573) (by kernel_rfl)
  have p528 : physical (.BaseLayerWitness 389) = logical 528 :=
    placed agreement (position := 528) (by kernel_rfl)
  have p575 : physical (.BaseLayerWitness 436) = logical 575 :=
    placed agreement (position := 575) (by kernel_rfl)
  have p576 : physical (.BaseLayerWitness 437) = logical 576 :=
    placed agreement (position := 576) (by kernel_rfl)
  simp only [operand243, NativeLookups.Input.fields, sourceFields243, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p573, p528, p575, p576]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement243 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup243).Contains (Verification.environment logical) ↔
      ∃ index, operand243.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields243 physical logical agreement]
  exact source_semantics243 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields244 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand244.input.fields physical = sourceFields244 logical := by
  have p574 : physical (.BaseLayerWitness 435) = logical 574 :=
    placed agreement (position := 574) (by kernel_rfl)
  have p51 : physical (.BaseLayerMemory 74) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p528 : physical (.BaseLayerWitness 389) = logical 528 :=
    placed agreement (position := 528) (by kernel_rfl)
  have p575 : physical (.BaseLayerWitness 436) = logical 575 :=
    placed agreement (position := 575) (by kernel_rfl)
  have p577 : physical (.BaseLayerWitness 438) = logical 577 :=
    placed agreement (position := 577) (by kernel_rfl)
  simp only [operand244, NativeLookups.Input.fields, sourceFields244, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p574, p51, p528, p575, p577]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement244 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup244).Contains (Verification.environment logical) ↔
      ∃ index, operand244.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields244 physical logical agreement]
  exact source_semantics244 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields245 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand245.input.fields physical = sourceFields245 logical := by
  have p578 : physical (.BaseLayerWitness 439) = logical 578 :=
    placed agreement (position := 578) (by kernel_rfl)
  have p473 : physical (.BaseLayerWitness 334) = logical 473 :=
    placed agreement (position := 473) (by kernel_rfl)
  have p579 : physical (.BaseLayerWitness 440) = logical 579 :=
    placed agreement (position := 579) (by kernel_rfl)
  simp only [operand245, NativeLookups.Input.fields, sourceFields245, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p578, p473, p579]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement245 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup245).Contains (Verification.environment logical) ↔
      ∃ index, operand245.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields245 physical logical agreement]
  exact source_semantics245 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields246 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand246.input.fields physical = sourceFields246 logical := by
  have p168 : physical (.BaseLayerWitness 29) = logical 168 :=
    placed agreement (position := 168) (by kernel_rfl)
  have p578 : physical (.BaseLayerWitness 439) = logical 578 :=
    placed agreement (position := 578) (by kernel_rfl)
  have p84 : physical (.BaseLayerMemory 123) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p473 : physical (.BaseLayerWitness 334) = logical 473 :=
    placed agreement (position := 473) (by kernel_rfl)
  have p580 : physical (.BaseLayerWitness 441) = logical 580 :=
    placed agreement (position := 580) (by kernel_rfl)
  simp only [operand246, NativeLookups.Input.fields, sourceFields246, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p168, p578, p84, p473, p580]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement246 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup246).Contains (Verification.environment logical) ↔
      ∃ index, operand246.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields246 physical logical agreement]
  exact source_semantics246 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields247 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand247.input.fields physical = sourceFields247 logical := by
  have p579 : physical (.BaseLayerWitness 440) = logical 579 :=
    placed agreement (position := 579) (by kernel_rfl)
  have p529 : physical (.BaseLayerWitness 390) = logical 529 :=
    placed agreement (position := 529) (by kernel_rfl)
  have p581 : physical (.BaseLayerWitness 442) = logical 581 :=
    placed agreement (position := 581) (by kernel_rfl)
  have p582 : physical (.BaseLayerWitness 443) = logical 582 :=
    placed agreement (position := 582) (by kernel_rfl)
  simp only [operand247, NativeLookups.Input.fields, sourceFields247, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p579, p529, p581, p582]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement247 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup247).Contains (Verification.environment logical) ↔
      ∃ index, operand247.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields247 physical logical agreement]
  exact source_semantics247 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
