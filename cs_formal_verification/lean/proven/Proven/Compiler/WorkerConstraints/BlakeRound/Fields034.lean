module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries022
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries023

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields272 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand272.input.fields physical = sourceFields272 logical := by
  have p96 : physical (.BaseLayerMemory 141) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p531 : physical (.BaseLayerWitness 392) = logical 531 :=
    placed agreement (position := 531) (by kernel_rfl)
  have p616 : physical (.BaseLayerWitness 477) = logical 616 :=
    placed agreement (position := 616) (by kernel_rfl)
  have p617 : physical (.BaseLayerWitness 478) = logical 617 :=
    placed agreement (position := 617) (by kernel_rfl)
  have p619 : physical (.BaseLayerWitness 480) = logical 619 :=
    placed agreement (position := 619) (by kernel_rfl)
  simp only [operand272, NativeLookups.Input.fields, sourceFields272, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p96, p531, p616, p617, p619]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement272 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup272).Contains (Verification.environment logical) ↔
      ∃ index, operand272.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields272 physical logical agreement]
  exact source_semantics272 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields273 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand273.input.fields physical = sourceFields273 logical := by
  have p504 : physical (.BaseLayerWitness 365) = logical 504 :=
    placed agreement (position := 504) (by kernel_rfl)
  have p620 : physical (.BaseLayerWitness 481) = logical 620 :=
    placed agreement (position := 620) (by kernel_rfl)
  have p621 : physical (.BaseLayerWitness 482) = logical 621 :=
    placed agreement (position := 621) (by kernel_rfl)
  simp only [operand273, NativeLookups.Input.fields, sourceFields273, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p504, p620, p621]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement273 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup273).Contains (Verification.environment logical) ↔
      ∃ index, operand273.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields273 physical logical agreement]
  exact source_semantics273 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields274 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand274.input.fields physical = sourceFields274 logical := by
  have p67 : physical (.BaseLayerMemory 98) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p504 : physical (.BaseLayerWitness 365) = logical 504 :=
    placed agreement (position := 504) (by kernel_rfl)
  have p182 : physical (.BaseLayerWitness 43) = logical 182 :=
    placed agreement (position := 182) (by kernel_rfl)
  have p620 : physical (.BaseLayerWitness 481) = logical 620 :=
    placed agreement (position := 620) (by kernel_rfl)
  have p622 : physical (.BaseLayerWitness 483) = logical 622 :=
    placed agreement (position := 622) (by kernel_rfl)
  simp only [operand274, NativeLookups.Input.fields, sourceFields274, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p67, p504, p182, p620, p622]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement274 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup274).Contains (Verification.environment logical) ↔
      ∃ index, operand274.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields274 physical logical agreement]
  exact source_semantics274 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields275 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand275.input.fields physical = sourceFields275 logical := by
  have p440 : physical (.BaseLayerWitness 301) = logical 440 :=
    placed agreement (position := 440) (by kernel_rfl)
  have p621 : physical (.BaseLayerWitness 482) = logical 621 :=
    placed agreement (position := 621) (by kernel_rfl)
  have p623 : physical (.BaseLayerWitness 484) = logical 623 :=
    placed agreement (position := 623) (by kernel_rfl)
  have p624 : physical (.BaseLayerWitness 485) = logical 624 :=
    placed agreement (position := 624) (by kernel_rfl)
  simp only [operand275, NativeLookups.Input.fields, sourceFields275, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p440, p621, p623, p624]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement275 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup275).Contains (Verification.environment logical) ↔
      ∃ index, operand275.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields275 physical logical agreement]
  exact source_semantics275 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields276 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand276.input.fields physical = sourceFields276 logical := by
  have p99 : physical (.BaseLayerMemory 146) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p440 : physical (.BaseLayerWitness 301) = logical 440 :=
    placed agreement (position := 440) (by kernel_rfl)
  have p622 : physical (.BaseLayerWitness 483) = logical 622 :=
    placed agreement (position := 622) (by kernel_rfl)
  have p623 : physical (.BaseLayerWitness 484) = logical 623 :=
    placed agreement (position := 623) (by kernel_rfl)
  have p625 : physical (.BaseLayerWitness 486) = logical 625 :=
    placed agreement (position := 625) (by kernel_rfl)
  simp only [operand276, NativeLookups.Input.fields, sourceFields276, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p99, p440, p622, p623, p625]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement276 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup276).Contains (Verification.environment logical) ↔
      ∃ index, operand276.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields276 physical logical agreement]
  exact source_semantics276 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields277 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand277.input.fields physical = sourceFields277 logical := by
  have p505 : physical (.BaseLayerWitness 366) = logical 505 :=
    placed agreement (position := 505) (by kernel_rfl)
  have p626 : physical (.BaseLayerWitness 487) = logical 626 :=
    placed agreement (position := 626) (by kernel_rfl)
  have p627 : physical (.BaseLayerWitness 488) = logical 627 :=
    placed agreement (position := 627) (by kernel_rfl)
  simp only [operand277, NativeLookups.Input.fields, sourceFields277, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p505, p626, p627]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement277 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup277).Contains (Verification.environment logical) ↔
      ∃ index, operand277.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields277 physical logical agreement]
  exact source_semantics277 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields278 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand278.input.fields physical = sourceFields278 logical := by
  have p68 : physical (.BaseLayerMemory 99) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p505 : physical (.BaseLayerWitness 366) = logical 505 :=
    placed agreement (position := 505) (by kernel_rfl)
  have p184 : physical (.BaseLayerWitness 45) = logical 184 :=
    placed agreement (position := 184) (by kernel_rfl)
  have p626 : physical (.BaseLayerWitness 487) = logical 626 :=
    placed agreement (position := 626) (by kernel_rfl)
  have p628 : physical (.BaseLayerWitness 489) = logical 628 :=
    placed agreement (position := 628) (by kernel_rfl)
  simp only [operand278, NativeLookups.Input.fields, sourceFields278, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p68, p505, p184, p626, p628]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement278 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup278).Contains (Verification.environment logical) ↔
      ∃ index, operand278.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields278 physical logical agreement]
  exact source_semantics278 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields279 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand279.input.fields physical = sourceFields279 logical := by
  have p441 : physical (.BaseLayerWitness 302) = logical 441 :=
    placed agreement (position := 441) (by kernel_rfl)
  have p627 : physical (.BaseLayerWitness 488) = logical 627 :=
    placed agreement (position := 627) (by kernel_rfl)
  have p629 : physical (.BaseLayerWitness 490) = logical 629 :=
    placed agreement (position := 629) (by kernel_rfl)
  have p630 : physical (.BaseLayerWitness 491) = logical 630 :=
    placed agreement (position := 630) (by kernel_rfl)
  simp only [operand279, NativeLookups.Input.fields, sourceFields279, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p441, p627, p629, p630]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement279 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup279).Contains (Verification.environment logical) ↔
      ∃ index, operand279.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields279 physical logical agreement]
  exact source_semantics279 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
