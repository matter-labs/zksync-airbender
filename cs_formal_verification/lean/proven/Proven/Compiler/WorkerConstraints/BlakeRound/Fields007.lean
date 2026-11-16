module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries004
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields56 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand56.input.fields physical = sourceFields56 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p714 : physical (.BaseLayerMemory 157) = logical 714 :=
    placed agreement (position := 714) (by kernel_rfl)
  have p715 : physical (.BaseLayerWitness 520) = logical 715 :=
    placed agreement (position := 715) (by kernel_rfl)
  simp only [operand56, NativeLookups.Input.fields, sourceFields56]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p714, p715]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement56 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup56).Contains (Verification.environment logical) ↔
      ∃ index, operand56.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields56 physical logical agreement]
  exact source_semantics56 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields57 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand57.input.fields physical = sourceFields57 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p716 : physical (.BaseLayerMemory 160) = logical 716 :=
    placed agreement (position := 716) (by kernel_rfl)
  have p718 : physical (.BaseLayerWitness 521) = logical 718 :=
    placed agreement (position := 718) (by kernel_rfl)
  simp only [operand57, NativeLookups.Input.fields, sourceFields57]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p716, p718]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement57 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup57).Contains (Verification.environment logical) ↔
      ∃ index, operand57.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields57 physical logical agreement]
  exact source_semantics57 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields58 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand58.input.fields physical = sourceFields58 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p717 : physical (.BaseLayerMemory 161) = logical 717 :=
    placed agreement (position := 717) (by kernel_rfl)
  have p718 : physical (.BaseLayerWitness 521) = logical 718 :=
    placed agreement (position := 718) (by kernel_rfl)
  simp only [operand58, NativeLookups.Input.fields, sourceFields58]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p717, p718]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement58 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup58).Contains (Verification.environment logical) ↔
      ∃ index, operand58.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields58 physical logical agreement]
  exact source_semantics58 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields59 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand59.input.fields physical = sourceFields59 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p719 : physical (.BaseLayerMemory 164) = logical 719 :=
    placed agreement (position := 719) (by kernel_rfl)
  have p721 : physical (.BaseLayerWitness 522) = logical 721 :=
    placed agreement (position := 721) (by kernel_rfl)
  simp only [operand59, NativeLookups.Input.fields, sourceFields59]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p719, p721]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement59 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup59).Contains (Verification.environment logical) ↔
      ∃ index, operand59.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields59 physical logical agreement]
  exact source_semantics59 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields60 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand60.input.fields physical = sourceFields60 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p720 : physical (.BaseLayerMemory 165) = logical 720 :=
    placed agreement (position := 720) (by kernel_rfl)
  have p721 : physical (.BaseLayerWitness 522) = logical 721 :=
    placed agreement (position := 721) (by kernel_rfl)
  simp only [operand60, NativeLookups.Input.fields, sourceFields60]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p720, p721]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement60 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup60).Contains (Verification.environment logical) ↔
      ∃ index, operand60.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields60 physical logical agreement]
  exact source_semantics60 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields61 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand61.input.fields physical = sourceFields61 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p722 : physical (.BaseLayerMemory 168) = logical 722 :=
    placed agreement (position := 722) (by kernel_rfl)
  have p724 : physical (.BaseLayerWitness 523) = logical 724 :=
    placed agreement (position := 724) (by kernel_rfl)
  simp only [operand61, NativeLookups.Input.fields, sourceFields61]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p722, p724]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement61 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup61).Contains (Verification.environment logical) ↔
      ∃ index, operand61.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields61 physical logical agreement]
  exact source_semantics61 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields62 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand62.input.fields physical = sourceFields62 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p723 : physical (.BaseLayerMemory 169) = logical 723 :=
    placed agreement (position := 723) (by kernel_rfl)
  have p724 : physical (.BaseLayerWitness 523) = logical 724 :=
    placed agreement (position := 724) (by kernel_rfl)
  simp only [operand62, NativeLookups.Input.fields, sourceFields62]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p723, p724]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement62 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup62).Contains (Verification.environment logical) ↔
      ∃ index, operand62.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields62 physical logical agreement]
  exact source_semantics62 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields63 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand63.input.fields physical = sourceFields63 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p725 : physical (.BaseLayerMemory 172) = logical 725 :=
    placed agreement (position := 725) (by kernel_rfl)
  have p727 : physical (.BaseLayerWitness 524) = logical 727 :=
    placed agreement (position := 727) (by kernel_rfl)
  simp only [operand63, NativeLookups.Input.fields, sourceFields63]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p725, p727]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement63 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup63).Contains (Verification.environment logical) ↔
      ∃ index, operand63.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields63 physical logical agreement]
  exact source_semantics63 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
