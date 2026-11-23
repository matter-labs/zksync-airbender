module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries006
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries007

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields80 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand80.input.fields physical = sourceFields80 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p750 : physical (.BaseLayerMemory 205) = logical 750 :=
    placed agreement (position := 750) (by kernel_rfl)
  have p751 : physical (.BaseLayerWitness 532) = logical 751 :=
    placed agreement (position := 751) (by kernel_rfl)
  simp only [operand80, NativeLookups.Input.fields, sourceFields80]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p750, p751]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement80 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup80).Contains (Verification.environment logical) ↔
      ∃ index, operand80.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields80 physical logical agreement]
  exact source_semantics80 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields81 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand81.input.fields physical = sourceFields81 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p752 : physical (.BaseLayerMemory 208) = logical 752 :=
    placed agreement (position := 752) (by kernel_rfl)
  have p754 : physical (.BaseLayerWitness 533) = logical 754 :=
    placed agreement (position := 754) (by kernel_rfl)
  simp only [operand81, NativeLookups.Input.fields, sourceFields81]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p752, p754]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement81 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup81).Contains (Verification.environment logical) ↔
      ∃ index, operand81.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields81 physical logical agreement]
  exact source_semantics81 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields82 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand82.input.fields physical = sourceFields82 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p753 : physical (.BaseLayerMemory 209) = logical 753 :=
    placed agreement (position := 753) (by kernel_rfl)
  have p754 : physical (.BaseLayerWitness 533) = logical 754 :=
    placed agreement (position := 754) (by kernel_rfl)
  simp only [operand82, NativeLookups.Input.fields, sourceFields82]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p753, p754]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement82 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup82).Contains (Verification.environment logical) ↔
      ∃ index, operand82.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields82 physical logical agreement]
  exact source_semantics82 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields83 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand83.input.fields physical = sourceFields83 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p755 : physical (.BaseLayerMemory 212) = logical 755 :=
    placed agreement (position := 755) (by kernel_rfl)
  have p757 : physical (.BaseLayerWitness 534) = logical 757 :=
    placed agreement (position := 757) (by kernel_rfl)
  simp only [operand83, NativeLookups.Input.fields, sourceFields83]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p755, p757]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement83 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup83).Contains (Verification.environment logical) ↔
      ∃ index, operand83.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields83 physical logical agreement]
  exact source_semantics83 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields84 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand84.input.fields physical = sourceFields84 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p756 : physical (.BaseLayerMemory 213) = logical 756 :=
    placed agreement (position := 756) (by kernel_rfl)
  have p757 : physical (.BaseLayerWitness 534) = logical 757 :=
    placed agreement (position := 757) (by kernel_rfl)
  simp only [operand84, NativeLookups.Input.fields, sourceFields84]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p756, p757]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement84 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup84).Contains (Verification.environment logical) ↔
      ∃ index, operand84.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields84 physical logical agreement]
  exact source_semantics84 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields85 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand85.input.fields physical = sourceFields85 logical := by
  have p1 : physical (.BaseLayerMemory 223) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p758 : physical (.BaseLayerMemory 216) = logical 758 :=
    placed agreement (position := 758) (by kernel_rfl)
  have p760 : physical (.BaseLayerWitness 535) = logical 760 :=
    placed agreement (position := 760) (by kernel_rfl)
  simp only [operand85, NativeLookups.Input.fields, sourceFields85]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p758, p760]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement85 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup85).Contains (Verification.environment logical) ↔
      ∃ index, operand85.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields85 physical logical agreement]
  exact source_semantics85 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields86 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand86.input.fields physical = sourceFields86 logical := by
  have p2 : physical (.BaseLayerMemory 224) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p759 : physical (.BaseLayerMemory 217) = logical 759 :=
    placed agreement (position := 759) (by kernel_rfl)
  have p760 : physical (.BaseLayerWitness 535) = logical 760 :=
    placed agreement (position := 760) (by kernel_rfl)
  simp only [operand86, NativeLookups.Input.fields, sourceFields86]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p759, p760]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement86 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup86).Contains (Verification.environment logical) ↔
      ∃ index, operand86.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields86 physical logical agreement]
  exact source_semantics86 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields87 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand87.input.fields physical = sourceFields87 logical := by
  have p3 : physical (.BaseLayerMemory 2) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  simp only [operand87, NativeLookups.Input.fields, sourceFields87]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement87 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup87).Contains (Verification.environment logical) ↔
      ∃ index, operand87.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields87 physical logical agreement]
  exact source_semantics87 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
