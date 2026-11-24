module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries021

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields256 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand256.input.fields physical = sourceFields256 logical := by
  have p88 : physical (.BaseLayerMemory 129) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p471 : physical (.BaseLayerWitness 332) = logical 471 :=
    placed agreement (position := 471) (by kernel_rfl)
  have p592 : physical (.BaseLayerWitness 453) = logical 592 :=
    placed agreement (position := 592) (by kernel_rfl)
  have p593 : physical (.BaseLayerWitness 454) = logical 593 :=
    placed agreement (position := 593) (by kernel_rfl)
  have p595 : physical (.BaseLayerWitness 456) = logical 595 :=
    placed agreement (position := 595) (by kernel_rfl)
  simp only [operand256, NativeLookups.Input.fields, sourceFields256, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p88, p471, p592, p593, p595]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement256 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup256).Contains (Verification.environment logical) ↔
      ∃ index, operand256.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields256 physical logical agreement]
  exact source_semantics256 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields257 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand257.input.fields physical = sourceFields257 logical := by
  have p444 : physical (.BaseLayerWitness 305) = logical 444 :=
    placed agreement (position := 444) (by kernel_rfl)
  have p596 : physical (.BaseLayerWitness 457) = logical 596 :=
    placed agreement (position := 596) (by kernel_rfl)
  have p597 : physical (.BaseLayerWitness 458) = logical 597 :=
    placed agreement (position := 597) (by kernel_rfl)
  simp only [operand257, NativeLookups.Input.fields, sourceFields257, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p444, p596, p597]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement257 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup257).Contains (Verification.environment logical) ↔
      ∃ index, operand257.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields257 physical logical agreement]
  exact source_semantics257 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields258 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand258.input.fields physical = sourceFields258 logical := by
  have p59 : physical (.BaseLayerMemory 86) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p444 : physical (.BaseLayerWitness 305) = logical 444 :=
    placed agreement (position := 444) (by kernel_rfl)
  have p174 : physical (.BaseLayerWitness 35) = logical 174 :=
    placed agreement (position := 174) (by kernel_rfl)
  have p596 : physical (.BaseLayerWitness 457) = logical 596 :=
    placed agreement (position := 596) (by kernel_rfl)
  have p598 : physical (.BaseLayerWitness 459) = logical 598 :=
    placed agreement (position := 598) (by kernel_rfl)
  simp only [operand258, NativeLookups.Input.fields, sourceFields258, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p59, p444, p174, p596, p598]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement258 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup258).Contains (Verification.environment logical) ↔
      ∃ index, operand258.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields258 physical logical agreement]
  exact source_semantics258 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields259 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand259.input.fields physical = sourceFields259 logical := by
  have p500 : physical (.BaseLayerWitness 361) = logical 500 :=
    placed agreement (position := 500) (by kernel_rfl)
  have p597 : physical (.BaseLayerWitness 458) = logical 597 :=
    placed agreement (position := 597) (by kernel_rfl)
  have p599 : physical (.BaseLayerWitness 460) = logical 599 :=
    placed agreement (position := 599) (by kernel_rfl)
  have p600 : physical (.BaseLayerWitness 461) = logical 600 :=
    placed agreement (position := 600) (by kernel_rfl)
  simp only [operand259, NativeLookups.Input.fields, sourceFields259, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p500, p597, p599, p600]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement259 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup259).Contains (Verification.environment logical) ↔
      ∃ index, operand259.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields259 physical logical agreement]
  exact source_semantics259 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields260 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand260.input.fields physical = sourceFields260 logical := by
  have p91 : physical (.BaseLayerMemory 134) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p500 : physical (.BaseLayerWitness 361) = logical 500 :=
    placed agreement (position := 500) (by kernel_rfl)
  have p598 : physical (.BaseLayerWitness 459) = logical 598 :=
    placed agreement (position := 598) (by kernel_rfl)
  have p599 : physical (.BaseLayerWitness 460) = logical 599 :=
    placed agreement (position := 599) (by kernel_rfl)
  have p601 : physical (.BaseLayerWitness 462) = logical 601 :=
    placed agreement (position := 601) (by kernel_rfl)
  simp only [operand260, NativeLookups.Input.fields, sourceFields260, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p91, p500, p598, p599, p601]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement260 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup260).Contains (Verification.environment logical) ↔
      ∃ index, operand260.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields260 physical logical agreement]
  exact source_semantics260 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields261 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand261.input.fields physical = sourceFields261 logical := by
  have p445 : physical (.BaseLayerWitness 306) = logical 445 :=
    placed agreement (position := 445) (by kernel_rfl)
  have p602 : physical (.BaseLayerWitness 463) = logical 602 :=
    placed agreement (position := 602) (by kernel_rfl)
  have p603 : physical (.BaseLayerWitness 464) = logical 603 :=
    placed agreement (position := 603) (by kernel_rfl)
  simp only [operand261, NativeLookups.Input.fields, sourceFields261, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p445, p602, p603]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement261 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup261).Contains (Verification.environment logical) ↔
      ∃ index, operand261.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields261 physical logical agreement]
  exact source_semantics261 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields262 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand262.input.fields physical = sourceFields262 logical := by
  have p60 : physical (.BaseLayerMemory 87) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p445 : physical (.BaseLayerWitness 306) = logical 445 :=
    placed agreement (position := 445) (by kernel_rfl)
  have p176 : physical (.BaseLayerWitness 37) = logical 176 :=
    placed agreement (position := 176) (by kernel_rfl)
  have p602 : physical (.BaseLayerWitness 463) = logical 602 :=
    placed agreement (position := 602) (by kernel_rfl)
  have p604 : physical (.BaseLayerWitness 465) = logical 604 :=
    placed agreement (position := 604) (by kernel_rfl)
  simp only [operand262, NativeLookups.Input.fields, sourceFields262, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p60, p445, p176, p602, p604]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement262 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup262).Contains (Verification.environment logical) ↔
      ∃ index, operand262.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields262 physical logical agreement]
  exact source_semantics262 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields263 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand263.input.fields physical = sourceFields263 logical := by
  have p501 : physical (.BaseLayerWitness 362) = logical 501 :=
    placed agreement (position := 501) (by kernel_rfl)
  have p603 : physical (.BaseLayerWitness 464) = logical 603 :=
    placed agreement (position := 603) (by kernel_rfl)
  have p605 : physical (.BaseLayerWitness 466) = logical 605 :=
    placed agreement (position := 605) (by kernel_rfl)
  have p606 : physical (.BaseLayerWitness 467) = logical 606 :=
    placed agreement (position := 606) (by kernel_rfl)
  simp only [operand263, NativeLookups.Input.fields, sourceFields263, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p501, p603, p605, p606]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement263 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup263).Contains (Verification.environment logical) ↔
      ∃ index, operand263.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields263 physical logical agreement]
  exact source_semantics263 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
