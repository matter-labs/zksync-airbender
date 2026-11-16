module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries011

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields136 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand136.input.fields physical = sourceFields136 logical := by
  have p359 : physical (.BaseLayerWitness 220) = logical 359 :=
    placed agreement (position := 359) (by kernel_rfl)
  have p370 : physical (.BaseLayerWitness 231) = logical 370 :=
    placed agreement (position := 370) (by kernel_rfl)
  have p375 : physical (.BaseLayerWitness 236) = logical 375 :=
    placed agreement (position := 375) (by kernel_rfl)
  simp only [operand136, NativeLookups.Input.fields, sourceFields136, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p359, p370, p375]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement136 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup136).Contains (Verification.environment logical) ↔
      ∃ index, operand136.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields136 physical logical agreement]
  exact source_semantics136 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields137 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand137.input.fields physical = sourceFields137 logical := by
  have p380 : physical (.BaseLayerWitness 241) = logical 380 :=
    placed agreement (position := 380) (by kernel_rfl)
  have p376 : physical (.BaseLayerWitness 237) = logical 376 :=
    placed agreement (position := 376) (by kernel_rfl)
  have p377 : physical (.BaseLayerWitness 238) = logical 377 :=
    placed agreement (position := 377) (by kernel_rfl)
  have p382 : physical (.BaseLayerWitness 243) = logical 382 :=
    placed agreement (position := 382) (by kernel_rfl)
  simp only [operand137, NativeLookups.Input.fields, sourceFields137, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p380, p376, p377, p382]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement137 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup137).Contains (Verification.environment logical) ↔
      ∃ index, operand137.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields137 physical logical agreement]
  exact source_semantics137 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields138 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand138.input.fields physical = sourceFields138 logical := by
  have p196 : physical (.BaseLayerWitness 57) = logical 196 :=
    placed agreement (position := 196) (by kernel_rfl)
  have p380 : physical (.BaseLayerWitness 241) = logical 380 :=
    placed agreement (position := 380) (by kernel_rfl)
  have p167 : physical (.BaseLayerWitness 28) = logical 167 :=
    placed agreement (position := 167) (by kernel_rfl)
  have p183 : physical (.BaseLayerWitness 44) = logical 183 :=
    placed agreement (position := 183) (by kernel_rfl)
  have p236 : physical (.BaseLayerWitness 97) = logical 236 :=
    placed agreement (position := 236) (by kernel_rfl)
  have p376 : physical (.BaseLayerWitness 237) = logical 376 :=
    placed agreement (position := 376) (by kernel_rfl)
  have p377 : physical (.BaseLayerWitness 238) = logical 377 :=
    placed agreement (position := 377) (by kernel_rfl)
  have p383 : physical (.BaseLayerWitness 244) = logical 383 :=
    placed agreement (position := 383) (by kernel_rfl)
  simp only [operand138, NativeLookups.Input.fields, sourceFields138, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p196, p380, p167, p183, p236, p376, p377, p383]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement138 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup138).Contains (Verification.environment logical) ↔
      ∃ index, operand138.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields138 physical logical agreement]
  exact source_semantics138 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields139 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand139.input.fields physical = sourceFields139 logical := by
  have p381 : physical (.BaseLayerWitness 242) = logical 381 :=
    placed agreement (position := 381) (by kernel_rfl)
  have p378 : physical (.BaseLayerWitness 239) = logical 378 :=
    placed agreement (position := 378) (by kernel_rfl)
  have p379 : physical (.BaseLayerWitness 240) = logical 379 :=
    placed agreement (position := 379) (by kernel_rfl)
  have p384 : physical (.BaseLayerWitness 245) = logical 384 :=
    placed agreement (position := 384) (by kernel_rfl)
  simp only [operand139, NativeLookups.Input.fields, sourceFields139, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p381, p378, p379, p384]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement139 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup139).Contains (Verification.environment logical) ↔
      ∃ index, operand139.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields139 physical logical agreement]
  exact source_semantics139 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields140 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand140.input.fields physical = sourceFields140 logical := by
  have p197 : physical (.BaseLayerWitness 58) = logical 197 :=
    placed agreement (position := 197) (by kernel_rfl)
  have p381 : physical (.BaseLayerWitness 242) = logical 381 :=
    placed agreement (position := 381) (by kernel_rfl)
  have p169 : physical (.BaseLayerWitness 30) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  have p185 : physical (.BaseLayerWitness 46) = logical 185 :=
    placed agreement (position := 185) (by kernel_rfl)
  have p237 : physical (.BaseLayerWitness 98) = logical 237 :=
    placed agreement (position := 237) (by kernel_rfl)
  have p377 : physical (.BaseLayerWitness 238) = logical 377 :=
    placed agreement (position := 377) (by kernel_rfl)
  have p378 : physical (.BaseLayerWitness 239) = logical 378 :=
    placed agreement (position := 378) (by kernel_rfl)
  have p379 : physical (.BaseLayerWitness 240) = logical 379 :=
    placed agreement (position := 379) (by kernel_rfl)
  have p385 : physical (.BaseLayerWitness 246) = logical 385 :=
    placed agreement (position := 385) (by kernel_rfl)
  simp only [operand140, NativeLookups.Input.fields, sourceFields140, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p197, p381, p169, p185, p237, p377, p378, p379, p385]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement140 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup140).Contains (Verification.environment logical) ↔
      ∃ index, operand140.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields140 physical logical agreement]
  exact source_semantics140 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields141 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand141.input.fields physical = sourceFields141 logical := by
  have p393 : physical (.BaseLayerWitness 254) = logical 393 :=
    placed agreement (position := 393) (by kernel_rfl)
  have p387 : physical (.BaseLayerWitness 248) = logical 387 :=
    placed agreement (position := 387) (by kernel_rfl)
  have p396 : physical (.BaseLayerWitness 257) = logical 396 :=
    placed agreement (position := 396) (by kernel_rfl)
  simp only [operand141, NativeLookups.Input.fields, sourceFields141, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p393, p387, p396]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement141 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup141).Contains (Verification.environment logical) ↔
      ∃ index, operand141.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields141 physical logical agreement]
  exact source_semantics141 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields142 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand142.input.fields physical = sourceFields142 logical := by
  have p395 : physical (.BaseLayerWitness 256) = logical 395 :=
    placed agreement (position := 395) (by kernel_rfl)
  have p390 : physical (.BaseLayerWitness 251) = logical 390 :=
    placed agreement (position := 390) (by kernel_rfl)
  have p397 : physical (.BaseLayerWitness 258) = logical 397 :=
    placed agreement (position := 397) (by kernel_rfl)
  simp only [operand142, NativeLookups.Input.fields, sourceFields142, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p395, p390, p397]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement142 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup142).Contains (Verification.environment logical) ↔
      ∃ index, operand142.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields142 physical logical agreement]
  exact source_semantics142 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields143 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand143.input.fields physical = sourceFields143 logical := by
  have p183 : physical (.BaseLayerWitness 44) = logical 183 :=
    placed agreement (position := 183) (by kernel_rfl)
  have p392 : physical (.BaseLayerWitness 253) = logical 392 :=
    placed agreement (position := 392) (by kernel_rfl)
  have p393 : physical (.BaseLayerWitness 254) = logical 393 :=
    placed agreement (position := 393) (by kernel_rfl)
  have p394 : physical (.BaseLayerWitness 255) = logical 394 :=
    placed agreement (position := 394) (by kernel_rfl)
  have p192 : physical (.BaseLayerWitness 53) = logical 192 :=
    placed agreement (position := 192) (by kernel_rfl)
  have p384 : physical (.BaseLayerWitness 245) = logical 384 :=
    placed agreement (position := 384) (by kernel_rfl)
  have p385 : physical (.BaseLayerWitness 246) = logical 385 :=
    placed agreement (position := 385) (by kernel_rfl)
  have p386 : physical (.BaseLayerWitness 247) = logical 386 :=
    placed agreement (position := 386) (by kernel_rfl)
  have p387 : physical (.BaseLayerWitness 248) = logical 387 :=
    placed agreement (position := 387) (by kernel_rfl)
  have p388 : physical (.BaseLayerWitness 249) = logical 388 :=
    placed agreement (position := 388) (by kernel_rfl)
  have p389 : physical (.BaseLayerWitness 250) = logical 389 :=
    placed agreement (position := 389) (by kernel_rfl)
  have p398 : physical (.BaseLayerWitness 259) = logical 398 :=
    placed agreement (position := 398) (by kernel_rfl)
  simp only [operand143, NativeLookups.Input.fields, sourceFields143, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p183, p392, p393, p394, p192, p384, p385, p386, p387, p388, p389, p398]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement143 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup143).Contains (Verification.environment logical) ↔
      ∃ index, operand143.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields143 physical logical agreement]
  exact source_semantics143 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
