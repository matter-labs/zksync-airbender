module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries012

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields144 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand144.input.fields physical = sourceFields144 logical := by
  have p185 : physical (.BaseLayerWitness 46) = logical 185 :=
    placed agreement (position := 185) (by kernel_rfl)
  have p394 : physical (.BaseLayerWitness 255) = logical 394 :=
    placed agreement (position := 394) (by kernel_rfl)
  have p395 : physical (.BaseLayerWitness 256) = logical 395 :=
    placed agreement (position := 395) (by kernel_rfl)
  have p392 : physical (.BaseLayerWitness 253) = logical 392 :=
    placed agreement (position := 392) (by kernel_rfl)
  have p193 : physical (.BaseLayerWitness 54) = logical 193 :=
    placed agreement (position := 193) (by kernel_rfl)
  have p382 : physical (.BaseLayerWitness 243) = logical 382 :=
    placed agreement (position := 382) (by kernel_rfl)
  have p383 : physical (.BaseLayerWitness 244) = logical 383 :=
    placed agreement (position := 383) (by kernel_rfl)
  have p388 : physical (.BaseLayerWitness 249) = logical 388 :=
    placed agreement (position := 388) (by kernel_rfl)
  have p389 : physical (.BaseLayerWitness 250) = logical 389 :=
    placed agreement (position := 389) (by kernel_rfl)
  have p390 : physical (.BaseLayerWitness 251) = logical 390 :=
    placed agreement (position := 390) (by kernel_rfl)
  have p391 : physical (.BaseLayerWitness 252) = logical 391 :=
    placed agreement (position := 391) (by kernel_rfl)
  have p386 : physical (.BaseLayerWitness 247) = logical 386 :=
    placed agreement (position := 386) (by kernel_rfl)
  have p399 : physical (.BaseLayerWitness 260) = logical 399 :=
    placed agreement (position := 399) (by kernel_rfl)
  simp only [operand144, NativeLookups.Input.fields, sourceFields144, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p185, p394, p395, p392, p193, p382, p383, p388, p389, p390, p391, p386, p399]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement144 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup144).Contains (Verification.environment logical) ↔
      ∃ index, operand144.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields144 physical logical agreement]
  exact source_semantics144 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields145 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand145.input.fields physical = sourceFields145 logical := by
  have p385 : physical (.BaseLayerWitness 246) = logical 385 :=
    placed agreement (position := 385) (by kernel_rfl)
  have p167 : physical (.BaseLayerWitness 28) = logical 167 :=
    placed agreement (position := 167) (by kernel_rfl)
  have p183 : physical (.BaseLayerWitness 44) = logical 183 :=
    placed agreement (position := 183) (by kernel_rfl)
  have p236 : physical (.BaseLayerWitness 97) = logical 236 :=
    placed agreement (position := 236) (by kernel_rfl)
  have p238 : physical (.BaseLayerWitness 99) = logical 238 :=
    placed agreement (position := 238) (by kernel_rfl)
  have p377 : physical (.BaseLayerWitness 238) = logical 377 :=
    placed agreement (position := 377) (by kernel_rfl)
  have p397 : physical (.BaseLayerWitness 258) = logical 397 :=
    placed agreement (position := 397) (by kernel_rfl)
  have p398 : physical (.BaseLayerWitness 259) = logical 398 :=
    placed agreement (position := 398) (by kernel_rfl)
  have p400 : physical (.BaseLayerWitness 261) = logical 400 :=
    placed agreement (position := 400) (by kernel_rfl)
  have p401 : physical (.BaseLayerWitness 262) = logical 401 :=
    placed agreement (position := 401) (by kernel_rfl)
  have p404 : physical (.BaseLayerWitness 265) = logical 404 :=
    placed agreement (position := 404) (by kernel_rfl)
  simp only [operand145, NativeLookups.Input.fields, sourceFields145, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p385, p167, p183, p236, p238, p377, p397, p398, p400, p401, p404]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement145 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup145).Contains (Verification.environment logical) ↔
      ∃ index, operand145.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields145 physical logical agreement]
  exact source_semantics145 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields146 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand146.input.fields physical = sourceFields146 logical := by
  have p383 : physical (.BaseLayerWitness 244) = logical 383 :=
    placed agreement (position := 383) (by kernel_rfl)
  have p169 : physical (.BaseLayerWitness 30) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  have p185 : physical (.BaseLayerWitness 46) = logical 185 :=
    placed agreement (position := 185) (by kernel_rfl)
  have p237 : physical (.BaseLayerWitness 98) = logical 237 :=
    placed agreement (position := 237) (by kernel_rfl)
  have p239 : physical (.BaseLayerWitness 100) = logical 239 :=
    placed agreement (position := 239) (by kernel_rfl)
  have p377 : physical (.BaseLayerWitness 238) = logical 377 :=
    placed agreement (position := 377) (by kernel_rfl)
  have p379 : physical (.BaseLayerWitness 240) = logical 379 :=
    placed agreement (position := 379) (by kernel_rfl)
  have p396 : physical (.BaseLayerWitness 257) = logical 396 :=
    placed agreement (position := 396) (by kernel_rfl)
  have p399 : physical (.BaseLayerWitness 260) = logical 399 :=
    placed agreement (position := 399) (by kernel_rfl)
  have p401 : physical (.BaseLayerWitness 262) = logical 401 :=
    placed agreement (position := 401) (by kernel_rfl)
  have p402 : physical (.BaseLayerWitness 263) = logical 402 :=
    placed agreement (position := 402) (by kernel_rfl)
  have p403 : physical (.BaseLayerWitness 264) = logical 403 :=
    placed agreement (position := 403) (by kernel_rfl)
  have p405 : physical (.BaseLayerWitness 266) = logical 405 :=
    placed agreement (position := 405) (by kernel_rfl)
  simp only [operand146, NativeLookups.Input.fields, sourceFields146, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p383, p169, p185, p237, p239, p377, p379, p396, p399, p401, p402, p403, p405]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement146 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup146).Contains (Verification.environment logical) ↔
      ∃ index, operand146.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields146 physical logical agreement]
  exact source_semantics146 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields147 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand147.input.fields physical = sourceFields147 logical := by
  have p384 : physical (.BaseLayerWitness 245) = logical 384 :=
    placed agreement (position := 384) (by kernel_rfl)
  have p400 : physical (.BaseLayerWitness 261) = logical 400 :=
    placed agreement (position := 400) (by kernel_rfl)
  have p401 : physical (.BaseLayerWitness 262) = logical 401 :=
    placed agreement (position := 401) (by kernel_rfl)
  have p406 : physical (.BaseLayerWitness 267) = logical 406 :=
    placed agreement (position := 406) (by kernel_rfl)
  simp only [operand147, NativeLookups.Input.fields, sourceFields147, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p384, p400, p401, p406]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement147 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup147).Contains (Verification.environment logical) ↔
      ∃ index, operand147.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields147 physical logical agreement]
  exact source_semantics147 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields148 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand148.input.fields physical = sourceFields148 logical := by
  have p382 : physical (.BaseLayerWitness 243) = logical 382 :=
    placed agreement (position := 382) (by kernel_rfl)
  have p402 : physical (.BaseLayerWitness 263) = logical 402 :=
    placed agreement (position := 402) (by kernel_rfl)
  have p403 : physical (.BaseLayerWitness 264) = logical 403 :=
    placed agreement (position := 403) (by kernel_rfl)
  have p407 : physical (.BaseLayerWitness 268) = logical 407 :=
    placed agreement (position := 407) (by kernel_rfl)
  simp only [operand148, NativeLookups.Input.fields, sourceFields148, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p382, p402, p403, p407]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement148 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup148).Contains (Verification.environment logical) ↔
      ∃ index, operand148.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields148 physical logical agreement]
  exact source_semantics148 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields149 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand149.input.fields physical = sourceFields149 logical := by
  have p397 : physical (.BaseLayerWitness 258) = logical 397 :=
    placed agreement (position := 397) (by kernel_rfl)
  have p192 : physical (.BaseLayerWitness 53) = logical 192 :=
    placed agreement (position := 192) (by kernel_rfl)
  have p384 : physical (.BaseLayerWitness 245) = logical 384 :=
    placed agreement (position := 384) (by kernel_rfl)
  have p385 : physical (.BaseLayerWitness 246) = logical 385 :=
    placed agreement (position := 385) (by kernel_rfl)
  have p388 : physical (.BaseLayerWitness 249) = logical 388 :=
    placed agreement (position := 388) (by kernel_rfl)
  have p404 : physical (.BaseLayerWitness 265) = logical 404 :=
    placed agreement (position := 404) (by kernel_rfl)
  have p407 : physical (.BaseLayerWitness 268) = logical 407 :=
    placed agreement (position := 407) (by kernel_rfl)
  have p408 : physical (.BaseLayerWitness 269) = logical 408 :=
    placed agreement (position := 408) (by kernel_rfl)
  have p409 : physical (.BaseLayerWitness 270) = logical 409 :=
    placed agreement (position := 409) (by kernel_rfl)
  have p412 : physical (.BaseLayerWitness 273) = logical 412 :=
    placed agreement (position := 412) (by kernel_rfl)
  simp only [operand149, NativeLookups.Input.fields, sourceFields149, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p397, p192, p384, p385, p388, p404, p407, p408, p409, p412]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement149 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup149).Contains (Verification.environment logical) ↔
      ∃ index, operand149.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields149 physical logical agreement]
  exact source_semantics149 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields150 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand150.input.fields physical = sourceFields150 logical := by
  have p396 : physical (.BaseLayerWitness 257) = logical 396 :=
    placed agreement (position := 396) (by kernel_rfl)
  have p193 : physical (.BaseLayerWitness 54) = logical 193 :=
    placed agreement (position := 193) (by kernel_rfl)
  have p382 : physical (.BaseLayerWitness 243) = logical 382 :=
    placed agreement (position := 382) (by kernel_rfl)
  have p383 : physical (.BaseLayerWitness 244) = logical 383 :=
    placed agreement (position := 383) (by kernel_rfl)
  have p388 : physical (.BaseLayerWitness 249) = logical 388 :=
    placed agreement (position := 388) (by kernel_rfl)
  have p391 : physical (.BaseLayerWitness 252) = logical 391 :=
    placed agreement (position := 391) (by kernel_rfl)
  have p405 : physical (.BaseLayerWitness 266) = logical 405 :=
    placed agreement (position := 405) (by kernel_rfl)
  have p406 : physical (.BaseLayerWitness 267) = logical 406 :=
    placed agreement (position := 406) (by kernel_rfl)
  have p409 : physical (.BaseLayerWitness 270) = logical 409 :=
    placed agreement (position := 409) (by kernel_rfl)
  have p410 : physical (.BaseLayerWitness 271) = logical 410 :=
    placed agreement (position := 410) (by kernel_rfl)
  have p411 : physical (.BaseLayerWitness 272) = logical 411 :=
    placed agreement (position := 411) (by kernel_rfl)
  have p413 : physical (.BaseLayerWitness 274) = logical 413 :=
    placed agreement (position := 413) (by kernel_rfl)
  simp only [operand150, NativeLookups.Input.fields, sourceFields150, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p396, p193, p382, p383, p388, p391, p405, p406, p409, p410, p411, p413]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement150 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup150).Contains (Verification.environment logical) ↔
      ∃ index, operand150.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields150 physical logical agreement]
  exact source_semantics150 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields151 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand151.input.fields physical = sourceFields151 logical := by
  have p398 : physical (.BaseLayerWitness 259) = logical 398 :=
    placed agreement (position := 398) (by kernel_rfl)
  have p408 : physical (.BaseLayerWitness 269) = logical 408 :=
    placed agreement (position := 408) (by kernel_rfl)
  have p414 : physical (.BaseLayerWitness 275) = logical 414 :=
    placed agreement (position := 414) (by kernel_rfl)
  simp only [operand151, NativeLookups.Input.fields, sourceFields151, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p398, p408, p414]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement151 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup151).Contains (Verification.environment logical) ↔
      ∃ index, operand151.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields151 physical logical agreement]
  exact source_semantics151 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
