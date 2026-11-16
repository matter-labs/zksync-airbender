module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries014
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries015

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields176 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand176.input.fields physical = sourceFields176 logical := by
  have p373 : physical (.BaseLayerWitness 234) = logical 373 :=
    placed agreement (position := 373) (by kernel_rfl)
  have p374 : physical (.BaseLayerWitness 235) = logical 374 :=
    placed agreement (position := 374) (by kernel_rfl)
  have p462 : physical (.BaseLayerWitness 323) = logical 462 :=
    placed agreement (position := 462) (by kernel_rfl)
  have p463 : physical (.BaseLayerWitness 324) = logical 463 :=
    placed agreement (position := 463) (by kernel_rfl)
  have p460 : physical (.BaseLayerWitness 321) = logical 460 :=
    placed agreement (position := 460) (by kernel_rfl)
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
  have p411 : physical (.BaseLayerWitness 272) = logical 411 :=
    placed agreement (position := 411) (by kernel_rfl)
  have p450 : physical (.BaseLayerWitness 311) = logical 450 :=
    placed agreement (position := 450) (by kernel_rfl)
  have p451 : physical (.BaseLayerWitness 312) = logical 451 :=
    placed agreement (position := 451) (by kernel_rfl)
  have p456 : physical (.BaseLayerWitness 317) = logical 456 :=
    placed agreement (position := 456) (by kernel_rfl)
  have p457 : physical (.BaseLayerWitness 318) = logical 457 :=
    placed agreement (position := 457) (by kernel_rfl)
  have p458 : physical (.BaseLayerWitness 319) = logical 458 :=
    placed agreement (position := 458) (by kernel_rfl)
  have p459 : physical (.BaseLayerWitness 320) = logical 459 :=
    placed agreement (position := 459) (by kernel_rfl)
  have p454 : physical (.BaseLayerWitness 315) = logical 454 :=
    placed agreement (position := 454) (by kernel_rfl)
  have p467 : physical (.BaseLayerWitness 328) = logical 467 :=
    placed agreement (position := 467) (by kernel_rfl)
  simp only [operand176, NativeLookups.Input.fields, sourceFields176, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p373, p374, p462, p463, p460, p193, p382, p383, p388, p391, p405, p406, p409, p411, p450, p451, p456, p457, p458, p459, p454, p467]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement176 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup176).Contains (Verification.environment logical) ↔
      ∃ index, operand176.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields176 physical logical agreement]
  exact source_semantics176 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields177 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand177.input.fields physical = sourceFields177 logical := by
  have p453 : physical (.BaseLayerWitness 314) = logical 453 :=
    placed agreement (position := 453) (by kernel_rfl)
  have p43 : physical (.BaseLayerMemory 62) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p468 : physical (.BaseLayerWitness 329) = logical 468 :=
    placed agreement (position := 468) (by kernel_rfl)
  have p470 : physical (.BaseLayerWitness 331) = logical 470 :=
    placed agreement (position := 470) (by kernel_rfl)
  simp only [operand177, NativeLookups.Input.fields, sourceFields177, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p453, p43, p468, p470]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement177 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup177).Contains (Verification.environment logical) ↔
      ∃ index, operand177.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields177 physical logical agreement]
  exact source_semantics177 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields178 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand178.input.fields physical = sourceFields178 logical := by
  have p451 : physical (.BaseLayerWitness 312) = logical 451 :=
    placed agreement (position := 451) (by kernel_rfl)
  have p44 : physical (.BaseLayerMemory 63) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  have p469 : physical (.BaseLayerWitness 330) = logical 469 :=
    placed agreement (position := 469) (by kernel_rfl)
  have p471 : physical (.BaseLayerWitness 332) = logical 471 :=
    placed agreement (position := 471) (by kernel_rfl)
  simp only [operand178, NativeLookups.Input.fields, sourceFields178, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p451, p44, p469, p471]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement178 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup178).Contains (Verification.environment logical) ↔
      ∃ index, operand178.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields178 physical logical agreement]
  exact source_semantics178 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields179 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand179.input.fields physical = sourceFields179 logical := by
  have p452 : physical (.BaseLayerWitness 313) = logical 452 :=
    placed agreement (position := 452) (by kernel_rfl)
  have p468 : physical (.BaseLayerWitness 329) = logical 468 :=
    placed agreement (position := 468) (by kernel_rfl)
  have p43 : physical (.BaseLayerMemory 62) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p159 : physical (.BaseLayerWitness 20) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p175 : physical (.BaseLayerWitness 36) = logical 175 :=
    placed agreement (position := 175) (by kernel_rfl)
  have p228 : physical (.BaseLayerWitness 89) = logical 228 :=
    placed agreement (position := 228) (by kernel_rfl)
  have p230 : physical (.BaseLayerWitness 91) = logical 230 :=
    placed agreement (position := 230) (by kernel_rfl)
  have p244 : physical (.BaseLayerWitness 105) = logical 244 :=
    placed agreement (position := 244) (by kernel_rfl)
  have p246 : physical (.BaseLayerWitness 107) = logical 246 :=
    placed agreement (position := 246) (by kernel_rfl)
  have p297 : physical (.BaseLayerWitness 158) = logical 297 :=
    placed agreement (position := 297) (by kernel_rfl)
  have p317 : physical (.BaseLayerWitness 178) = logical 317 :=
    placed agreement (position := 317) (by kernel_rfl)
  have p318 : physical (.BaseLayerWitness 179) = logical 318 :=
    placed agreement (position := 318) (by kernel_rfl)
  have p321 : physical (.BaseLayerWitness 182) = logical 321 :=
    placed agreement (position := 321) (by kernel_rfl)
  have p372 : physical (.BaseLayerWitness 233) = logical 372 :=
    placed agreement (position := 372) (by kernel_rfl)
  have p375 : physical (.BaseLayerWitness 236) = logical 375 :=
    placed agreement (position := 375) (by kernel_rfl)
  have p447 : physical (.BaseLayerWitness 308) = logical 447 :=
    placed agreement (position := 447) (by kernel_rfl)
  have p465 : physical (.BaseLayerWitness 326) = logical 465 :=
    placed agreement (position := 465) (by kernel_rfl)
  have p466 : physical (.BaseLayerWitness 327) = logical 466 :=
    placed agreement (position := 466) (by kernel_rfl)
  have p88 : physical (.BaseLayerMemory 129) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p471 : physical (.BaseLayerWitness 332) = logical 471 :=
    placed agreement (position := 471) (by kernel_rfl)
  simp only [operand179, NativeLookups.Input.fields, sourceFields179, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p452, p468, p43, p159, p175, p228, p230, p244, p246, p297, p317, p318, p321, p372, p375, p447, p465, p466, p88, p471]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement179 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup179).Contains (Verification.environment logical) ↔
      ∃ index, operand179.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields179 physical logical agreement]
  exact source_semantics179 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields180 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand180.input.fields physical = sourceFields180 logical := by
  have p450 : physical (.BaseLayerWitness 311) = logical 450 :=
    placed agreement (position := 450) (by kernel_rfl)
  have p469 : physical (.BaseLayerWitness 330) = logical 469 :=
    placed agreement (position := 469) (by kernel_rfl)
  have p43 : physical (.BaseLayerMemory 62) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p44 : physical (.BaseLayerMemory 63) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  have p159 : physical (.BaseLayerWitness 20) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 22) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  have p175 : physical (.BaseLayerWitness 36) = logical 175 :=
    placed agreement (position := 175) (by kernel_rfl)
  have p177 : physical (.BaseLayerWitness 38) = logical 177 :=
    placed agreement (position := 177) (by kernel_rfl)
  have p228 : physical (.BaseLayerWitness 89) = logical 228 :=
    placed agreement (position := 228) (by kernel_rfl)
  have p229 : physical (.BaseLayerWitness 90) = logical 229 :=
    placed agreement (position := 229) (by kernel_rfl)
  have p230 : physical (.BaseLayerWitness 91) = logical 230 :=
    placed agreement (position := 230) (by kernel_rfl)
  have p231 : physical (.BaseLayerWitness 92) = logical 231 :=
    placed agreement (position := 231) (by kernel_rfl)
  have p244 : physical (.BaseLayerWitness 105) = logical 244 :=
    placed agreement (position := 244) (by kernel_rfl)
  have p245 : physical (.BaseLayerWitness 106) = logical 245 :=
    placed agreement (position := 245) (by kernel_rfl)
  have p246 : physical (.BaseLayerWitness 107) = logical 246 :=
    placed agreement (position := 246) (by kernel_rfl)
  have p247 : physical (.BaseLayerWitness 108) = logical 247 :=
    placed agreement (position := 247) (by kernel_rfl)
  have p299 : physical (.BaseLayerWitness 160) = logical 299 :=
    placed agreement (position := 299) (by kernel_rfl)
  have p316 : physical (.BaseLayerWitness 177) = logical 316 :=
    placed agreement (position := 316) (by kernel_rfl)
  have p317 : physical (.BaseLayerWitness 178) = logical 317 :=
    placed agreement (position := 317) (by kernel_rfl)
  have p318 : physical (.BaseLayerWitness 179) = logical 318 :=
    placed agreement (position := 318) (by kernel_rfl)
  have p319 : physical (.BaseLayerWitness 180) = logical 319 :=
    placed agreement (position := 319) (by kernel_rfl)
  have p323 : physical (.BaseLayerWitness 184) = logical 323 :=
    placed agreement (position := 323) (by kernel_rfl)
  have p372 : physical (.BaseLayerWitness 233) = logical 372 :=
    placed agreement (position := 372) (by kernel_rfl)
  have p373 : physical (.BaseLayerWitness 234) = logical 373 :=
    placed agreement (position := 373) (by kernel_rfl)
  have p374 : physical (.BaseLayerWitness 235) = logical 374 :=
    placed agreement (position := 374) (by kernel_rfl)
  have p375 : physical (.BaseLayerWitness 236) = logical 375 :=
    placed agreement (position := 375) (by kernel_rfl)
  have p449 : physical (.BaseLayerWitness 310) = logical 449 :=
    placed agreement (position := 449) (by kernel_rfl)
  have p464 : physical (.BaseLayerWitness 325) = logical 464 :=
    placed agreement (position := 464) (by kernel_rfl)
  have p465 : physical (.BaseLayerWitness 326) = logical 465 :=
    placed agreement (position := 465) (by kernel_rfl)
  have p466 : physical (.BaseLayerWitness 327) = logical 466 :=
    placed agreement (position := 466) (by kernel_rfl)
  have p467 : physical (.BaseLayerWitness 328) = logical 467 :=
    placed agreement (position := 467) (by kernel_rfl)
  have p87 : physical (.BaseLayerMemory 128) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p470 : physical (.BaseLayerWitness 331) = logical 470 :=
    placed agreement (position := 470) (by kernel_rfl)
  simp only [operand180, NativeLookups.Input.fields, sourceFields180, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p450, p469, p43, p44, p159, p161, p175, p177, p228, p229, p230, p231, p244, p245, p246, p247, p299, p316, p317, p318, p319, p323, p372, p373, p374, p375, p449, p464, p465, p466, p467, p87, p470]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement180 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup180).Contains (Verification.environment logical) ↔
      ∃ index, operand180.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields180 physical logical agreement]
  exact source_semantics180 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields181 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand181.input.fields physical = sourceFields181 logical := by
  have p465 : physical (.BaseLayerWitness 326) = logical 465 :=
    placed agreement (position := 465) (by kernel_rfl)
  have p83 : physical (.BaseLayerMemory 122) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p472 : physical (.BaseLayerWitness 333) = logical 472 :=
    placed agreement (position := 472) (by kernel_rfl)
  have p474 : physical (.BaseLayerWitness 335) = logical 474 :=
    placed agreement (position := 474) (by kernel_rfl)
  simp only [operand181, NativeLookups.Input.fields, sourceFields181, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p465, p83, p472, p474]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement181 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup181).Contains (Verification.environment logical) ↔
      ∃ index, operand181.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields181 physical logical agreement]
  exact source_semantics181 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields182 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand182.input.fields physical = sourceFields182 logical := by
  have p464 : physical (.BaseLayerWitness 325) = logical 464 :=
    placed agreement (position := 464) (by kernel_rfl)
  have p84 : physical (.BaseLayerMemory 123) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p473 : physical (.BaseLayerWitness 334) = logical 473 :=
    placed agreement (position := 473) (by kernel_rfl)
  have p475 : physical (.BaseLayerWitness 336) = logical 475 :=
    placed agreement (position := 475) (by kernel_rfl)
  simp only [operand182, NativeLookups.Input.fields, sourceFields182, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p464, p84, p473, p475]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement182 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup182).Contains (Verification.environment logical) ↔
      ∃ index, operand182.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields182 physical logical agreement]
  exact source_semantics182 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields183 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand183.input.fields physical = sourceFields183 logical := by
  have p466 : physical (.BaseLayerWitness 327) = logical 466 :=
    placed agreement (position := 466) (by kernel_rfl)
  have p472 : physical (.BaseLayerWitness 333) = logical 472 :=
    placed agreement (position := 472) (by kernel_rfl)
  have p83 : physical (.BaseLayerMemory 122) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p87 : physical (.BaseLayerMemory 128) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
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
  have p409 : physical (.BaseLayerWitness 270) = logical 409 :=
    placed agreement (position := 409) (by kernel_rfl)
  have p452 : physical (.BaseLayerWitness 313) = logical 452 :=
    placed agreement (position := 452) (by kernel_rfl)
  have p453 : physical (.BaseLayerWitness 314) = logical 453 :=
    placed agreement (position := 453) (by kernel_rfl)
  have p456 : physical (.BaseLayerWitness 317) = logical 456 :=
    placed agreement (position := 456) (by kernel_rfl)
  have p64 : physical (.BaseLayerMemory 93) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p475 : physical (.BaseLayerWitness 336) = logical 475 :=
    placed agreement (position := 475) (by kernel_rfl)
  simp only [operand183, NativeLookups.Input.fields, sourceFields183, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p466, p472, p83, p87, p192, p384, p385, p388, p404, p407, p409, p452, p453, p456, p64, p475]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement183 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup183).Contains (Verification.environment logical) ↔
      ∃ index, operand183.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields183 physical logical agreement]
  exact source_semantics183 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
