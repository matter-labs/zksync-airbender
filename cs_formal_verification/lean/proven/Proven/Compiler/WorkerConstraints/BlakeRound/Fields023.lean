module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries015

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields184 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand184.input.fields physical = sourceFields184 logical := by
  have p467 : physical (.BaseLayerWitness 328) = logical 467 :=
    placed agreement (position := 467) (by kernel_rfl)
  have p473 : physical (.BaseLayerWitness 334) = logical 473 :=
    placed agreement (position := 473) (by kernel_rfl)
  have p83 : physical (.BaseLayerMemory 122) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p84 : physical (.BaseLayerMemory 123) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p87 : physical (.BaseLayerMemory 128) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerMemory 129) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p192 : physical (.BaseLayerWitness 53) = logical 192 :=
    placed agreement (position := 192) (by kernel_rfl)
  have p193 : physical (.BaseLayerWitness 54) = logical 193 :=
    placed agreement (position := 193) (by kernel_rfl)
  have p382 : physical (.BaseLayerWitness 243) = logical 382 :=
    placed agreement (position := 382) (by kernel_rfl)
  have p383 : physical (.BaseLayerWitness 244) = logical 383 :=
    placed agreement (position := 383) (by kernel_rfl)
  have p384 : physical (.BaseLayerWitness 245) = logical 384 :=
    placed agreement (position := 384) (by kernel_rfl)
  have p385 : physical (.BaseLayerWitness 246) = logical 385 :=
    placed agreement (position := 385) (by kernel_rfl)
  have p391 : physical (.BaseLayerWitness 252) = logical 391 :=
    placed agreement (position := 391) (by kernel_rfl)
  have p404 : physical (.BaseLayerWitness 265) = logical 404 :=
    placed agreement (position := 404) (by kernel_rfl)
  have p405 : physical (.BaseLayerWitness 266) = logical 405 :=
    placed agreement (position := 405) (by kernel_rfl)
  have p406 : physical (.BaseLayerWitness 267) = logical 406 :=
    placed agreement (position := 406) (by kernel_rfl)
  have p407 : physical (.BaseLayerWitness 268) = logical 407 :=
    placed agreement (position := 407) (by kernel_rfl)
  have p411 : physical (.BaseLayerWitness 272) = logical 411 :=
    placed agreement (position := 411) (by kernel_rfl)
  have p450 : physical (.BaseLayerWitness 311) = logical 450 :=
    placed agreement (position := 450) (by kernel_rfl)
  have p451 : physical (.BaseLayerWitness 312) = logical 451 :=
    placed agreement (position := 451) (by kernel_rfl)
  have p452 : physical (.BaseLayerWitness 313) = logical 452 :=
    placed agreement (position := 452) (by kernel_rfl)
  have p453 : physical (.BaseLayerWitness 314) = logical 453 :=
    placed agreement (position := 453) (by kernel_rfl)
  have p459 : physical (.BaseLayerWitness 320) = logical 459 :=
    placed agreement (position := 459) (by kernel_rfl)
  have p63 : physical (.BaseLayerMemory 92) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p474 : physical (.BaseLayerWitness 335) = logical 474 :=
    placed agreement (position := 474) (by kernel_rfl)
  simp only [operand184, NativeLookups.Input.fields, sourceFields184, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p467, p473, p83, p84, p87, p88, p192, p193, p382, p383, p384, p385, p391, p404, p405, p406, p407, p411, p450, p451, p452, p453, p459, p63, p474]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement184 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup184).Contains (Verification.environment logical) ↔
      ∃ index, operand184.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields184 physical logical agreement]
  exact source_semantics184 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields185 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand185.input.fields physical = sourceFields185 logical := by
  have p324 : physical (.BaseLayerWitness 185) = logical 324 :=
    placed agreement (position := 324) (by kernel_rfl)
  have p476 : physical (.BaseLayerWitness 337) = logical 476 :=
    placed agreement (position := 476) (by kernel_rfl)
  have p477 : physical (.BaseLayerWitness 338) = logical 477 :=
    placed agreement (position := 477) (by kernel_rfl)
  have p480 : physical (.BaseLayerWitness 341) = logical 480 :=
    placed agreement (position := 480) (by kernel_rfl)
  simp only [operand185, NativeLookups.Input.fields, sourceFields185, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p324, p476, p477, p480]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement185 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup185).Contains (Verification.environment logical) ↔
      ∃ index, operand185.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields185 physical logical agreement]
  exact source_semantics185 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields186 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand186.input.fields physical = sourceFields186 logical := by
  have p327 : physical (.BaseLayerWitness 188) = logical 327 :=
    placed agreement (position := 327) (by kernel_rfl)
  have p163 : physical (.BaseLayerWitness 24) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  have p179 : physical (.BaseLayerWitness 40) = logical 179 :=
    placed agreement (position := 179) (by kernel_rfl)
  have p232 : physical (.BaseLayerWitness 93) = logical 232 :=
    placed agreement (position := 232) (by kernel_rfl)
  have p234 : physical (.BaseLayerWitness 95) = logical 234 :=
    placed agreement (position := 234) (by kernel_rfl)
  have p248 : physical (.BaseLayerWitness 109) = logical 248 :=
    placed agreement (position := 248) (by kernel_rfl)
  have p337 : physical (.BaseLayerWitness 198) = logical 337 :=
    placed agreement (position := 337) (by kernel_rfl)
  have p357 : physical (.BaseLayerWitness 218) = logical 357 :=
    placed agreement (position := 357) (by kernel_rfl)
  have p358 : physical (.BaseLayerWitness 219) = logical 358 :=
    placed agreement (position := 358) (by kernel_rfl)
  have p361 : physical (.BaseLayerWitness 222) = logical 361 :=
    placed agreement (position := 361) (by kernel_rfl)
  have p412 : physical (.BaseLayerWitness 273) = logical 412 :=
    placed agreement (position := 412) (by kernel_rfl)
  have p415 : physical (.BaseLayerWitness 276) = logical 415 :=
    placed agreement (position := 415) (by kernel_rfl)
  have p476 : physical (.BaseLayerWitness 337) = logical 476 :=
    placed agreement (position := 476) (by kernel_rfl)
  have p477 : physical (.BaseLayerWitness 338) = logical 477 :=
    placed agreement (position := 477) (by kernel_rfl)
  have p481 : physical (.BaseLayerWitness 342) = logical 481 :=
    placed agreement (position := 481) (by kernel_rfl)
  simp only [operand186, NativeLookups.Input.fields, sourceFields186, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p327, p163, p179, p232, p234, p248, p337, p357, p358, p361, p412, p415, p476, p477, p481]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement186 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup186).Contains (Verification.environment logical) ↔
      ∃ index, operand186.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields186 physical logical agreement]
  exact source_semantics186 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields187 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand187.input.fields physical = sourceFields187 logical := by
  have p325 : physical (.BaseLayerWitness 186) = logical 325 :=
    placed agreement (position := 325) (by kernel_rfl)
  have p478 : physical (.BaseLayerWitness 339) = logical 478 :=
    placed agreement (position := 478) (by kernel_rfl)
  have p479 : physical (.BaseLayerWitness 340) = logical 479 :=
    placed agreement (position := 479) (by kernel_rfl)
  have p482 : physical (.BaseLayerWitness 343) = logical 482 :=
    placed agreement (position := 482) (by kernel_rfl)
  simp only [operand187, NativeLookups.Input.fields, sourceFields187, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p325, p478, p479, p482]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement187 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup187).Contains (Verification.environment logical) ↔
      ∃ index, operand187.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields187 physical logical agreement]
  exact source_semantics187 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields188 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand188.input.fields physical = sourceFields188 logical := by
  have p326 : physical (.BaseLayerWitness 187) = logical 326 :=
    placed agreement (position := 326) (by kernel_rfl)
  have p165 : physical (.BaseLayerWitness 26) = logical 165 :=
    placed agreement (position := 165) (by kernel_rfl)
  have p181 : physical (.BaseLayerWitness 42) = logical 181 :=
    placed agreement (position := 181) (by kernel_rfl)
  have p233 : physical (.BaseLayerWitness 94) = logical 233 :=
    placed agreement (position := 233) (by kernel_rfl)
  have p235 : physical (.BaseLayerWitness 96) = logical 235 :=
    placed agreement (position := 235) (by kernel_rfl)
  have p249 : physical (.BaseLayerWitness 110) = logical 249 :=
    placed agreement (position := 249) (by kernel_rfl)
  have p337 : physical (.BaseLayerWitness 198) = logical 337 :=
    placed agreement (position := 337) (by kernel_rfl)
  have p339 : physical (.BaseLayerWitness 200) = logical 339 :=
    placed agreement (position := 339) (by kernel_rfl)
  have p356 : physical (.BaseLayerWitness 217) = logical 356 :=
    placed agreement (position := 356) (by kernel_rfl)
  have p359 : physical (.BaseLayerWitness 220) = logical 359 :=
    placed agreement (position := 359) (by kernel_rfl)
  have p361 : physical (.BaseLayerWitness 222) = logical 361 :=
    placed agreement (position := 361) (by kernel_rfl)
  have p363 : physical (.BaseLayerWitness 224) = logical 363 :=
    placed agreement (position := 363) (by kernel_rfl)
  have p413 : physical (.BaseLayerWitness 274) = logical 413 :=
    placed agreement (position := 413) (by kernel_rfl)
  have p414 : physical (.BaseLayerWitness 275) = logical 414 :=
    placed agreement (position := 414) (by kernel_rfl)
  have p477 : physical (.BaseLayerWitness 338) = logical 477 :=
    placed agreement (position := 477) (by kernel_rfl)
  have p478 : physical (.BaseLayerWitness 339) = logical 478 :=
    placed agreement (position := 478) (by kernel_rfl)
  have p479 : physical (.BaseLayerWitness 340) = logical 479 :=
    placed agreement (position := 479) (by kernel_rfl)
  have p483 : physical (.BaseLayerWitness 344) = logical 483 :=
    placed agreement (position := 483) (by kernel_rfl)
  simp only [operand188, NativeLookups.Input.fields, sourceFields188, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p326, p165, p181, p233, p235, p249, p337, p339, p356, p359, p361, p363, p413, p414, p477, p478, p479, p483]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement188 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup188).Contains (Verification.environment logical) ↔
      ∃ index, operand188.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields188 physical logical agreement]
  exact source_semantics188 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields189 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand189.input.fields physical = sourceFields189 logical := by
  have p491 : physical (.BaseLayerWitness 352) = logical 491 :=
    placed agreement (position := 491) (by kernel_rfl)
  have p485 : physical (.BaseLayerWitness 346) = logical 485 :=
    placed agreement (position := 485) (by kernel_rfl)
  have p494 : physical (.BaseLayerWitness 355) = logical 494 :=
    placed agreement (position := 494) (by kernel_rfl)
  simp only [operand189, NativeLookups.Input.fields, sourceFields189, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p491, p485, p494]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement189 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup189).Contains (Verification.environment logical) ↔
      ∃ index, operand189.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields189 physical logical agreement]
  exact source_semantics189 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields190 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand190.input.fields physical = sourceFields190 logical := by
  have p493 : physical (.BaseLayerWitness 354) = logical 493 :=
    placed agreement (position := 493) (by kernel_rfl)
  have p488 : physical (.BaseLayerWitness 349) = logical 488 :=
    placed agreement (position := 488) (by kernel_rfl)
  have p495 : physical (.BaseLayerWitness 356) = logical 495 :=
    placed agreement (position := 495) (by kernel_rfl)
  simp only [operand190, NativeLookups.Input.fields, sourceFields190, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p493, p488, p495]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement190 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup190).Contains (Verification.environment logical) ↔
      ∃ index, operand190.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields190 physical logical agreement]
  exact source_semantics190 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields191 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand191.input.fields physical = sourceFields191 logical := by
  have p412 : physical (.BaseLayerWitness 273) = logical 412 :=
    placed agreement (position := 412) (by kernel_rfl)
  have p415 : physical (.BaseLayerWitness 276) = logical 415 :=
    placed agreement (position := 415) (by kernel_rfl)
  have p490 : physical (.BaseLayerWitness 351) = logical 490 :=
    placed agreement (position := 490) (by kernel_rfl)
  have p491 : physical (.BaseLayerWitness 352) = logical 491 :=
    placed agreement (position := 491) (by kernel_rfl)
  have p492 : physical (.BaseLayerWitness 353) = logical 492 :=
    placed agreement (position := 492) (by kernel_rfl)
  have p186 : physical (.BaseLayerWitness 47) = logical 186 :=
    placed agreement (position := 186) (by kernel_rfl)
  have p264 : physical (.BaseLayerWitness 125) = logical 264 :=
    placed agreement (position := 264) (by kernel_rfl)
  have p265 : physical (.BaseLayerWitness 126) = logical 265 :=
    placed agreement (position := 265) (by kernel_rfl)
  have p268 : physical (.BaseLayerWitness 129) = logical 268 :=
    placed agreement (position := 268) (by kernel_rfl)
  have p284 : physical (.BaseLayerWitness 145) = logical 284 :=
    placed agreement (position := 284) (by kernel_rfl)
  have p287 : physical (.BaseLayerWitness 148) = logical 287 :=
    placed agreement (position := 287) (by kernel_rfl)
  have p289 : physical (.BaseLayerWitness 150) = logical 289 :=
    placed agreement (position := 289) (by kernel_rfl)
  have p482 : physical (.BaseLayerWitness 343) = logical 482 :=
    placed agreement (position := 482) (by kernel_rfl)
  have p483 : physical (.BaseLayerWitness 344) = logical 483 :=
    placed agreement (position := 483) (by kernel_rfl)
  have p484 : physical (.BaseLayerWitness 345) = logical 484 :=
    placed agreement (position := 484) (by kernel_rfl)
  have p485 : physical (.BaseLayerWitness 346) = logical 485 :=
    placed agreement (position := 485) (by kernel_rfl)
  have p486 : physical (.BaseLayerWitness 347) = logical 486 :=
    placed agreement (position := 486) (by kernel_rfl)
  have p487 : physical (.BaseLayerWitness 348) = logical 487 :=
    placed agreement (position := 487) (by kernel_rfl)
  have p496 : physical (.BaseLayerWitness 357) = logical 496 :=
    placed agreement (position := 496) (by kernel_rfl)
  simp only [operand191, NativeLookups.Input.fields, sourceFields191, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p412, p415, p490, p491, p492, p186, p264, p265, p268, p284, p287, p289, p482, p483, p484, p485, p486, p487, p496]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement191 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup191).Contains (Verification.environment logical) ↔
      ∃ index, operand191.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields191 physical logical agreement]
  exact source_semantics191 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
