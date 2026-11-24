module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries016

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields192 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand192.input.fields physical = sourceFields192 logical := by
  have p413 : physical (.BaseLayerWitness 274) = logical 413 :=
    placed agreement (position := 413) (by kernel_rfl)
  have p414 : physical (.BaseLayerWitness 275) = logical 414 :=
    placed agreement (position := 414) (by kernel_rfl)
  have p492 : physical (.BaseLayerWitness 353) = logical 492 :=
    placed agreement (position := 492) (by kernel_rfl)
  have p493 : physical (.BaseLayerWitness 354) = logical 493 :=
    placed agreement (position := 493) (by kernel_rfl)
  have p490 : physical (.BaseLayerWitness 351) = logical 490 :=
    placed agreement (position := 490) (by kernel_rfl)
  have p187 : physical (.BaseLayerWitness 48) = logical 187 :=
    placed agreement (position := 187) (by kernel_rfl)
  have p262 : physical (.BaseLayerWitness 123) = logical 262 :=
    placed agreement (position := 262) (by kernel_rfl)
  have p263 : physical (.BaseLayerWitness 124) = logical 263 :=
    placed agreement (position := 263) (by kernel_rfl)
  have p268 : physical (.BaseLayerWitness 129) = logical 268 :=
    placed agreement (position := 268) (by kernel_rfl)
  have p271 : physical (.BaseLayerWitness 132) = logical 271 :=
    placed agreement (position := 271) (by kernel_rfl)
  have p285 : physical (.BaseLayerWitness 146) = logical 285 :=
    placed agreement (position := 285) (by kernel_rfl)
  have p286 : physical (.BaseLayerWitness 147) = logical 286 :=
    placed agreement (position := 286) (by kernel_rfl)
  have p289 : physical (.BaseLayerWitness 150) = logical 289 :=
    placed agreement (position := 289) (by kernel_rfl)
  have p291 : physical (.BaseLayerWitness 152) = logical 291 :=
    placed agreement (position := 291) (by kernel_rfl)
  have p480 : physical (.BaseLayerWitness 341) = logical 480 :=
    placed agreement (position := 480) (by kernel_rfl)
  have p481 : physical (.BaseLayerWitness 342) = logical 481 :=
    placed agreement (position := 481) (by kernel_rfl)
  have p486 : physical (.BaseLayerWitness 347) = logical 486 :=
    placed agreement (position := 486) (by kernel_rfl)
  have p487 : physical (.BaseLayerWitness 348) = logical 487 :=
    placed agreement (position := 487) (by kernel_rfl)
  have p488 : physical (.BaseLayerWitness 349) = logical 488 :=
    placed agreement (position := 488) (by kernel_rfl)
  have p489 : physical (.BaseLayerWitness 350) = logical 489 :=
    placed agreement (position := 489) (by kernel_rfl)
  have p484 : physical (.BaseLayerWitness 345) = logical 484 :=
    placed agreement (position := 484) (by kernel_rfl)
  have p497 : physical (.BaseLayerWitness 358) = logical 497 :=
    placed agreement (position := 497) (by kernel_rfl)
  simp only [operand192, NativeLookups.Input.fields, sourceFields192, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p413, p414, p492, p493, p490, p187, p262, p263, p268, p271, p285, p286, p289, p291, p480, p481, p486, p487, p488, p489, p484, p497]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement192 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup192).Contains (Verification.environment logical) ↔
      ∃ index, operand192.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields192 physical logical agreement]
  exact source_semantics192 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields193 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand193.input.fields physical = sourceFields193 logical := by
  have p483 : physical (.BaseLayerWitness 344) = logical 483 :=
    placed agreement (position := 483) (by kernel_rfl)
  have p47 : physical (.BaseLayerMemory 68) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p498 : physical (.BaseLayerWitness 359) = logical 498 :=
    placed agreement (position := 498) (by kernel_rfl)
  have p500 : physical (.BaseLayerWitness 361) = logical 500 :=
    placed agreement (position := 500) (by kernel_rfl)
  simp only [operand193, NativeLookups.Input.fields, sourceFields193, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p483, p47, p498, p500]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement193 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup193).Contains (Verification.environment logical) ↔
      ∃ index, operand193.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields193 physical logical agreement]
  exact source_semantics193 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields194 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand194.input.fields physical = sourceFields194 logical := by
  have p481 : physical (.BaseLayerWitness 342) = logical 481 :=
    placed agreement (position := 481) (by kernel_rfl)
  have p48 : physical (.BaseLayerMemory 69) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p499 : physical (.BaseLayerWitness 360) = logical 499 :=
    placed agreement (position := 499) (by kernel_rfl)
  have p501 : physical (.BaseLayerWitness 362) = logical 501 :=
    placed agreement (position := 501) (by kernel_rfl)
  simp only [operand194, NativeLookups.Input.fields, sourceFields194, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p481, p48, p499, p501]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement194 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup194).Contains (Verification.environment logical) ↔
      ∃ index, operand194.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields194 physical logical agreement]
  exact source_semantics194 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields195 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand195.input.fields physical = sourceFields195 logical := by
  have p482 : physical (.BaseLayerWitness 343) = logical 482 :=
    placed agreement (position := 482) (by kernel_rfl)
  have p498 : physical (.BaseLayerWitness 359) = logical 498 :=
    placed agreement (position := 498) (by kernel_rfl)
  have p47 : physical (.BaseLayerMemory 68) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
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
  have p250 : physical (.BaseLayerWitness 111) = logical 250 :=
    placed agreement (position := 250) (by kernel_rfl)
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
  have p477 : physical (.BaseLayerWitness 338) = logical 477 :=
    placed agreement (position := 477) (by kernel_rfl)
  have p495 : physical (.BaseLayerWitness 356) = logical 495 :=
    placed agreement (position := 495) (by kernel_rfl)
  have p496 : physical (.BaseLayerWitness 357) = logical 496 :=
    placed agreement (position := 496) (by kernel_rfl)
  have p92 : physical (.BaseLayerMemory 135) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p501 : physical (.BaseLayerWitness 362) = logical 501 :=
    placed agreement (position := 501) (by kernel_rfl)
  simp only [operand195, NativeLookups.Input.fields, sourceFields195, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p482, p498, p47, p163, p179, p232, p234, p248, p250, p337, p357, p358, p361, p412, p415, p477, p495, p496, p92, p501]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement195 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup195).Contains (Verification.environment logical) ↔
      ∃ index, operand195.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields195 physical logical agreement]
  exact source_semantics195 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields196 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand196.input.fields physical = sourceFields196 logical := by
  have p480 : physical (.BaseLayerWitness 341) = logical 480 :=
    placed agreement (position := 480) (by kernel_rfl)
  have p499 : physical (.BaseLayerWitness 360) = logical 499 :=
    placed agreement (position := 499) (by kernel_rfl)
  have p47 : physical (.BaseLayerMemory 68) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p48 : physical (.BaseLayerMemory 69) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p163 : physical (.BaseLayerWitness 24) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  have p165 : physical (.BaseLayerWitness 26) = logical 165 :=
    placed agreement (position := 165) (by kernel_rfl)
  have p179 : physical (.BaseLayerWitness 40) = logical 179 :=
    placed agreement (position := 179) (by kernel_rfl)
  have p181 : physical (.BaseLayerWitness 42) = logical 181 :=
    placed agreement (position := 181) (by kernel_rfl)
  have p232 : physical (.BaseLayerWitness 93) = logical 232 :=
    placed agreement (position := 232) (by kernel_rfl)
  have p233 : physical (.BaseLayerWitness 94) = logical 233 :=
    placed agreement (position := 233) (by kernel_rfl)
  have p234 : physical (.BaseLayerWitness 95) = logical 234 :=
    placed agreement (position := 234) (by kernel_rfl)
  have p235 : physical (.BaseLayerWitness 96) = logical 235 :=
    placed agreement (position := 235) (by kernel_rfl)
  have p248 : physical (.BaseLayerWitness 109) = logical 248 :=
    placed agreement (position := 248) (by kernel_rfl)
  have p249 : physical (.BaseLayerWitness 110) = logical 249 :=
    placed agreement (position := 249) (by kernel_rfl)
  have p250 : physical (.BaseLayerWitness 111) = logical 250 :=
    placed agreement (position := 250) (by kernel_rfl)
  have p251 : physical (.BaseLayerWitness 112) = logical 251 :=
    placed agreement (position := 251) (by kernel_rfl)
  have p339 : physical (.BaseLayerWitness 200) = logical 339 :=
    placed agreement (position := 339) (by kernel_rfl)
  have p356 : physical (.BaseLayerWitness 217) = logical 356 :=
    placed agreement (position := 356) (by kernel_rfl)
  have p357 : physical (.BaseLayerWitness 218) = logical 357 :=
    placed agreement (position := 357) (by kernel_rfl)
  have p358 : physical (.BaseLayerWitness 219) = logical 358 :=
    placed agreement (position := 358) (by kernel_rfl)
  have p359 : physical (.BaseLayerWitness 220) = logical 359 :=
    placed agreement (position := 359) (by kernel_rfl)
  have p363 : physical (.BaseLayerWitness 224) = logical 363 :=
    placed agreement (position := 363) (by kernel_rfl)
  have p412 : physical (.BaseLayerWitness 273) = logical 412 :=
    placed agreement (position := 412) (by kernel_rfl)
  have p413 : physical (.BaseLayerWitness 274) = logical 413 :=
    placed agreement (position := 413) (by kernel_rfl)
  have p414 : physical (.BaseLayerWitness 275) = logical 414 :=
    placed agreement (position := 414) (by kernel_rfl)
  have p415 : physical (.BaseLayerWitness 276) = logical 415 :=
    placed agreement (position := 415) (by kernel_rfl)
  have p479 : physical (.BaseLayerWitness 340) = logical 479 :=
    placed agreement (position := 479) (by kernel_rfl)
  have p494 : physical (.BaseLayerWitness 355) = logical 494 :=
    placed agreement (position := 494) (by kernel_rfl)
  have p495 : physical (.BaseLayerWitness 356) = logical 495 :=
    placed agreement (position := 495) (by kernel_rfl)
  have p496 : physical (.BaseLayerWitness 357) = logical 496 :=
    placed agreement (position := 496) (by kernel_rfl)
  have p497 : physical (.BaseLayerWitness 358) = logical 497 :=
    placed agreement (position := 497) (by kernel_rfl)
  have p91 : physical (.BaseLayerMemory 134) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p500 : physical (.BaseLayerWitness 361) = logical 500 :=
    placed agreement (position := 500) (by kernel_rfl)
  simp only [operand196, NativeLookups.Input.fields, sourceFields196, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p480, p499, p47, p48, p163, p165, p179, p181, p232, p233, p234, p235, p248, p249, p250, p251, p339, p356, p357, p358, p359, p363, p412, p413, p414, p415, p479, p494, p495, p496, p497, p91, p500]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement196 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup196).Contains (Verification.environment logical) ↔
      ∃ index, operand196.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields196 physical logical agreement]
  exact source_semantics196 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields197 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand197.input.fields physical = sourceFields197 logical := by
  have p495 : physical (.BaseLayerWitness 356) = logical 495 :=
    placed agreement (position := 495) (by kernel_rfl)
  have p71 : physical (.BaseLayerMemory 104) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p502 : physical (.BaseLayerWitness 363) = logical 502 :=
    placed agreement (position := 502) (by kernel_rfl)
  have p504 : physical (.BaseLayerWitness 365) = logical 504 :=
    placed agreement (position := 504) (by kernel_rfl)
  simp only [operand197, NativeLookups.Input.fields, sourceFields197, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p495, p71, p502, p504]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement197 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup197).Contains (Verification.environment logical) ↔
      ∃ index, operand197.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields197 physical logical agreement]
  exact source_semantics197 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields198 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand198.input.fields physical = sourceFields198 logical := by
  have p494 : physical (.BaseLayerWitness 355) = logical 494 :=
    placed agreement (position := 494) (by kernel_rfl)
  have p72 : physical (.BaseLayerMemory 105) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p503 : physical (.BaseLayerWitness 364) = logical 503 :=
    placed agreement (position := 503) (by kernel_rfl)
  have p505 : physical (.BaseLayerWitness 366) = logical 505 :=
    placed agreement (position := 505) (by kernel_rfl)
  simp only [operand198, NativeLookups.Input.fields, sourceFields198, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p494, p72, p503, p505]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement198 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup198).Contains (Verification.environment logical) ↔
      ∃ index, operand198.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields198 physical logical agreement]
  exact source_semantics198 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields199 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand199.input.fields physical = sourceFields199 logical := by
  have p496 : physical (.BaseLayerWitness 357) = logical 496 :=
    placed agreement (position := 496) (by kernel_rfl)
  have p502 : physical (.BaseLayerWitness 363) = logical 502 :=
    placed agreement (position := 502) (by kernel_rfl)
  have p71 : physical (.BaseLayerMemory 104) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p91 : physical (.BaseLayerMemory 134) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
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
  have p486 : physical (.BaseLayerWitness 347) = logical 486 :=
    placed agreement (position := 486) (by kernel_rfl)
  have p68 : physical (.BaseLayerMemory 99) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p505 : physical (.BaseLayerWitness 366) = logical 505 :=
    placed agreement (position := 505) (by kernel_rfl)
  simp only [operand199, NativeLookups.Input.fields, sourceFields199, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p496, p502, p71, p91, p186, p264, p265, p268, p284, p287, p289, p482, p483, p486, p68, p505]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement199 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup199).Contains (Verification.environment logical) ↔
      ∃ index, operand199.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields199 physical logical agreement]
  exact source_semantics199 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
