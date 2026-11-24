module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries016
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries017

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields200 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand200.input.fields physical = sourceFields200 logical := by
  have p497 : physical (.BaseLayerWitness 358) = logical 497 :=
    placed agreement (position := 497) (by kernel_rfl)
  have p503 : physical (.BaseLayerWitness 364) = logical 503 :=
    placed agreement (position := 503) (by kernel_rfl)
  have p71 : physical (.BaseLayerMemory 104) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p72 : physical (.BaseLayerMemory 105) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p91 : physical (.BaseLayerMemory 134) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p92 : physical (.BaseLayerMemory 135) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p186 : physical (.BaseLayerWitness 47) = logical 186 :=
    placed agreement (position := 186) (by kernel_rfl)
  have p187 : physical (.BaseLayerWitness 48) = logical 187 :=
    placed agreement (position := 187) (by kernel_rfl)
  have p262 : physical (.BaseLayerWitness 123) = logical 262 :=
    placed agreement (position := 262) (by kernel_rfl)
  have p263 : physical (.BaseLayerWitness 124) = logical 263 :=
    placed agreement (position := 263) (by kernel_rfl)
  have p264 : physical (.BaseLayerWitness 125) = logical 264 :=
    placed agreement (position := 264) (by kernel_rfl)
  have p265 : physical (.BaseLayerWitness 126) = logical 265 :=
    placed agreement (position := 265) (by kernel_rfl)
  have p271 : physical (.BaseLayerWitness 132) = logical 271 :=
    placed agreement (position := 271) (by kernel_rfl)
  have p284 : physical (.BaseLayerWitness 145) = logical 284 :=
    placed agreement (position := 284) (by kernel_rfl)
  have p285 : physical (.BaseLayerWitness 146) = logical 285 :=
    placed agreement (position := 285) (by kernel_rfl)
  have p286 : physical (.BaseLayerWitness 147) = logical 286 :=
    placed agreement (position := 286) (by kernel_rfl)
  have p287 : physical (.BaseLayerWitness 148) = logical 287 :=
    placed agreement (position := 287) (by kernel_rfl)
  have p291 : physical (.BaseLayerWitness 152) = logical 291 :=
    placed agreement (position := 291) (by kernel_rfl)
  have p480 : physical (.BaseLayerWitness 341) = logical 480 :=
    placed agreement (position := 480) (by kernel_rfl)
  have p481 : physical (.BaseLayerWitness 342) = logical 481 :=
    placed agreement (position := 481) (by kernel_rfl)
  have p482 : physical (.BaseLayerWitness 343) = logical 482 :=
    placed agreement (position := 482) (by kernel_rfl)
  have p483 : physical (.BaseLayerWitness 344) = logical 483 :=
    placed agreement (position := 483) (by kernel_rfl)
  have p489 : physical (.BaseLayerWitness 350) = logical 489 :=
    placed agreement (position := 489) (by kernel_rfl)
  have p67 : physical (.BaseLayerMemory 98) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p504 : physical (.BaseLayerWitness 365) = logical 504 :=
    placed agreement (position := 504) (by kernel_rfl)
  simp only [operand200, NativeLookups.Input.fields, sourceFields200, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p497, p503, p71, p72, p91, p92, p186, p187, p262, p263, p264, p265, p271, p284, p285, p286, p287, p291, p480, p481, p482, p483, p489, p67, p504]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement200 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup200).Contains (Verification.environment logical) ↔
      ∃ index, operand200.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields200 physical logical agreement]
  exact source_semantics200 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields201 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand201.input.fields physical = sourceFields201 logical := by
  have p364 : physical (.BaseLayerWitness 225) = logical 364 :=
    placed agreement (position := 364) (by kernel_rfl)
  have p506 : physical (.BaseLayerWitness 367) = logical 506 :=
    placed agreement (position := 506) (by kernel_rfl)
  have p507 : physical (.BaseLayerWitness 368) = logical 507 :=
    placed agreement (position := 507) (by kernel_rfl)
  have p510 : physical (.BaseLayerWitness 371) = logical 510 :=
    placed agreement (position := 510) (by kernel_rfl)
  simp only [operand201, NativeLookups.Input.fields, sourceFields201, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p364, p506, p507, p510]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement201 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup201).Contains (Verification.environment logical) ↔
      ∃ index, operand201.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields201 physical logical agreement]
  exact source_semantics201 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields202 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand202.input.fields physical = sourceFields202 logical := by
  have p367 : physical (.BaseLayerWitness 228) = logical 367 :=
    placed agreement (position := 367) (by kernel_rfl)
  have p167 : physical (.BaseLayerWitness 28) = logical 167 :=
    placed agreement (position := 167) (by kernel_rfl)
  have p183 : physical (.BaseLayerWitness 44) = logical 183 :=
    placed agreement (position := 183) (by kernel_rfl)
  have p236 : physical (.BaseLayerWitness 97) = logical 236 :=
    placed agreement (position := 236) (by kernel_rfl)
  have p238 : physical (.BaseLayerWitness 99) = logical 238 :=
    placed agreement (position := 238) (by kernel_rfl)
  have p252 : physical (.BaseLayerWitness 113) = logical 252 :=
    placed agreement (position := 252) (by kernel_rfl)
  have p292 : physical (.BaseLayerWitness 153) = logical 292 :=
    placed agreement (position := 292) (by kernel_rfl)
  have p295 : physical (.BaseLayerWitness 156) = logical 295 :=
    placed agreement (position := 295) (by kernel_rfl)
  have p377 : physical (.BaseLayerWitness 238) = logical 377 :=
    placed agreement (position := 377) (by kernel_rfl)
  have p397 : physical (.BaseLayerWitness 258) = logical 397 :=
    placed agreement (position := 397) (by kernel_rfl)
  have p398 : physical (.BaseLayerWitness 259) = logical 398 :=
    placed agreement (position := 398) (by kernel_rfl)
  have p401 : physical (.BaseLayerWitness 262) = logical 401 :=
    placed agreement (position := 401) (by kernel_rfl)
  have p506 : physical (.BaseLayerWitness 367) = logical 506 :=
    placed agreement (position := 506) (by kernel_rfl)
  have p507 : physical (.BaseLayerWitness 368) = logical 507 :=
    placed agreement (position := 507) (by kernel_rfl)
  have p511 : physical (.BaseLayerWitness 372) = logical 511 :=
    placed agreement (position := 511) (by kernel_rfl)
  simp only [operand202, NativeLookups.Input.fields, sourceFields202, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p367, p167, p183, p236, p238, p252, p292, p295, p377, p397, p398, p401, p506, p507, p511]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement202 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup202).Contains (Verification.environment logical) ↔
      ∃ index, operand202.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields202 physical logical agreement]
  exact source_semantics202 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields203 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand203.input.fields physical = sourceFields203 logical := by
  have p365 : physical (.BaseLayerWitness 226) = logical 365 :=
    placed agreement (position := 365) (by kernel_rfl)
  have p508 : physical (.BaseLayerWitness 369) = logical 508 :=
    placed agreement (position := 508) (by kernel_rfl)
  have p509 : physical (.BaseLayerWitness 370) = logical 509 :=
    placed agreement (position := 509) (by kernel_rfl)
  have p512 : physical (.BaseLayerWitness 373) = logical 512 :=
    placed agreement (position := 512) (by kernel_rfl)
  simp only [operand203, NativeLookups.Input.fields, sourceFields203, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p365, p508, p509, p512]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement203 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup203).Contains (Verification.environment logical) ↔
      ∃ index, operand203.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields203 physical logical agreement]
  exact source_semantics203 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields204 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand204.input.fields physical = sourceFields204 logical := by
  have p366 : physical (.BaseLayerWitness 227) = logical 366 :=
    placed agreement (position := 366) (by kernel_rfl)
  have p169 : physical (.BaseLayerWitness 30) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  have p185 : physical (.BaseLayerWitness 46) = logical 185 :=
    placed agreement (position := 185) (by kernel_rfl)
  have p237 : physical (.BaseLayerWitness 98) = logical 237 :=
    placed agreement (position := 237) (by kernel_rfl)
  have p239 : physical (.BaseLayerWitness 100) = logical 239 :=
    placed agreement (position := 239) (by kernel_rfl)
  have p253 : physical (.BaseLayerWitness 114) = logical 253 :=
    placed agreement (position := 253) (by kernel_rfl)
  have p293 : physical (.BaseLayerWitness 154) = logical 293 :=
    placed agreement (position := 293) (by kernel_rfl)
  have p294 : physical (.BaseLayerWitness 155) = logical 294 :=
    placed agreement (position := 294) (by kernel_rfl)
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
  have p403 : physical (.BaseLayerWitness 264) = logical 403 :=
    placed agreement (position := 403) (by kernel_rfl)
  have p507 : physical (.BaseLayerWitness 368) = logical 507 :=
    placed agreement (position := 507) (by kernel_rfl)
  have p508 : physical (.BaseLayerWitness 369) = logical 508 :=
    placed agreement (position := 508) (by kernel_rfl)
  have p509 : physical (.BaseLayerWitness 370) = logical 509 :=
    placed agreement (position := 509) (by kernel_rfl)
  have p513 : physical (.BaseLayerWitness 374) = logical 513 :=
    placed agreement (position := 513) (by kernel_rfl)
  simp only [operand204, NativeLookups.Input.fields, sourceFields204, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p366, p169, p185, p237, p239, p253, p293, p294, p377, p379, p396, p399, p401, p403, p507, p508, p509, p513]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement204 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup204).Contains (Verification.environment logical) ↔
      ∃ index, operand204.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields204 physical logical agreement]
  exact source_semantics204 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields205 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand205.input.fields physical = sourceFields205 logical := by
  have p521 : physical (.BaseLayerWitness 382) = logical 521 :=
    placed agreement (position := 521) (by kernel_rfl)
  have p515 : physical (.BaseLayerWitness 376) = logical 515 :=
    placed agreement (position := 515) (by kernel_rfl)
  have p524 : physical (.BaseLayerWitness 385) = logical 524 :=
    placed agreement (position := 524) (by kernel_rfl)
  simp only [operand205, NativeLookups.Input.fields, sourceFields205, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p521, p515, p524]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement205 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup205).Contains (Verification.environment logical) ↔
      ∃ index, operand205.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields205 physical logical agreement]
  exact source_semantics205 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields206 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand206.input.fields physical = sourceFields206 logical := by
  have p523 : physical (.BaseLayerWitness 384) = logical 523 :=
    placed agreement (position := 523) (by kernel_rfl)
  have p518 : physical (.BaseLayerWitness 379) = logical 518 :=
    placed agreement (position := 518) (by kernel_rfl)
  have p525 : physical (.BaseLayerWitness 386) = logical 525 :=
    placed agreement (position := 525) (by kernel_rfl)
  simp only [operand206, NativeLookups.Input.fields, sourceFields206, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p523, p518, p525]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement206 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup206).Contains (Verification.environment logical) ↔
      ∃ index, operand206.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields206 physical logical agreement]
  exact source_semantics206 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields207 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand207.input.fields physical = sourceFields207 logical := by
  have p292 : physical (.BaseLayerWitness 153) = logical 292 :=
    placed agreement (position := 292) (by kernel_rfl)
  have p295 : physical (.BaseLayerWitness 156) = logical 295 :=
    placed agreement (position := 295) (by kernel_rfl)
  have p520 : physical (.BaseLayerWitness 381) = logical 520 :=
    placed agreement (position := 520) (by kernel_rfl)
  have p521 : physical (.BaseLayerWitness 382) = logical 521 :=
    placed agreement (position := 521) (by kernel_rfl)
  have p522 : physical (.BaseLayerWitness 383) = logical 522 :=
    placed agreement (position := 522) (by kernel_rfl)
  have p188 : physical (.BaseLayerWitness 49) = logical 188 :=
    placed agreement (position := 188) (by kernel_rfl)
  have p304 : physical (.BaseLayerWitness 165) = logical 304 :=
    placed agreement (position := 304) (by kernel_rfl)
  have p305 : physical (.BaseLayerWitness 166) = logical 305 :=
    placed agreement (position := 305) (by kernel_rfl)
  have p308 : physical (.BaseLayerWitness 169) = logical 308 :=
    placed agreement (position := 308) (by kernel_rfl)
  have p324 : physical (.BaseLayerWitness 185) = logical 324 :=
    placed agreement (position := 324) (by kernel_rfl)
  have p327 : physical (.BaseLayerWitness 188) = logical 327 :=
    placed agreement (position := 327) (by kernel_rfl)
  have p329 : physical (.BaseLayerWitness 190) = logical 329 :=
    placed agreement (position := 329) (by kernel_rfl)
  have p512 : physical (.BaseLayerWitness 373) = logical 512 :=
    placed agreement (position := 512) (by kernel_rfl)
  have p513 : physical (.BaseLayerWitness 374) = logical 513 :=
    placed agreement (position := 513) (by kernel_rfl)
  have p514 : physical (.BaseLayerWitness 375) = logical 514 :=
    placed agreement (position := 514) (by kernel_rfl)
  have p515 : physical (.BaseLayerWitness 376) = logical 515 :=
    placed agreement (position := 515) (by kernel_rfl)
  have p516 : physical (.BaseLayerWitness 377) = logical 516 :=
    placed agreement (position := 516) (by kernel_rfl)
  have p517 : physical (.BaseLayerWitness 378) = logical 517 :=
    placed agreement (position := 517) (by kernel_rfl)
  have p526 : physical (.BaseLayerWitness 387) = logical 526 :=
    placed agreement (position := 526) (by kernel_rfl)
  simp only [operand207, NativeLookups.Input.fields, sourceFields207, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p292, p295, p520, p521, p522, p188, p304, p305, p308, p324, p327, p329, p512, p513, p514, p515, p516, p517, p526]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement207 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup207).Contains (Verification.environment logical) ↔
      ∃ index, operand207.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields207 physical logical agreement]
  exact source_semantics207 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
