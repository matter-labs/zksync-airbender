module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries017

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields208 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand208.input.fields physical = sourceFields208 logical := by
  have p293 : physical (.BaseLayerWitness 154) = logical 293 :=
    placed agreement (position := 293) (by kernel_rfl)
  have p294 : physical (.BaseLayerWitness 155) = logical 294 :=
    placed agreement (position := 294) (by kernel_rfl)
  have p522 : physical (.BaseLayerWitness 383) = logical 522 :=
    placed agreement (position := 522) (by kernel_rfl)
  have p523 : physical (.BaseLayerWitness 384) = logical 523 :=
    placed agreement (position := 523) (by kernel_rfl)
  have p520 : physical (.BaseLayerWitness 381) = logical 520 :=
    placed agreement (position := 520) (by kernel_rfl)
  have p189 : physical (.BaseLayerWitness 50) = logical 189 :=
    placed agreement (position := 189) (by kernel_rfl)
  have p302 : physical (.BaseLayerWitness 163) = logical 302 :=
    placed agreement (position := 302) (by kernel_rfl)
  have p303 : physical (.BaseLayerWitness 164) = logical 303 :=
    placed agreement (position := 303) (by kernel_rfl)
  have p308 : physical (.BaseLayerWitness 169) = logical 308 :=
    placed agreement (position := 308) (by kernel_rfl)
  have p311 : physical (.BaseLayerWitness 172) = logical 311 :=
    placed agreement (position := 311) (by kernel_rfl)
  have p325 : physical (.BaseLayerWitness 186) = logical 325 :=
    placed agreement (position := 325) (by kernel_rfl)
  have p326 : physical (.BaseLayerWitness 187) = logical 326 :=
    placed agreement (position := 326) (by kernel_rfl)
  have p329 : physical (.BaseLayerWitness 190) = logical 329 :=
    placed agreement (position := 329) (by kernel_rfl)
  have p331 : physical (.BaseLayerWitness 192) = logical 331 :=
    placed agreement (position := 331) (by kernel_rfl)
  have p510 : physical (.BaseLayerWitness 371) = logical 510 :=
    placed agreement (position := 510) (by kernel_rfl)
  have p511 : physical (.BaseLayerWitness 372) = logical 511 :=
    placed agreement (position := 511) (by kernel_rfl)
  have p516 : physical (.BaseLayerWitness 377) = logical 516 :=
    placed agreement (position := 516) (by kernel_rfl)
  have p517 : physical (.BaseLayerWitness 378) = logical 517 :=
    placed agreement (position := 517) (by kernel_rfl)
  have p518 : physical (.BaseLayerWitness 379) = logical 518 :=
    placed agreement (position := 518) (by kernel_rfl)
  have p519 : physical (.BaseLayerWitness 380) = logical 519 :=
    placed agreement (position := 519) (by kernel_rfl)
  have p514 : physical (.BaseLayerWitness 375) = logical 514 :=
    placed agreement (position := 514) (by kernel_rfl)
  have p527 : physical (.BaseLayerWitness 388) = logical 527 :=
    placed agreement (position := 527) (by kernel_rfl)
  simp only [operand208, NativeLookups.Input.fields, sourceFields208, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p293, p294, p522, p523, p520, p189, p302, p303, p308, p311, p325, p326, p329, p331, p510, p511, p516, p517, p518, p519, p514, p527]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement208 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup208).Contains (Verification.environment logical) ↔
      ∃ index, operand208.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields208 physical logical agreement]
  exact source_semantics208 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields209 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand209.input.fields physical = sourceFields209 logical := by
  have p513 : physical (.BaseLayerWitness 374) = logical 513 :=
    placed agreement (position := 513) (by kernel_rfl)
  have p51 : physical (.BaseLayerMemory 74) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p528 : physical (.BaseLayerWitness 389) = logical 528 :=
    placed agreement (position := 528) (by kernel_rfl)
  have p530 : physical (.BaseLayerWitness 391) = logical 530 :=
    placed agreement (position := 530) (by kernel_rfl)
  simp only [operand209, NativeLookups.Input.fields, sourceFields209, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p513, p51, p528, p530]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement209 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup209).Contains (Verification.environment logical) ↔
      ∃ index, operand209.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields209 physical logical agreement]
  exact source_semantics209 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields210 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand210.input.fields physical = sourceFields210 logical := by
  have p511 : physical (.BaseLayerWitness 372) = logical 511 :=
    placed agreement (position := 511) (by kernel_rfl)
  have p52 : physical (.BaseLayerMemory 75) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p529 : physical (.BaseLayerWitness 390) = logical 529 :=
    placed agreement (position := 529) (by kernel_rfl)
  have p531 : physical (.BaseLayerWitness 392) = logical 531 :=
    placed agreement (position := 531) (by kernel_rfl)
  simp only [operand210, NativeLookups.Input.fields, sourceFields210, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p511, p52, p529, p531]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement210 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup210).Contains (Verification.environment logical) ↔
      ∃ index, operand210.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields210 physical logical agreement]
  exact source_semantics210 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields211 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand211.input.fields physical = sourceFields211 logical := by
  have p512 : physical (.BaseLayerWitness 373) = logical 512 :=
    placed agreement (position := 512) (by kernel_rfl)
  have p528 : physical (.BaseLayerWitness 389) = logical 528 :=
    placed agreement (position := 528) (by kernel_rfl)
  have p51 : physical (.BaseLayerMemory 74) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
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
  have p254 : physical (.BaseLayerWitness 115) = logical 254 :=
    placed agreement (position := 254) (by kernel_rfl)
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
  have p507 : physical (.BaseLayerWitness 368) = logical 507 :=
    placed agreement (position := 507) (by kernel_rfl)
  have p525 : physical (.BaseLayerWitness 386) = logical 525 :=
    placed agreement (position := 525) (by kernel_rfl)
  have p526 : physical (.BaseLayerWitness 387) = logical 526 :=
    placed agreement (position := 526) (by kernel_rfl)
  have p96 : physical (.BaseLayerMemory 141) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p531 : physical (.BaseLayerWitness 392) = logical 531 :=
    placed agreement (position := 531) (by kernel_rfl)
  simp only [operand211, NativeLookups.Input.fields, sourceFields211, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p512, p528, p51, p167, p183, p236, p238, p252, p254, p292, p295, p377, p397, p398, p401, p507, p525, p526, p96, p531]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement211 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup211).Contains (Verification.environment logical) ↔
      ∃ index, operand211.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields211 physical logical agreement]
  exact source_semantics211 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields212 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand212.input.fields physical = sourceFields212 logical := by
  have p510 : physical (.BaseLayerWitness 371) = logical 510 :=
    placed agreement (position := 510) (by kernel_rfl)
  have p529 : physical (.BaseLayerWitness 390) = logical 529 :=
    placed agreement (position := 529) (by kernel_rfl)
  have p51 : physical (.BaseLayerMemory 74) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p52 : physical (.BaseLayerMemory 75) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p167 : physical (.BaseLayerWitness 28) = logical 167 :=
    placed agreement (position := 167) (by kernel_rfl)
  have p169 : physical (.BaseLayerWitness 30) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  have p183 : physical (.BaseLayerWitness 44) = logical 183 :=
    placed agreement (position := 183) (by kernel_rfl)
  have p185 : physical (.BaseLayerWitness 46) = logical 185 :=
    placed agreement (position := 185) (by kernel_rfl)
  have p236 : physical (.BaseLayerWitness 97) = logical 236 :=
    placed agreement (position := 236) (by kernel_rfl)
  have p237 : physical (.BaseLayerWitness 98) = logical 237 :=
    placed agreement (position := 237) (by kernel_rfl)
  have p238 : physical (.BaseLayerWitness 99) = logical 238 :=
    placed agreement (position := 238) (by kernel_rfl)
  have p239 : physical (.BaseLayerWitness 100) = logical 239 :=
    placed agreement (position := 239) (by kernel_rfl)
  have p252 : physical (.BaseLayerWitness 113) = logical 252 :=
    placed agreement (position := 252) (by kernel_rfl)
  have p253 : physical (.BaseLayerWitness 114) = logical 253 :=
    placed agreement (position := 253) (by kernel_rfl)
  have p254 : physical (.BaseLayerWitness 115) = logical 254 :=
    placed agreement (position := 254) (by kernel_rfl)
  have p255 : physical (.BaseLayerWitness 116) = logical 255 :=
    placed agreement (position := 255) (by kernel_rfl)
  have p292 : physical (.BaseLayerWitness 153) = logical 292 :=
    placed agreement (position := 292) (by kernel_rfl)
  have p293 : physical (.BaseLayerWitness 154) = logical 293 :=
    placed agreement (position := 293) (by kernel_rfl)
  have p294 : physical (.BaseLayerWitness 155) = logical 294 :=
    placed agreement (position := 294) (by kernel_rfl)
  have p295 : physical (.BaseLayerWitness 156) = logical 295 :=
    placed agreement (position := 295) (by kernel_rfl)
  have p379 : physical (.BaseLayerWitness 240) = logical 379 :=
    placed agreement (position := 379) (by kernel_rfl)
  have p396 : physical (.BaseLayerWitness 257) = logical 396 :=
    placed agreement (position := 396) (by kernel_rfl)
  have p397 : physical (.BaseLayerWitness 258) = logical 397 :=
    placed agreement (position := 397) (by kernel_rfl)
  have p398 : physical (.BaseLayerWitness 259) = logical 398 :=
    placed agreement (position := 398) (by kernel_rfl)
  have p399 : physical (.BaseLayerWitness 260) = logical 399 :=
    placed agreement (position := 399) (by kernel_rfl)
  have p403 : physical (.BaseLayerWitness 264) = logical 403 :=
    placed agreement (position := 403) (by kernel_rfl)
  have p509 : physical (.BaseLayerWitness 370) = logical 509 :=
    placed agreement (position := 509) (by kernel_rfl)
  have p524 : physical (.BaseLayerWitness 385) = logical 524 :=
    placed agreement (position := 524) (by kernel_rfl)
  have p525 : physical (.BaseLayerWitness 386) = logical 525 :=
    placed agreement (position := 525) (by kernel_rfl)
  have p526 : physical (.BaseLayerWitness 387) = logical 526 :=
    placed agreement (position := 526) (by kernel_rfl)
  have p527 : physical (.BaseLayerWitness 388) = logical 527 :=
    placed agreement (position := 527) (by kernel_rfl)
  have p95 : physical (.BaseLayerMemory 140) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p530 : physical (.BaseLayerWitness 391) = logical 530 :=
    placed agreement (position := 530) (by kernel_rfl)
  simp only [operand212, NativeLookups.Input.fields, sourceFields212, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p510, p529, p51, p52, p167, p169, p183, p185, p236, p237, p238, p239, p252, p253, p254, p255, p292, p293, p294, p295, p379, p396, p397, p398, p399, p403, p509, p524, p525, p526, p527, p95, p530]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement212 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup212).Contains (Verification.environment logical) ↔
      ∃ index, operand212.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields212 physical logical agreement]
  exact source_semantics212 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields213 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand213.input.fields physical = sourceFields213 logical := by
  have p525 : physical (.BaseLayerWitness 386) = logical 525 :=
    placed agreement (position := 525) (by kernel_rfl)
  have p75 : physical (.BaseLayerMemory 110) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p532 : physical (.BaseLayerWitness 393) = logical 532 :=
    placed agreement (position := 532) (by kernel_rfl)
  have p534 : physical (.BaseLayerWitness 395) = logical 534 :=
    placed agreement (position := 534) (by kernel_rfl)
  simp only [operand213, NativeLookups.Input.fields, sourceFields213, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p525, p75, p532, p534]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement213 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup213).Contains (Verification.environment logical) ↔
      ∃ index, operand213.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields213 physical logical agreement]
  exact source_semantics213 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields214 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand214.input.fields physical = sourceFields214 logical := by
  have p524 : physical (.BaseLayerWitness 385) = logical 524 :=
    placed agreement (position := 524) (by kernel_rfl)
  have p76 : physical (.BaseLayerMemory 111) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p533 : physical (.BaseLayerWitness 394) = logical 533 :=
    placed agreement (position := 533) (by kernel_rfl)
  have p535 : physical (.BaseLayerWitness 396) = logical 535 :=
    placed agreement (position := 535) (by kernel_rfl)
  simp only [operand214, NativeLookups.Input.fields, sourceFields214, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p524, p76, p533, p535]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement214 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup214).Contains (Verification.environment logical) ↔
      ∃ index, operand214.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields214 physical logical agreement]
  exact source_semantics214 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields215 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand215.input.fields physical = sourceFields215 logical := by
  have p526 : physical (.BaseLayerWitness 387) = logical 526 :=
    placed agreement (position := 526) (by kernel_rfl)
  have p532 : physical (.BaseLayerWitness 393) = logical 532 :=
    placed agreement (position := 532) (by kernel_rfl)
  have p75 : physical (.BaseLayerMemory 110) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p95 : physical (.BaseLayerMemory 140) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
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
  have p516 : physical (.BaseLayerWitness 377) = logical 516 :=
    placed agreement (position := 516) (by kernel_rfl)
  have p56 : physical (.BaseLayerMemory 81) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p535 : physical (.BaseLayerWitness 396) = logical 535 :=
    placed agreement (position := 535) (by kernel_rfl)
  simp only [operand215, NativeLookups.Input.fields, sourceFields215, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p526, p532, p75, p95, p188, p304, p305, p308, p324, p327, p329, p512, p513, p516, p56, p535]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement215 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup215).Contains (Verification.environment logical) ↔
      ∃ index, operand215.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields215 physical logical agreement]
  exact source_semantics215 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
