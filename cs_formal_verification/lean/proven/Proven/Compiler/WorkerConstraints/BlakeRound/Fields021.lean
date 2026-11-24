module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries014

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields168 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand168.input.fields physical = sourceFields168 logical := by
  have p437 : physical (.BaseLayerWitness 298) = logical 437 :=
    placed agreement (position := 437) (by kernel_rfl)
  have p443 : physical (.BaseLayerWitness 304) = logical 443 :=
    placed agreement (position := 443) (by kernel_rfl)
  have p79 : physical (.BaseLayerMemory 116) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p80 : physical (.BaseLayerMemory 117) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p99 : physical (.BaseLayerMemory 146) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p100 : physical (.BaseLayerMemory 147) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  have p190 : physical (.BaseLayerWitness 51) = logical 190 :=
    placed agreement (position := 190) (by kernel_rfl)
  have p191 : physical (.BaseLayerWitness 52) = logical 191 :=
    placed agreement (position := 191) (by kernel_rfl)
  have p342 : physical (.BaseLayerWitness 203) = logical 342 :=
    placed agreement (position := 342) (by kernel_rfl)
  have p343 : physical (.BaseLayerWitness 204) = logical 343 :=
    placed agreement (position := 343) (by kernel_rfl)
  have p344 : physical (.BaseLayerWitness 205) = logical 344 :=
    placed agreement (position := 344) (by kernel_rfl)
  have p345 : physical (.BaseLayerWitness 206) = logical 345 :=
    placed agreement (position := 345) (by kernel_rfl)
  have p351 : physical (.BaseLayerWitness 212) = logical 351 :=
    placed agreement (position := 351) (by kernel_rfl)
  have p364 : physical (.BaseLayerWitness 225) = logical 364 :=
    placed agreement (position := 364) (by kernel_rfl)
  have p365 : physical (.BaseLayerWitness 226) = logical 365 :=
    placed agreement (position := 365) (by kernel_rfl)
  have p366 : physical (.BaseLayerWitness 227) = logical 366 :=
    placed agreement (position := 366) (by kernel_rfl)
  have p367 : physical (.BaseLayerWitness 228) = logical 367 :=
    placed agreement (position := 367) (by kernel_rfl)
  have p371 : physical (.BaseLayerWitness 232) = logical 371 :=
    placed agreement (position := 371) (by kernel_rfl)
  have p420 : physical (.BaseLayerWitness 281) = logical 420 :=
    placed agreement (position := 420) (by kernel_rfl)
  have p421 : physical (.BaseLayerWitness 282) = logical 421 :=
    placed agreement (position := 421) (by kernel_rfl)
  have p422 : physical (.BaseLayerWitness 283) = logical 422 :=
    placed agreement (position := 422) (by kernel_rfl)
  have p423 : physical (.BaseLayerWitness 284) = logical 423 :=
    placed agreement (position := 423) (by kernel_rfl)
  have p429 : physical (.BaseLayerWitness 290) = logical 429 :=
    placed agreement (position := 429) (by kernel_rfl)
  have p59 : physical (.BaseLayerMemory 86) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p444 : physical (.BaseLayerWitness 305) = logical 444 :=
    placed agreement (position := 444) (by kernel_rfl)
  simp only [operand168, NativeLookups.Input.fields, sourceFields168, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p437, p443, p79, p80, p99, p100, p190, p191, p342, p343, p344, p345, p351, p364, p365, p366, p367, p371, p420, p421, p422, p423, p429, p59, p444]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement168 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup168).Contains (Verification.environment logical) ↔
      ∃ index, operand168.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields168 physical logical agreement]
  exact source_semantics168 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields169 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand169.input.fields physical = sourceFields169 logical := by
  have p284 : physical (.BaseLayerWitness 145) = logical 284 :=
    placed agreement (position := 284) (by kernel_rfl)
  have p446 : physical (.BaseLayerWitness 307) = logical 446 :=
    placed agreement (position := 446) (by kernel_rfl)
  have p447 : physical (.BaseLayerWitness 308) = logical 447 :=
    placed agreement (position := 447) (by kernel_rfl)
  have p450 : physical (.BaseLayerWitness 311) = logical 450 :=
    placed agreement (position := 450) (by kernel_rfl)
  simp only [operand169, NativeLookups.Input.fields, sourceFields169, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p284, p446, p447, p450]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement169 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup169).Contains (Verification.environment logical) ↔
      ∃ index, operand169.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields169 physical logical agreement]
  exact source_semantics169 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields170 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand170.input.fields physical = sourceFields170 logical := by
  have p287 : physical (.BaseLayerWitness 148) = logical 287 :=
    placed agreement (position := 287) (by kernel_rfl)
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
  have p446 : physical (.BaseLayerWitness 307) = logical 446 :=
    placed agreement (position := 446) (by kernel_rfl)
  have p447 : physical (.BaseLayerWitness 308) = logical 447 :=
    placed agreement (position := 447) (by kernel_rfl)
  have p451 : physical (.BaseLayerWitness 312) = logical 451 :=
    placed agreement (position := 451) (by kernel_rfl)
  simp only [operand170, NativeLookups.Input.fields, sourceFields170, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p287, p159, p175, p228, p230, p244, p297, p317, p318, p321, p372, p375, p446, p447, p451]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement170 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup170).Contains (Verification.environment logical) ↔
      ∃ index, operand170.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields170 physical logical agreement]
  exact source_semantics170 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields171 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand171.input.fields physical = sourceFields171 logical := by
  have p285 : physical (.BaseLayerWitness 146) = logical 285 :=
    placed agreement (position := 285) (by kernel_rfl)
  have p448 : physical (.BaseLayerWitness 309) = logical 448 :=
    placed agreement (position := 448) (by kernel_rfl)
  have p449 : physical (.BaseLayerWitness 310) = logical 449 :=
    placed agreement (position := 449) (by kernel_rfl)
  have p452 : physical (.BaseLayerWitness 313) = logical 452 :=
    placed agreement (position := 452) (by kernel_rfl)
  simp only [operand171, NativeLookups.Input.fields, sourceFields171, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p285, p448, p449, p452]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement171 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup171).Contains (Verification.environment logical) ↔
      ∃ index, operand171.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields171 physical logical agreement]
  exact source_semantics171 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields172 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand172.input.fields physical = sourceFields172 logical := by
  have p286 : physical (.BaseLayerWitness 147) = logical 286 :=
    placed agreement (position := 286) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 22) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  have p177 : physical (.BaseLayerWitness 38) = logical 177 :=
    placed agreement (position := 177) (by kernel_rfl)
  have p229 : physical (.BaseLayerWitness 90) = logical 229 :=
    placed agreement (position := 229) (by kernel_rfl)
  have p231 : physical (.BaseLayerWitness 92) = logical 231 :=
    placed agreement (position := 231) (by kernel_rfl)
  have p245 : physical (.BaseLayerWitness 106) = logical 245 :=
    placed agreement (position := 245) (by kernel_rfl)
  have p297 : physical (.BaseLayerWitness 158) = logical 297 :=
    placed agreement (position := 297) (by kernel_rfl)
  have p299 : physical (.BaseLayerWitness 160) = logical 299 :=
    placed agreement (position := 299) (by kernel_rfl)
  have p316 : physical (.BaseLayerWitness 177) = logical 316 :=
    placed agreement (position := 316) (by kernel_rfl)
  have p319 : physical (.BaseLayerWitness 180) = logical 319 :=
    placed agreement (position := 319) (by kernel_rfl)
  have p321 : physical (.BaseLayerWitness 182) = logical 321 :=
    placed agreement (position := 321) (by kernel_rfl)
  have p323 : physical (.BaseLayerWitness 184) = logical 323 :=
    placed agreement (position := 323) (by kernel_rfl)
  have p373 : physical (.BaseLayerWitness 234) = logical 373 :=
    placed agreement (position := 373) (by kernel_rfl)
  have p374 : physical (.BaseLayerWitness 235) = logical 374 :=
    placed agreement (position := 374) (by kernel_rfl)
  have p447 : physical (.BaseLayerWitness 308) = logical 447 :=
    placed agreement (position := 447) (by kernel_rfl)
  have p448 : physical (.BaseLayerWitness 309) = logical 448 :=
    placed agreement (position := 448) (by kernel_rfl)
  have p449 : physical (.BaseLayerWitness 310) = logical 449 :=
    placed agreement (position := 449) (by kernel_rfl)
  have p453 : physical (.BaseLayerWitness 314) = logical 453 :=
    placed agreement (position := 453) (by kernel_rfl)
  simp only [operand172, NativeLookups.Input.fields, sourceFields172, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p286, p161, p177, p229, p231, p245, p297, p299, p316, p319, p321, p323, p373, p374, p447, p448, p449, p453]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement172 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup172).Contains (Verification.environment logical) ↔
      ∃ index, operand172.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields172 physical logical agreement]
  exact source_semantics172 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields173 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand173.input.fields physical = sourceFields173 logical := by
  have p461 : physical (.BaseLayerWitness 322) = logical 461 :=
    placed agreement (position := 461) (by kernel_rfl)
  have p455 : physical (.BaseLayerWitness 316) = logical 455 :=
    placed agreement (position := 455) (by kernel_rfl)
  have p464 : physical (.BaseLayerWitness 325) = logical 464 :=
    placed agreement (position := 464) (by kernel_rfl)
  simp only [operand173, NativeLookups.Input.fields, sourceFields173, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p461, p455, p464]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement173 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup173).Contains (Verification.environment logical) ↔
      ∃ index, operand173.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields173 physical logical agreement]
  exact source_semantics173 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields174 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand174.input.fields physical = sourceFields174 logical := by
  have p463 : physical (.BaseLayerWitness 324) = logical 463 :=
    placed agreement (position := 463) (by kernel_rfl)
  have p458 : physical (.BaseLayerWitness 319) = logical 458 :=
    placed agreement (position := 458) (by kernel_rfl)
  have p465 : physical (.BaseLayerWitness 326) = logical 465 :=
    placed agreement (position := 465) (by kernel_rfl)
  simp only [operand174, NativeLookups.Input.fields, sourceFields174, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p463, p458, p465]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement174 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup174).Contains (Verification.environment logical) ↔
      ∃ index, operand174.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields174 physical logical agreement]
  exact source_semantics174 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields175 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand175.input.fields physical = sourceFields175 logical := by
  have p372 : physical (.BaseLayerWitness 233) = logical 372 :=
    placed agreement (position := 372) (by kernel_rfl)
  have p375 : physical (.BaseLayerWitness 236) = logical 375 :=
    placed agreement (position := 375) (by kernel_rfl)
  have p460 : physical (.BaseLayerWitness 321) = logical 460 :=
    placed agreement (position := 460) (by kernel_rfl)
  have p461 : physical (.BaseLayerWitness 322) = logical 461 :=
    placed agreement (position := 461) (by kernel_rfl)
  have p462 : physical (.BaseLayerWitness 323) = logical 462 :=
    placed agreement (position := 462) (by kernel_rfl)
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
  have p454 : physical (.BaseLayerWitness 315) = logical 454 :=
    placed agreement (position := 454) (by kernel_rfl)
  have p455 : physical (.BaseLayerWitness 316) = logical 455 :=
    placed agreement (position := 455) (by kernel_rfl)
  have p456 : physical (.BaseLayerWitness 317) = logical 456 :=
    placed agreement (position := 456) (by kernel_rfl)
  have p457 : physical (.BaseLayerWitness 318) = logical 457 :=
    placed agreement (position := 457) (by kernel_rfl)
  have p466 : physical (.BaseLayerWitness 327) = logical 466 :=
    placed agreement (position := 466) (by kernel_rfl)
  simp only [operand175, NativeLookups.Input.fields, sourceFields175, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p372, p375, p460, p461, p462, p192, p384, p385, p388, p404, p407, p409, p452, p453, p454, p455, p456, p457, p466]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement175 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup175).Contains (Verification.environment logical) ↔
      ∃ index, operand175.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields175 physical logical agreement]
  exact source_semantics175 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
