module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries013

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields160 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand160.input.fields physical = sourceFields160 logical := by
  have p333 : physical (.BaseLayerWitness 194) = logical 333 :=
    placed agreement (position := 333) (by kernel_rfl)
  have p334 : physical (.BaseLayerWitness 195) = logical 334 :=
    placed agreement (position := 334) (by kernel_rfl)
  have p432 : physical (.BaseLayerWitness 293) = logical 432 :=
    placed agreement (position := 432) (by kernel_rfl)
  have p433 : physical (.BaseLayerWitness 294) = logical 433 :=
    placed agreement (position := 433) (by kernel_rfl)
  have p430 : physical (.BaseLayerWitness 291) = logical 430 :=
    placed agreement (position := 430) (by kernel_rfl)
  have p191 : physical (.BaseLayerWitness 52) = logical 191 :=
    placed agreement (position := 191) (by kernel_rfl)
  have p342 : physical (.BaseLayerWitness 203) = logical 342 :=
    placed agreement (position := 342) (by kernel_rfl)
  have p343 : physical (.BaseLayerWitness 204) = logical 343 :=
    placed agreement (position := 343) (by kernel_rfl)
  have p348 : physical (.BaseLayerWitness 209) = logical 348 :=
    placed agreement (position := 348) (by kernel_rfl)
  have p351 : physical (.BaseLayerWitness 212) = logical 351 :=
    placed agreement (position := 351) (by kernel_rfl)
  have p365 : physical (.BaseLayerWitness 226) = logical 365 :=
    placed agreement (position := 365) (by kernel_rfl)
  have p366 : physical (.BaseLayerWitness 227) = logical 366 :=
    placed agreement (position := 366) (by kernel_rfl)
  have p369 : physical (.BaseLayerWitness 230) = logical 369 :=
    placed agreement (position := 369) (by kernel_rfl)
  have p371 : physical (.BaseLayerWitness 232) = logical 371 :=
    placed agreement (position := 371) (by kernel_rfl)
  have p420 : physical (.BaseLayerWitness 281) = logical 420 :=
    placed agreement (position := 420) (by kernel_rfl)
  have p421 : physical (.BaseLayerWitness 282) = logical 421 :=
    placed agreement (position := 421) (by kernel_rfl)
  have p426 : physical (.BaseLayerWitness 287) = logical 426 :=
    placed agreement (position := 426) (by kernel_rfl)
  have p427 : physical (.BaseLayerWitness 288) = logical 427 :=
    placed agreement (position := 427) (by kernel_rfl)
  have p428 : physical (.BaseLayerWitness 289) = logical 428 :=
    placed agreement (position := 428) (by kernel_rfl)
  have p429 : physical (.BaseLayerWitness 290) = logical 429 :=
    placed agreement (position := 429) (by kernel_rfl)
  have p424 : physical (.BaseLayerWitness 285) = logical 424 :=
    placed agreement (position := 424) (by kernel_rfl)
  have p437 : physical (.BaseLayerWitness 298) = logical 437 :=
    placed agreement (position := 437) (by kernel_rfl)
  simp only [operand160, NativeLookups.Input.fields, sourceFields160, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p333, p334, p432, p433, p430, p191, p342, p343, p348, p351, p365, p366, p369, p371, p420, p421, p426, p427, p428, p429, p424, p437]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement160 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup160).Contains (Verification.environment logical) ↔
      ∃ index, operand160.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields160 physical logical agreement]
  exact source_semantics160 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields161 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand161.input.fields physical = sourceFields161 logical := by
  have p423 : physical (.BaseLayerWitness 284) = logical 423 :=
    placed agreement (position := 423) (by kernel_rfl)
  have p39 : physical (.BaseLayerMemory 56) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p438 : physical (.BaseLayerWitness 299) = logical 438 :=
    placed agreement (position := 438) (by kernel_rfl)
  have p440 : physical (.BaseLayerWitness 301) = logical 440 :=
    placed agreement (position := 440) (by kernel_rfl)
  simp only [operand161, NativeLookups.Input.fields, sourceFields161, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p423, p39, p438, p440]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement161 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup161).Contains (Verification.environment logical) ↔
      ∃ index, operand161.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields161 physical logical agreement]
  exact source_semantics161 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields162 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand162.input.fields physical = sourceFields162 logical := by
  have p421 : physical (.BaseLayerWitness 282) = logical 421 :=
    placed agreement (position := 421) (by kernel_rfl)
  have p40 : physical (.BaseLayerMemory 57) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p439 : physical (.BaseLayerWitness 300) = logical 439 :=
    placed agreement (position := 439) (by kernel_rfl)
  have p441 : physical (.BaseLayerWitness 302) = logical 441 :=
    placed agreement (position := 441) (by kernel_rfl)
  simp only [operand162, NativeLookups.Input.fields, sourceFields162, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p421, p40, p439, p441]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement162 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup162).Contains (Verification.environment logical) ↔
      ∃ index, operand162.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields162 physical logical agreement]
  exact source_semantics162 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields163 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand163.input.fields physical = sourceFields163 logical := by
  have p422 : physical (.BaseLayerWitness 283) = logical 422 :=
    placed agreement (position := 422) (by kernel_rfl)
  have p438 : physical (.BaseLayerWitness 299) = logical 438 :=
    placed agreement (position := 438) (by kernel_rfl)
  have p39 : physical (.BaseLayerMemory 56) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p155 : physical (.BaseLayerWitness 16) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  have p171 : physical (.BaseLayerWitness 32) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  have p224 : physical (.BaseLayerWitness 85) = logical 224 :=
    placed agreement (position := 224) (by kernel_rfl)
  have p226 : physical (.BaseLayerWitness 87) = logical 226 :=
    placed agreement (position := 226) (by kernel_rfl)
  have p240 : physical (.BaseLayerWitness 101) = logical 240 :=
    placed agreement (position := 240) (by kernel_rfl)
  have p242 : physical (.BaseLayerWitness 103) = logical 242 :=
    placed agreement (position := 242) (by kernel_rfl)
  have p257 : physical (.BaseLayerWitness 118) = logical 257 :=
    placed agreement (position := 257) (by kernel_rfl)
  have p277 : physical (.BaseLayerWitness 138) = logical 277 :=
    placed agreement (position := 277) (by kernel_rfl)
  have p278 : physical (.BaseLayerWitness 139) = logical 278 :=
    placed agreement (position := 278) (by kernel_rfl)
  have p281 : physical (.BaseLayerWitness 142) = logical 281 :=
    placed agreement (position := 281) (by kernel_rfl)
  have p332 : physical (.BaseLayerWitness 193) = logical 332 :=
    placed agreement (position := 332) (by kernel_rfl)
  have p335 : physical (.BaseLayerWitness 196) = logical 335 :=
    placed agreement (position := 335) (by kernel_rfl)
  have p417 : physical (.BaseLayerWitness 278) = logical 417 :=
    placed agreement (position := 417) (by kernel_rfl)
  have p435 : physical (.BaseLayerWitness 296) = logical 435 :=
    placed agreement (position := 435) (by kernel_rfl)
  have p436 : physical (.BaseLayerWitness 297) = logical 436 :=
    placed agreement (position := 436) (by kernel_rfl)
  have p100 : physical (.BaseLayerMemory 147) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  have p441 : physical (.BaseLayerWitness 302) = logical 441 :=
    placed agreement (position := 441) (by kernel_rfl)
  simp only [operand163, NativeLookups.Input.fields, sourceFields163, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p422, p438, p39, p155, p171, p224, p226, p240, p242, p257, p277, p278, p281, p332, p335, p417, p435, p436, p100, p441]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement163 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup163).Contains (Verification.environment logical) ↔
      ∃ index, operand163.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields163 physical logical agreement]
  exact source_semantics163 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields164 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand164.input.fields physical = sourceFields164 logical := by
  have p420 : physical (.BaseLayerWitness 281) = logical 420 :=
    placed agreement (position := 420) (by kernel_rfl)
  have p439 : physical (.BaseLayerWitness 300) = logical 439 :=
    placed agreement (position := 439) (by kernel_rfl)
  have p39 : physical (.BaseLayerMemory 56) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p40 : physical (.BaseLayerMemory 57) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p155 : physical (.BaseLayerWitness 16) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  have p157 : physical (.BaseLayerWitness 18) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p171 : physical (.BaseLayerWitness 32) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  have p173 : physical (.BaseLayerWitness 34) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  have p224 : physical (.BaseLayerWitness 85) = logical 224 :=
    placed agreement (position := 224) (by kernel_rfl)
  have p225 : physical (.BaseLayerWitness 86) = logical 225 :=
    placed agreement (position := 225) (by kernel_rfl)
  have p226 : physical (.BaseLayerWitness 87) = logical 226 :=
    placed agreement (position := 226) (by kernel_rfl)
  have p227 : physical (.BaseLayerWitness 88) = logical 227 :=
    placed agreement (position := 227) (by kernel_rfl)
  have p240 : physical (.BaseLayerWitness 101) = logical 240 :=
    placed agreement (position := 240) (by kernel_rfl)
  have p241 : physical (.BaseLayerWitness 102) = logical 241 :=
    placed agreement (position := 241) (by kernel_rfl)
  have p242 : physical (.BaseLayerWitness 103) = logical 242 :=
    placed agreement (position := 242) (by kernel_rfl)
  have p243 : physical (.BaseLayerWitness 104) = logical 243 :=
    placed agreement (position := 243) (by kernel_rfl)
  have p259 : physical (.BaseLayerWitness 120) = logical 259 :=
    placed agreement (position := 259) (by kernel_rfl)
  have p276 : physical (.BaseLayerWitness 137) = logical 276 :=
    placed agreement (position := 276) (by kernel_rfl)
  have p277 : physical (.BaseLayerWitness 138) = logical 277 :=
    placed agreement (position := 277) (by kernel_rfl)
  have p278 : physical (.BaseLayerWitness 139) = logical 278 :=
    placed agreement (position := 278) (by kernel_rfl)
  have p279 : physical (.BaseLayerWitness 140) = logical 279 :=
    placed agreement (position := 279) (by kernel_rfl)
  have p283 : physical (.BaseLayerWitness 144) = logical 283 :=
    placed agreement (position := 283) (by kernel_rfl)
  have p332 : physical (.BaseLayerWitness 193) = logical 332 :=
    placed agreement (position := 332) (by kernel_rfl)
  have p333 : physical (.BaseLayerWitness 194) = logical 333 :=
    placed agreement (position := 333) (by kernel_rfl)
  have p334 : physical (.BaseLayerWitness 195) = logical 334 :=
    placed agreement (position := 334) (by kernel_rfl)
  have p335 : physical (.BaseLayerWitness 196) = logical 335 :=
    placed agreement (position := 335) (by kernel_rfl)
  have p419 : physical (.BaseLayerWitness 280) = logical 419 :=
    placed agreement (position := 419) (by kernel_rfl)
  have p434 : physical (.BaseLayerWitness 295) = logical 434 :=
    placed agreement (position := 434) (by kernel_rfl)
  have p435 : physical (.BaseLayerWitness 296) = logical 435 :=
    placed agreement (position := 435) (by kernel_rfl)
  have p436 : physical (.BaseLayerWitness 297) = logical 436 :=
    placed agreement (position := 436) (by kernel_rfl)
  have p437 : physical (.BaseLayerWitness 298) = logical 437 :=
    placed agreement (position := 437) (by kernel_rfl)
  have p99 : physical (.BaseLayerMemory 146) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p440 : physical (.BaseLayerWitness 301) = logical 440 :=
    placed agreement (position := 440) (by kernel_rfl)
  simp only [operand164, NativeLookups.Input.fields, sourceFields164, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p420, p439, p39, p40, p155, p157, p171, p173, p224, p225, p226, p227, p240, p241, p242, p243, p259, p276, p277, p278, p279, p283, p332, p333, p334, p335, p419, p434, p435, p436, p437, p99, p440]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement164 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup164).Contains (Verification.environment logical) ↔
      ∃ index, operand164.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields164 physical logical agreement]
  exact source_semantics164 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields165 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand165.input.fields physical = sourceFields165 logical := by
  have p435 : physical (.BaseLayerWitness 296) = logical 435 :=
    placed agreement (position := 435) (by kernel_rfl)
  have p79 : physical (.BaseLayerMemory 116) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p442 : physical (.BaseLayerWitness 303) = logical 442 :=
    placed agreement (position := 442) (by kernel_rfl)
  have p444 : physical (.BaseLayerWitness 305) = logical 444 :=
    placed agreement (position := 444) (by kernel_rfl)
  simp only [operand165, NativeLookups.Input.fields, sourceFields165, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p435, p79, p442, p444]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement165 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup165).Contains (Verification.environment logical) ↔
      ∃ index, operand165.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields165 physical logical agreement]
  exact source_semantics165 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields166 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand166.input.fields physical = sourceFields166 logical := by
  have p434 : physical (.BaseLayerWitness 295) = logical 434 :=
    placed agreement (position := 434) (by kernel_rfl)
  have p80 : physical (.BaseLayerMemory 117) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p443 : physical (.BaseLayerWitness 304) = logical 443 :=
    placed agreement (position := 443) (by kernel_rfl)
  have p445 : physical (.BaseLayerWitness 306) = logical 445 :=
    placed agreement (position := 445) (by kernel_rfl)
  simp only [operand166, NativeLookups.Input.fields, sourceFields166, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p434, p80, p443, p445]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement166 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup166).Contains (Verification.environment logical) ↔
      ∃ index, operand166.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields166 physical logical agreement]
  exact source_semantics166 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields167 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand167.input.fields physical = sourceFields167 logical := by
  have p436 : physical (.BaseLayerWitness 297) = logical 436 :=
    placed agreement (position := 436) (by kernel_rfl)
  have p442 : physical (.BaseLayerWitness 303) = logical 442 :=
    placed agreement (position := 442) (by kernel_rfl)
  have p79 : physical (.BaseLayerMemory 116) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p99 : physical (.BaseLayerMemory 146) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p190 : physical (.BaseLayerWitness 51) = logical 190 :=
    placed agreement (position := 190) (by kernel_rfl)
  have p344 : physical (.BaseLayerWitness 205) = logical 344 :=
    placed agreement (position := 344) (by kernel_rfl)
  have p345 : physical (.BaseLayerWitness 206) = logical 345 :=
    placed agreement (position := 345) (by kernel_rfl)
  have p348 : physical (.BaseLayerWitness 209) = logical 348 :=
    placed agreement (position := 348) (by kernel_rfl)
  have p364 : physical (.BaseLayerWitness 225) = logical 364 :=
    placed agreement (position := 364) (by kernel_rfl)
  have p367 : physical (.BaseLayerWitness 228) = logical 367 :=
    placed agreement (position := 367) (by kernel_rfl)
  have p369 : physical (.BaseLayerWitness 230) = logical 369 :=
    placed agreement (position := 369) (by kernel_rfl)
  have p422 : physical (.BaseLayerWitness 283) = logical 422 :=
    placed agreement (position := 422) (by kernel_rfl)
  have p423 : physical (.BaseLayerWitness 284) = logical 423 :=
    placed agreement (position := 423) (by kernel_rfl)
  have p426 : physical (.BaseLayerWitness 287) = logical 426 :=
    placed agreement (position := 426) (by kernel_rfl)
  have p60 : physical (.BaseLayerMemory 87) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p445 : physical (.BaseLayerWitness 306) = logical 445 :=
    placed agreement (position := 445) (by kernel_rfl)
  simp only [operand167, NativeLookups.Input.fields, sourceFields167, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p436, p442, p79, p99, p190, p344, p345, p348, p364, p367, p369, p422, p423, p426, p60, p445]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement167 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup167).Contains (Verification.environment logical) ↔
      ∃ index, operand167.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields167 physical logical agreement]
  exact source_semantics167 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
