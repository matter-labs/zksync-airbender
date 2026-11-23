module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries012
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries013

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields152 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand152.input.fields physical = sourceFields152 logical := by
  have p399 : physical (.BaseLayerWitness 260) = logical 399 :=
    placed agreement (position := 399) (by kernel_rfl)
  have p410 : physical (.BaseLayerWitness 271) = logical 410 :=
    placed agreement (position := 410) (by kernel_rfl)
  have p415 : physical (.BaseLayerWitness 276) = logical 415 :=
    placed agreement (position := 415) (by kernel_rfl)
  simp only [operand152, NativeLookups.Input.fields, sourceFields152, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p399, p410, p415]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement152 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup152).Contains (Verification.environment logical) ↔
      ∃ index, operand152.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields152 physical logical agreement]
  exact source_semantics152 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields153 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand153.input.fields physical = sourceFields153 logical := by
  have p404 : physical (.BaseLayerWitness 265) = logical 404 :=
    placed agreement (position := 404) (by kernel_rfl)
  have p416 : physical (.BaseLayerWitness 277) = logical 416 :=
    placed agreement (position := 416) (by kernel_rfl)
  have p417 : physical (.BaseLayerWitness 278) = logical 417 :=
    placed agreement (position := 417) (by kernel_rfl)
  have p420 : physical (.BaseLayerWitness 281) = logical 420 :=
    placed agreement (position := 420) (by kernel_rfl)
  simp only [operand153, NativeLookups.Input.fields, sourceFields153, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p404, p416, p417, p420]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement153 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup153).Contains (Verification.environment logical) ↔
      ∃ index, operand153.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields153 physical logical agreement]
  exact source_semantics153 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields154 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand154.input.fields physical = sourceFields154 logical := by
  have p407 : physical (.BaseLayerWitness 268) = logical 407 :=
    placed agreement (position := 407) (by kernel_rfl)
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
  have p416 : physical (.BaseLayerWitness 277) = logical 416 :=
    placed agreement (position := 416) (by kernel_rfl)
  have p417 : physical (.BaseLayerWitness 278) = logical 417 :=
    placed agreement (position := 417) (by kernel_rfl)
  have p421 : physical (.BaseLayerWitness 282) = logical 421 :=
    placed agreement (position := 421) (by kernel_rfl)
  simp only [operand154, NativeLookups.Input.fields, sourceFields154, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p407, p155, p171, p224, p226, p240, p257, p277, p278, p281, p332, p335, p416, p417, p421]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement154 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup154).Contains (Verification.environment logical) ↔
      ∃ index, operand154.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields154 physical logical agreement]
  exact source_semantics154 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields155 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand155.input.fields physical = sourceFields155 logical := by
  have p405 : physical (.BaseLayerWitness 266) = logical 405 :=
    placed agreement (position := 405) (by kernel_rfl)
  have p418 : physical (.BaseLayerWitness 279) = logical 418 :=
    placed agreement (position := 418) (by kernel_rfl)
  have p419 : physical (.BaseLayerWitness 280) = logical 419 :=
    placed agreement (position := 419) (by kernel_rfl)
  have p422 : physical (.BaseLayerWitness 283) = logical 422 :=
    placed agreement (position := 422) (by kernel_rfl)
  simp only [operand155, NativeLookups.Input.fields, sourceFields155, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p405, p418, p419, p422]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement155 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup155).Contains (Verification.environment logical) ↔
      ∃ index, operand155.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields155 physical logical agreement]
  exact source_semantics155 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields156 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand156.input.fields physical = sourceFields156 logical := by
  have p406 : physical (.BaseLayerWitness 267) = logical 406 :=
    placed agreement (position := 406) (by kernel_rfl)
  have p157 : physical (.BaseLayerWitness 18) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p173 : physical (.BaseLayerWitness 34) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  have p225 : physical (.BaseLayerWitness 86) = logical 225 :=
    placed agreement (position := 225) (by kernel_rfl)
  have p227 : physical (.BaseLayerWitness 88) = logical 227 :=
    placed agreement (position := 227) (by kernel_rfl)
  have p241 : physical (.BaseLayerWitness 102) = logical 241 :=
    placed agreement (position := 241) (by kernel_rfl)
  have p257 : physical (.BaseLayerWitness 118) = logical 257 :=
    placed agreement (position := 257) (by kernel_rfl)
  have p259 : physical (.BaseLayerWitness 120) = logical 259 :=
    placed agreement (position := 259) (by kernel_rfl)
  have p276 : physical (.BaseLayerWitness 137) = logical 276 :=
    placed agreement (position := 276) (by kernel_rfl)
  have p279 : physical (.BaseLayerWitness 140) = logical 279 :=
    placed agreement (position := 279) (by kernel_rfl)
  have p281 : physical (.BaseLayerWitness 142) = logical 281 :=
    placed agreement (position := 281) (by kernel_rfl)
  have p283 : physical (.BaseLayerWitness 144) = logical 283 :=
    placed agreement (position := 283) (by kernel_rfl)
  have p333 : physical (.BaseLayerWitness 194) = logical 333 :=
    placed agreement (position := 333) (by kernel_rfl)
  have p334 : physical (.BaseLayerWitness 195) = logical 334 :=
    placed agreement (position := 334) (by kernel_rfl)
  have p417 : physical (.BaseLayerWitness 278) = logical 417 :=
    placed agreement (position := 417) (by kernel_rfl)
  have p418 : physical (.BaseLayerWitness 279) = logical 418 :=
    placed agreement (position := 418) (by kernel_rfl)
  have p419 : physical (.BaseLayerWitness 280) = logical 419 :=
    placed agreement (position := 419) (by kernel_rfl)
  have p423 : physical (.BaseLayerWitness 284) = logical 423 :=
    placed agreement (position := 423) (by kernel_rfl)
  simp only [operand156, NativeLookups.Input.fields, sourceFields156, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p406, p157, p173, p225, p227, p241, p257, p259, p276, p279, p281, p283, p333, p334, p417, p418, p419, p423]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement156 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup156).Contains (Verification.environment logical) ↔
      ∃ index, operand156.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields156 physical logical agreement]
  exact source_semantics156 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields157 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand157.input.fields physical = sourceFields157 logical := by
  have p431 : physical (.BaseLayerWitness 292) = logical 431 :=
    placed agreement (position := 431) (by kernel_rfl)
  have p425 : physical (.BaseLayerWitness 286) = logical 425 :=
    placed agreement (position := 425) (by kernel_rfl)
  have p434 : physical (.BaseLayerWitness 295) = logical 434 :=
    placed agreement (position := 434) (by kernel_rfl)
  simp only [operand157, NativeLookups.Input.fields, sourceFields157, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p431, p425, p434]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement157 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup157).Contains (Verification.environment logical) ↔
      ∃ index, operand157.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields157 physical logical agreement]
  exact source_semantics157 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields158 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand158.input.fields physical = sourceFields158 logical := by
  have p433 : physical (.BaseLayerWitness 294) = logical 433 :=
    placed agreement (position := 433) (by kernel_rfl)
  have p428 : physical (.BaseLayerWitness 289) = logical 428 :=
    placed agreement (position := 428) (by kernel_rfl)
  have p435 : physical (.BaseLayerWitness 296) = logical 435 :=
    placed agreement (position := 435) (by kernel_rfl)
  simp only [operand158, NativeLookups.Input.fields, sourceFields158, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p433, p428, p435]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement158 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup158).Contains (Verification.environment logical) ↔
      ∃ index, operand158.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields158 physical logical agreement]
  exact source_semantics158 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields159 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand159.input.fields physical = sourceFields159 logical := by
  have p332 : physical (.BaseLayerWitness 193) = logical 332 :=
    placed agreement (position := 332) (by kernel_rfl)
  have p335 : physical (.BaseLayerWitness 196) = logical 335 :=
    placed agreement (position := 335) (by kernel_rfl)
  have p430 : physical (.BaseLayerWitness 291) = logical 430 :=
    placed agreement (position := 430) (by kernel_rfl)
  have p431 : physical (.BaseLayerWitness 292) = logical 431 :=
    placed agreement (position := 431) (by kernel_rfl)
  have p432 : physical (.BaseLayerWitness 293) = logical 432 :=
    placed agreement (position := 432) (by kernel_rfl)
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
  have p424 : physical (.BaseLayerWitness 285) = logical 424 :=
    placed agreement (position := 424) (by kernel_rfl)
  have p425 : physical (.BaseLayerWitness 286) = logical 425 :=
    placed agreement (position := 425) (by kernel_rfl)
  have p426 : physical (.BaseLayerWitness 287) = logical 426 :=
    placed agreement (position := 426) (by kernel_rfl)
  have p427 : physical (.BaseLayerWitness 288) = logical 427 :=
    placed agreement (position := 427) (by kernel_rfl)
  have p436 : physical (.BaseLayerWitness 297) = logical 436 :=
    placed agreement (position := 436) (by kernel_rfl)
  simp only [operand159, NativeLookups.Input.fields, sourceFields159, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p332, p335, p430, p431, p432, p190, p344, p345, p348, p364, p367, p369, p422, p423, p424, p425, p426, p427, p436]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement159 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup159).Contains (Verification.environment logical) ↔
      ∃ index, operand159.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields159 physical logical agreement]
  exact source_semantics159 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
