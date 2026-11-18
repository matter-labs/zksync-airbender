module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries008

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields96 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand96.input.fields physical = sourceFields96 logical := by
  have p173 : physical (.BaseLayerWitness 34) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  have p274 : physical (.BaseLayerWitness 135) = logical 274 :=
    placed agreement (position := 274) (by kernel_rfl)
  have p275 : physical (.BaseLayerWitness 136) = logical 275 :=
    placed agreement (position := 275) (by kernel_rfl)
  have p272 : physical (.BaseLayerWitness 133) = logical 272 :=
    placed agreement (position := 272) (by kernel_rfl)
  have p187 : physical (.BaseLayerWitness 48) = logical 187 :=
    placed agreement (position := 187) (by kernel_rfl)
  have p262 : physical (.BaseLayerWitness 123) = logical 262 :=
    placed agreement (position := 262) (by kernel_rfl)
  have p263 : physical (.BaseLayerWitness 124) = logical 263 :=
    placed agreement (position := 263) (by kernel_rfl)
  have p268 : physical (.BaseLayerWitness 129) = logical 268 :=
    placed agreement (position := 268) (by kernel_rfl)
  have p269 : physical (.BaseLayerWitness 130) = logical 269 :=
    placed agreement (position := 269) (by kernel_rfl)
  have p270 : physical (.BaseLayerWitness 131) = logical 270 :=
    placed agreement (position := 270) (by kernel_rfl)
  have p271 : physical (.BaseLayerWitness 132) = logical 271 :=
    placed agreement (position := 271) (by kernel_rfl)
  have p266 : physical (.BaseLayerWitness 127) = logical 266 :=
    placed agreement (position := 266) (by kernel_rfl)
  have p279 : physical (.BaseLayerWitness 140) = logical 279 :=
    placed agreement (position := 279) (by kernel_rfl)
  simp only [operand96, NativeLookups.Input.fields, sourceFields96, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p173, p274, p275, p272, p187, p262, p263, p268, p269, p270, p271, p266, p279]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement96 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup96).Contains (Verification.environment logical) ↔
      ∃ index, operand96.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields96 physical logical agreement]
  exact source_semantics96 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields97 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand97.input.fields physical = sourceFields97 logical := by
  have p265 : physical (.BaseLayerWitness 126) = logical 265 :=
    placed agreement (position := 265) (by kernel_rfl)
  have p155 : physical (.BaseLayerWitness 16) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  have p171 : physical (.BaseLayerWitness 32) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  have p224 : physical (.BaseLayerWitness 85) = logical 224 :=
    placed agreement (position := 224) (by kernel_rfl)
  have p226 : physical (.BaseLayerWitness 87) = logical 226 :=
    placed agreement (position := 226) (by kernel_rfl)
  have p257 : physical (.BaseLayerWitness 118) = logical 257 :=
    placed agreement (position := 257) (by kernel_rfl)
  have p277 : physical (.BaseLayerWitness 138) = logical 277 :=
    placed agreement (position := 277) (by kernel_rfl)
  have p278 : physical (.BaseLayerWitness 139) = logical 278 :=
    placed agreement (position := 278) (by kernel_rfl)
  have p280 : physical (.BaseLayerWitness 141) = logical 280 :=
    placed agreement (position := 280) (by kernel_rfl)
  have p281 : physical (.BaseLayerWitness 142) = logical 281 :=
    placed agreement (position := 281) (by kernel_rfl)
  have p284 : physical (.BaseLayerWitness 145) = logical 284 :=
    placed agreement (position := 284) (by kernel_rfl)
  simp only [operand97, NativeLookups.Input.fields, sourceFields97, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p265, p155, p171, p224, p226, p257, p277, p278, p280, p281, p284]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement97 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup97).Contains (Verification.environment logical) ↔
      ∃ index, operand97.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields97 physical logical agreement]
  exact source_semantics97 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields98 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand98.input.fields physical = sourceFields98 logical := by
  have p263 : physical (.BaseLayerWitness 124) = logical 263 :=
    placed agreement (position := 263) (by kernel_rfl)
  have p157 : physical (.BaseLayerWitness 18) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p173 : physical (.BaseLayerWitness 34) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  have p225 : physical (.BaseLayerWitness 86) = logical 225 :=
    placed agreement (position := 225) (by kernel_rfl)
  have p227 : physical (.BaseLayerWitness 88) = logical 227 :=
    placed agreement (position := 227) (by kernel_rfl)
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
  have p282 : physical (.BaseLayerWitness 143) = logical 282 :=
    placed agreement (position := 282) (by kernel_rfl)
  have p283 : physical (.BaseLayerWitness 144) = logical 283 :=
    placed agreement (position := 283) (by kernel_rfl)
  have p285 : physical (.BaseLayerWitness 146) = logical 285 :=
    placed agreement (position := 285) (by kernel_rfl)
  simp only [operand98, NativeLookups.Input.fields, sourceFields98, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p263, p157, p173, p225, p227, p257, p259, p276, p279, p281, p282, p283, p285]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement98 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup98).Contains (Verification.environment logical) ↔
      ∃ index, operand98.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields98 physical logical agreement]
  exact source_semantics98 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields99 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand99.input.fields physical = sourceFields99 logical := by
  have p264 : physical (.BaseLayerWitness 125) = logical 264 :=
    placed agreement (position := 264) (by kernel_rfl)
  have p280 : physical (.BaseLayerWitness 141) = logical 280 :=
    placed agreement (position := 280) (by kernel_rfl)
  have p281 : physical (.BaseLayerWitness 142) = logical 281 :=
    placed agreement (position := 281) (by kernel_rfl)
  have p286 : physical (.BaseLayerWitness 147) = logical 286 :=
    placed agreement (position := 286) (by kernel_rfl)
  simp only [operand99, NativeLookups.Input.fields, sourceFields99, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p264, p280, p281, p286]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement99 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup99).Contains (Verification.environment logical) ↔
      ∃ index, operand99.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields99 physical logical agreement]
  exact source_semantics99 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields100 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand100.input.fields physical = sourceFields100 logical := by
  have p262 : physical (.BaseLayerWitness 123) = logical 262 :=
    placed agreement (position := 262) (by kernel_rfl)
  have p282 : physical (.BaseLayerWitness 143) = logical 282 :=
    placed agreement (position := 282) (by kernel_rfl)
  have p283 : physical (.BaseLayerWitness 144) = logical 283 :=
    placed agreement (position := 283) (by kernel_rfl)
  have p287 : physical (.BaseLayerWitness 148) = logical 287 :=
    placed agreement (position := 287) (by kernel_rfl)
  simp only [operand100, NativeLookups.Input.fields, sourceFields100, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p262, p282, p283, p287]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement100 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup100).Contains (Verification.environment logical) ↔
      ∃ index, operand100.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields100 physical logical agreement]
  exact source_semantics100 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields101 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand101.input.fields physical = sourceFields101 logical := by
  have p277 : physical (.BaseLayerWitness 138) = logical 277 :=
    placed agreement (position := 277) (by kernel_rfl)
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
  have p288 : physical (.BaseLayerWitness 149) = logical 288 :=
    placed agreement (position := 288) (by kernel_rfl)
  have p289 : physical (.BaseLayerWitness 150) = logical 289 :=
    placed agreement (position := 289) (by kernel_rfl)
  have p292 : physical (.BaseLayerWitness 153) = logical 292 :=
    placed agreement (position := 292) (by kernel_rfl)
  simp only [operand101, NativeLookups.Input.fields, sourceFields101, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p277, p186, p264, p265, p268, p284, p287, p288, p289, p292]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement101 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup101).Contains (Verification.environment logical) ↔
      ∃ index, operand101.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields101 physical logical agreement]
  exact source_semantics101 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields102 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand102.input.fields physical = sourceFields102 logical := by
  have p276 : physical (.BaseLayerWitness 137) = logical 276 :=
    placed agreement (position := 276) (by kernel_rfl)
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
  have p290 : physical (.BaseLayerWitness 151) = logical 290 :=
    placed agreement (position := 290) (by kernel_rfl)
  have p291 : physical (.BaseLayerWitness 152) = logical 291 :=
    placed agreement (position := 291) (by kernel_rfl)
  have p293 : physical (.BaseLayerWitness 154) = logical 293 :=
    placed agreement (position := 293) (by kernel_rfl)
  simp only [operand102, NativeLookups.Input.fields, sourceFields102, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p276, p187, p262, p263, p268, p271, p285, p286, p289, p290, p291, p293]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement102 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup102).Contains (Verification.environment logical) ↔
      ∃ index, operand102.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields102 physical logical agreement]
  exact source_semantics102 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields103 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand103.input.fields physical = sourceFields103 logical := by
  have p278 : physical (.BaseLayerWitness 139) = logical 278 :=
    placed agreement (position := 278) (by kernel_rfl)
  have p288 : physical (.BaseLayerWitness 149) = logical 288 :=
    placed agreement (position := 288) (by kernel_rfl)
  have p294 : physical (.BaseLayerWitness 155) = logical 294 :=
    placed agreement (position := 294) (by kernel_rfl)
  simp only [operand103, NativeLookups.Input.fields, sourceFields103, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p278, p288, p294]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement103 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup103).Contains (Verification.environment logical) ↔
      ∃ index, operand103.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields103 physical logical agreement]
  exact source_semantics103 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
