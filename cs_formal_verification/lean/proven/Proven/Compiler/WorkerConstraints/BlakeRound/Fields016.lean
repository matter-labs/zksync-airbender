module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries011

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields128 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand128.input.fields physical = sourceFields128 logical := by
  have p181 : physical (.BaseLayerWitness 42) = logical 181 :=
    placed agreement (position := 181) (by kernel_rfl)
  have p354 : physical (.BaseLayerWitness 215) = logical 354 :=
    placed agreement (position := 354) (by kernel_rfl)
  have p355 : physical (.BaseLayerWitness 216) = logical 355 :=
    placed agreement (position := 355) (by kernel_rfl)
  have p352 : physical (.BaseLayerWitness 213) = logical 352 :=
    placed agreement (position := 352) (by kernel_rfl)
  have p191 : physical (.BaseLayerWitness 52) = logical 191 :=
    placed agreement (position := 191) (by kernel_rfl)
  have p342 : physical (.BaseLayerWitness 203) = logical 342 :=
    placed agreement (position := 342) (by kernel_rfl)
  have p343 : physical (.BaseLayerWitness 204) = logical 343 :=
    placed agreement (position := 343) (by kernel_rfl)
  have p348 : physical (.BaseLayerWitness 209) = logical 348 :=
    placed agreement (position := 348) (by kernel_rfl)
  have p349 : physical (.BaseLayerWitness 210) = logical 349 :=
    placed agreement (position := 349) (by kernel_rfl)
  have p350 : physical (.BaseLayerWitness 211) = logical 350 :=
    placed agreement (position := 350) (by kernel_rfl)
  have p351 : physical (.BaseLayerWitness 212) = logical 351 :=
    placed agreement (position := 351) (by kernel_rfl)
  have p346 : physical (.BaseLayerWitness 207) = logical 346 :=
    placed agreement (position := 346) (by kernel_rfl)
  have p359 : physical (.BaseLayerWitness 220) = logical 359 :=
    placed agreement (position := 359) (by kernel_rfl)
  simp only [operand128, NativeLookups.Input.fields, sourceFields128, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p181, p354, p355, p352, p191, p342, p343, p348, p349, p350, p351, p346, p359]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement128 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup128).Contains (Verification.environment logical) ↔
      ∃ index, operand128.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields128 physical logical agreement]
  exact source_semantics128 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields129 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand129.input.fields physical = sourceFields129 logical := by
  have p345 : physical (.BaseLayerWitness 206) = logical 345 :=
    placed agreement (position := 345) (by kernel_rfl)
  have p163 : physical (.BaseLayerWitness 24) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  have p179 : physical (.BaseLayerWitness 40) = logical 179 :=
    placed agreement (position := 179) (by kernel_rfl)
  have p232 : physical (.BaseLayerWitness 93) = logical 232 :=
    placed agreement (position := 232) (by kernel_rfl)
  have p234 : physical (.BaseLayerWitness 95) = logical 234 :=
    placed agreement (position := 234) (by kernel_rfl)
  have p337 : physical (.BaseLayerWitness 198) = logical 337 :=
    placed agreement (position := 337) (by kernel_rfl)
  have p357 : physical (.BaseLayerWitness 218) = logical 357 :=
    placed agreement (position := 357) (by kernel_rfl)
  have p358 : physical (.BaseLayerWitness 219) = logical 358 :=
    placed agreement (position := 358) (by kernel_rfl)
  have p360 : physical (.BaseLayerWitness 221) = logical 360 :=
    placed agreement (position := 360) (by kernel_rfl)
  have p361 : physical (.BaseLayerWitness 222) = logical 361 :=
    placed agreement (position := 361) (by kernel_rfl)
  have p364 : physical (.BaseLayerWitness 225) = logical 364 :=
    placed agreement (position := 364) (by kernel_rfl)
  simp only [operand129, NativeLookups.Input.fields, sourceFields129, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p345, p163, p179, p232, p234, p337, p357, p358, p360, p361, p364]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement129 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup129).Contains (Verification.environment logical) ↔
      ∃ index, operand129.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields129 physical logical agreement]
  exact source_semantics129 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields130 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand130.input.fields physical = sourceFields130 logical := by
  have p343 : physical (.BaseLayerWitness 204) = logical 343 :=
    placed agreement (position := 343) (by kernel_rfl)
  have p165 : physical (.BaseLayerWitness 26) = logical 165 :=
    placed agreement (position := 165) (by kernel_rfl)
  have p181 : physical (.BaseLayerWitness 42) = logical 181 :=
    placed agreement (position := 181) (by kernel_rfl)
  have p233 : physical (.BaseLayerWitness 94) = logical 233 :=
    placed agreement (position := 233) (by kernel_rfl)
  have p235 : physical (.BaseLayerWitness 96) = logical 235 :=
    placed agreement (position := 235) (by kernel_rfl)
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
  have p362 : physical (.BaseLayerWitness 223) = logical 362 :=
    placed agreement (position := 362) (by kernel_rfl)
  have p363 : physical (.BaseLayerWitness 224) = logical 363 :=
    placed agreement (position := 363) (by kernel_rfl)
  have p365 : physical (.BaseLayerWitness 226) = logical 365 :=
    placed agreement (position := 365) (by kernel_rfl)
  simp only [operand130, NativeLookups.Input.fields, sourceFields130, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p343, p165, p181, p233, p235, p337, p339, p356, p359, p361, p362, p363, p365]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement130 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup130).Contains (Verification.environment logical) ↔
      ∃ index, operand130.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields130 physical logical agreement]
  exact source_semantics130 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields131 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand131.input.fields physical = sourceFields131 logical := by
  have p344 : physical (.BaseLayerWitness 205) = logical 344 :=
    placed agreement (position := 344) (by kernel_rfl)
  have p360 : physical (.BaseLayerWitness 221) = logical 360 :=
    placed agreement (position := 360) (by kernel_rfl)
  have p361 : physical (.BaseLayerWitness 222) = logical 361 :=
    placed agreement (position := 361) (by kernel_rfl)
  have p366 : physical (.BaseLayerWitness 227) = logical 366 :=
    placed agreement (position := 366) (by kernel_rfl)
  simp only [operand131, NativeLookups.Input.fields, sourceFields131, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p344, p360, p361, p366]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement131 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup131).Contains (Verification.environment logical) ↔
      ∃ index, operand131.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields131 physical logical agreement]
  exact source_semantics131 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields132 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand132.input.fields physical = sourceFields132 logical := by
  have p342 : physical (.BaseLayerWitness 203) = logical 342 :=
    placed agreement (position := 342) (by kernel_rfl)
  have p362 : physical (.BaseLayerWitness 223) = logical 362 :=
    placed agreement (position := 362) (by kernel_rfl)
  have p363 : physical (.BaseLayerWitness 224) = logical 363 :=
    placed agreement (position := 363) (by kernel_rfl)
  have p367 : physical (.BaseLayerWitness 228) = logical 367 :=
    placed agreement (position := 367) (by kernel_rfl)
  simp only [operand132, NativeLookups.Input.fields, sourceFields132, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p342, p362, p363, p367]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement132 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup132).Contains (Verification.environment logical) ↔
      ∃ index, operand132.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields132 physical logical agreement]
  exact source_semantics132 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields133 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand133.input.fields physical = sourceFields133 logical := by
  have p357 : physical (.BaseLayerWitness 218) = logical 357 :=
    placed agreement (position := 357) (by kernel_rfl)
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
  have p368 : physical (.BaseLayerWitness 229) = logical 368 :=
    placed agreement (position := 368) (by kernel_rfl)
  have p369 : physical (.BaseLayerWitness 230) = logical 369 :=
    placed agreement (position := 369) (by kernel_rfl)
  have p372 : physical (.BaseLayerWitness 233) = logical 372 :=
    placed agreement (position := 372) (by kernel_rfl)
  simp only [operand133, NativeLookups.Input.fields, sourceFields133, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p357, p190, p344, p345, p348, p364, p367, p368, p369, p372]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement133 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup133).Contains (Verification.environment logical) ↔
      ∃ index, operand133.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields133 physical logical agreement]
  exact source_semantics133 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields134 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand134.input.fields physical = sourceFields134 logical := by
  have p356 : physical (.BaseLayerWitness 217) = logical 356 :=
    placed agreement (position := 356) (by kernel_rfl)
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
  have p370 : physical (.BaseLayerWitness 231) = logical 370 :=
    placed agreement (position := 370) (by kernel_rfl)
  have p371 : physical (.BaseLayerWitness 232) = logical 371 :=
    placed agreement (position := 371) (by kernel_rfl)
  have p373 : physical (.BaseLayerWitness 234) = logical 373 :=
    placed agreement (position := 373) (by kernel_rfl)
  simp only [operand134, NativeLookups.Input.fields, sourceFields134, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p356, p191, p342, p343, p348, p351, p365, p366, p369, p370, p371, p373]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement134 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup134).Contains (Verification.environment logical) ↔
      ∃ index, operand134.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields134 physical logical agreement]
  exact source_semantics134 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields135 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand135.input.fields physical = sourceFields135 logical := by
  have p358 : physical (.BaseLayerWitness 219) = logical 358 :=
    placed agreement (position := 358) (by kernel_rfl)
  have p368 : physical (.BaseLayerWitness 229) = logical 368 :=
    placed agreement (position := 368) (by kernel_rfl)
  have p374 : physical (.BaseLayerWitness 235) = logical 374 :=
    placed agreement (position := 374) (by kernel_rfl)
  simp only [operand135, NativeLookups.Input.fields, sourceFields135, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p358, p368, p374]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement135 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup135).Contains (Verification.environment logical) ↔
      ∃ index, operand135.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields135 physical logical agreement]
  exact source_semantics135 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
