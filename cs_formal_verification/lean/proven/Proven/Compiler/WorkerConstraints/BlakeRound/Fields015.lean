module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries010

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields120 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand120.input.fields physical = sourceFields120 logical := by
  have p319 : physical (.BaseLayerWitness 180) = logical 319 :=
    placed agreement (position := 319) (by kernel_rfl)
  have p330 : physical (.BaseLayerWitness 191) = logical 330 :=
    placed agreement (position := 330) (by kernel_rfl)
  have p335 : physical (.BaseLayerWitness 196) = logical 335 :=
    placed agreement (position := 335) (by kernel_rfl)
  simp only [operand120, NativeLookups.Input.fields, sourceFields120, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p319, p330, p335]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement120 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup120).Contains (Verification.environment logical) ↔
      ∃ index, operand120.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields120 physical logical agreement]
  exact source_semantics120 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields121 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand121.input.fields physical = sourceFields121 logical := by
  have p340 : physical (.BaseLayerWitness 201) = logical 340 :=
    placed agreement (position := 340) (by kernel_rfl)
  have p336 : physical (.BaseLayerWitness 197) = logical 336 :=
    placed agreement (position := 336) (by kernel_rfl)
  have p337 : physical (.BaseLayerWitness 198) = logical 337 :=
    placed agreement (position := 337) (by kernel_rfl)
  have p342 : physical (.BaseLayerWitness 203) = logical 342 :=
    placed agreement (position := 342) (by kernel_rfl)
  simp only [operand121, NativeLookups.Input.fields, sourceFields121, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p340, p336, p337, p342]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement121 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup121).Contains (Verification.environment logical) ↔
      ∃ index, operand121.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields121 physical logical agreement]
  exact source_semantics121 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields122 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand122.input.fields physical = sourceFields122 logical := by
  have p200 : physical (.BaseLayerWitness 61) = logical 200 :=
    placed agreement (position := 200) (by kernel_rfl)
  have p340 : physical (.BaseLayerWitness 201) = logical 340 :=
    placed agreement (position := 340) (by kernel_rfl)
  have p163 : physical (.BaseLayerWitness 24) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  have p179 : physical (.BaseLayerWitness 40) = logical 179 :=
    placed agreement (position := 179) (by kernel_rfl)
  have p232 : physical (.BaseLayerWitness 93) = logical 232 :=
    placed agreement (position := 232) (by kernel_rfl)
  have p336 : physical (.BaseLayerWitness 197) = logical 336 :=
    placed agreement (position := 336) (by kernel_rfl)
  have p337 : physical (.BaseLayerWitness 198) = logical 337 :=
    placed agreement (position := 337) (by kernel_rfl)
  have p343 : physical (.BaseLayerWitness 204) = logical 343 :=
    placed agreement (position := 343) (by kernel_rfl)
  simp only [operand122, NativeLookups.Input.fields, sourceFields122, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p200, p340, p163, p179, p232, p336, p337, p343]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement122 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup122).Contains (Verification.environment logical) ↔
      ∃ index, operand122.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields122 physical logical agreement]
  exact source_semantics122 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields123 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand123.input.fields physical = sourceFields123 logical := by
  have p341 : physical (.BaseLayerWitness 202) = logical 341 :=
    placed agreement (position := 341) (by kernel_rfl)
  have p338 : physical (.BaseLayerWitness 199) = logical 338 :=
    placed agreement (position := 338) (by kernel_rfl)
  have p339 : physical (.BaseLayerWitness 200) = logical 339 :=
    placed agreement (position := 339) (by kernel_rfl)
  have p344 : physical (.BaseLayerWitness 205) = logical 344 :=
    placed agreement (position := 344) (by kernel_rfl)
  simp only [operand123, NativeLookups.Input.fields, sourceFields123, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p341, p338, p339, p344]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement123 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup123).Contains (Verification.environment logical) ↔
      ∃ index, operand123.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields123 physical logical agreement]
  exact source_semantics123 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields124 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand124.input.fields physical = sourceFields124 logical := by
  have p201 : physical (.BaseLayerWitness 62) = logical 201 :=
    placed agreement (position := 201) (by kernel_rfl)
  have p341 : physical (.BaseLayerWitness 202) = logical 341 :=
    placed agreement (position := 341) (by kernel_rfl)
  have p165 : physical (.BaseLayerWitness 26) = logical 165 :=
    placed agreement (position := 165) (by kernel_rfl)
  have p181 : physical (.BaseLayerWitness 42) = logical 181 :=
    placed agreement (position := 181) (by kernel_rfl)
  have p233 : physical (.BaseLayerWitness 94) = logical 233 :=
    placed agreement (position := 233) (by kernel_rfl)
  have p337 : physical (.BaseLayerWitness 198) = logical 337 :=
    placed agreement (position := 337) (by kernel_rfl)
  have p338 : physical (.BaseLayerWitness 199) = logical 338 :=
    placed agreement (position := 338) (by kernel_rfl)
  have p339 : physical (.BaseLayerWitness 200) = logical 339 :=
    placed agreement (position := 339) (by kernel_rfl)
  have p345 : physical (.BaseLayerWitness 206) = logical 345 :=
    placed agreement (position := 345) (by kernel_rfl)
  simp only [operand124, NativeLookups.Input.fields, sourceFields124, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p201, p341, p165, p181, p233, p337, p338, p339, p345]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement124 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup124).Contains (Verification.environment logical) ↔
      ∃ index, operand124.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields124 physical logical agreement]
  exact source_semantics124 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields125 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand125.input.fields physical = sourceFields125 logical := by
  have p353 : physical (.BaseLayerWitness 214) = logical 353 :=
    placed agreement (position := 353) (by kernel_rfl)
  have p347 : physical (.BaseLayerWitness 208) = logical 347 :=
    placed agreement (position := 347) (by kernel_rfl)
  have p356 : physical (.BaseLayerWitness 217) = logical 356 :=
    placed agreement (position := 356) (by kernel_rfl)
  simp only [operand125, NativeLookups.Input.fields, sourceFields125, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p353, p347, p356]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement125 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup125).Contains (Verification.environment logical) ↔
      ∃ index, operand125.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields125 physical logical agreement]
  exact source_semantics125 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields126 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand126.input.fields physical = sourceFields126 logical := by
  have p355 : physical (.BaseLayerWitness 216) = logical 355 :=
    placed agreement (position := 355) (by kernel_rfl)
  have p350 : physical (.BaseLayerWitness 211) = logical 350 :=
    placed agreement (position := 350) (by kernel_rfl)
  have p357 : physical (.BaseLayerWitness 218) = logical 357 :=
    placed agreement (position := 357) (by kernel_rfl)
  simp only [operand126, NativeLookups.Input.fields, sourceFields126, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p355, p350, p357]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement126 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup126).Contains (Verification.environment logical) ↔
      ∃ index, operand126.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields126 physical logical agreement]
  exact source_semantics126 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields127 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand127.input.fields physical = sourceFields127 logical := by
  have p179 : physical (.BaseLayerWitness 40) = logical 179 :=
    placed agreement (position := 179) (by kernel_rfl)
  have p352 : physical (.BaseLayerWitness 213) = logical 352 :=
    placed agreement (position := 352) (by kernel_rfl)
  have p353 : physical (.BaseLayerWitness 214) = logical 353 :=
    placed agreement (position := 353) (by kernel_rfl)
  have p354 : physical (.BaseLayerWitness 215) = logical 354 :=
    placed agreement (position := 354) (by kernel_rfl)
  have p190 : physical (.BaseLayerWitness 51) = logical 190 :=
    placed agreement (position := 190) (by kernel_rfl)
  have p344 : physical (.BaseLayerWitness 205) = logical 344 :=
    placed agreement (position := 344) (by kernel_rfl)
  have p345 : physical (.BaseLayerWitness 206) = logical 345 :=
    placed agreement (position := 345) (by kernel_rfl)
  have p346 : physical (.BaseLayerWitness 207) = logical 346 :=
    placed agreement (position := 346) (by kernel_rfl)
  have p347 : physical (.BaseLayerWitness 208) = logical 347 :=
    placed agreement (position := 347) (by kernel_rfl)
  have p348 : physical (.BaseLayerWitness 209) = logical 348 :=
    placed agreement (position := 348) (by kernel_rfl)
  have p349 : physical (.BaseLayerWitness 210) = logical 349 :=
    placed agreement (position := 349) (by kernel_rfl)
  have p358 : physical (.BaseLayerWitness 219) = logical 358 :=
    placed agreement (position := 358) (by kernel_rfl)
  simp only [operand127, NativeLookups.Input.fields, sourceFields127, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p179, p352, p353, p354, p190, p344, p345, p346, p347, p348, p349, p358]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement127 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup127).Contains (Verification.environment logical) ↔
      ∃ index, operand127.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields127 physical logical agreement]
  exact source_semantics127 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
