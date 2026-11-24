module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries007

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields88 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand88.input.fields physical = sourceFields88 logical := by
  have p101 : physical (.BaseLayerMemory 150) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  simp only [operand88, NativeLookups.Input.fields, sourceFields88]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p101]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement88 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup88).Contains (Verification.environment logical) ↔
      ∃ index, operand88.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  rw [fields88 physical logical agreement]
  exact source_semantics88 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields89 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand89.input.fields physical = sourceFields89 logical := by
  have p260 : physical (.BaseLayerWitness 121) = logical 260 :=
    placed agreement (position := 260) (by kernel_rfl)
  have p256 : physical (.BaseLayerWitness 117) = logical 256 :=
    placed agreement (position := 256) (by kernel_rfl)
  have p257 : physical (.BaseLayerWitness 118) = logical 257 :=
    placed agreement (position := 257) (by kernel_rfl)
  have p262 : physical (.BaseLayerWitness 123) = logical 262 :=
    placed agreement (position := 262) (by kernel_rfl)
  simp only [operand89, NativeLookups.Input.fields, sourceFields89, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p260, p256, p257, p262]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement89 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup89).Contains (Verification.environment logical) ↔
      ∃ index, operand89.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields89 physical logical agreement]
  exact source_semantics89 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields90 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand90.input.fields physical = sourceFields90 logical := by
  have p198 : physical (.BaseLayerWitness 59) = logical 198 :=
    placed agreement (position := 198) (by kernel_rfl)
  have p260 : physical (.BaseLayerWitness 121) = logical 260 :=
    placed agreement (position := 260) (by kernel_rfl)
  have p155 : physical (.BaseLayerWitness 16) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  have p171 : physical (.BaseLayerWitness 32) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  have p224 : physical (.BaseLayerWitness 85) = logical 224 :=
    placed agreement (position := 224) (by kernel_rfl)
  have p256 : physical (.BaseLayerWitness 117) = logical 256 :=
    placed agreement (position := 256) (by kernel_rfl)
  have p257 : physical (.BaseLayerWitness 118) = logical 257 :=
    placed agreement (position := 257) (by kernel_rfl)
  have p263 : physical (.BaseLayerWitness 124) = logical 263 :=
    placed agreement (position := 263) (by kernel_rfl)
  simp only [operand90, NativeLookups.Input.fields, sourceFields90, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p198, p260, p155, p171, p224, p256, p257, p263]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement90 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup90).Contains (Verification.environment logical) ↔
      ∃ index, operand90.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields90 physical logical agreement]
  exact source_semantics90 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields91 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand91.input.fields physical = sourceFields91 logical := by
  have p261 : physical (.BaseLayerWitness 122) = logical 261 :=
    placed agreement (position := 261) (by kernel_rfl)
  have p258 : physical (.BaseLayerWitness 119) = logical 258 :=
    placed agreement (position := 258) (by kernel_rfl)
  have p259 : physical (.BaseLayerWitness 120) = logical 259 :=
    placed agreement (position := 259) (by kernel_rfl)
  have p264 : physical (.BaseLayerWitness 125) = logical 264 :=
    placed agreement (position := 264) (by kernel_rfl)
  simp only [operand91, NativeLookups.Input.fields, sourceFields91, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p261, p258, p259, p264]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement91 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup91).Contains (Verification.environment logical) ↔
      ∃ index, operand91.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields91 physical logical agreement]
  exact source_semantics91 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields92 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand92.input.fields physical = sourceFields92 logical := by
  have p199 : physical (.BaseLayerWitness 60) = logical 199 :=
    placed agreement (position := 199) (by kernel_rfl)
  have p261 : physical (.BaseLayerWitness 122) = logical 261 :=
    placed agreement (position := 261) (by kernel_rfl)
  have p157 : physical (.BaseLayerWitness 18) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p173 : physical (.BaseLayerWitness 34) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  have p225 : physical (.BaseLayerWitness 86) = logical 225 :=
    placed agreement (position := 225) (by kernel_rfl)
  have p257 : physical (.BaseLayerWitness 118) = logical 257 :=
    placed agreement (position := 257) (by kernel_rfl)
  have p258 : physical (.BaseLayerWitness 119) = logical 258 :=
    placed agreement (position := 258) (by kernel_rfl)
  have p259 : physical (.BaseLayerWitness 120) = logical 259 :=
    placed agreement (position := 259) (by kernel_rfl)
  have p265 : physical (.BaseLayerWitness 126) = logical 265 :=
    placed agreement (position := 265) (by kernel_rfl)
  simp only [operand92, NativeLookups.Input.fields, sourceFields92, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p199, p261, p157, p173, p225, p257, p258, p259, p265]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement92 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup92).Contains (Verification.environment logical) ↔
      ∃ index, operand92.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields92 physical logical agreement]
  exact source_semantics92 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields93 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand93.input.fields physical = sourceFields93 logical := by
  have p273 : physical (.BaseLayerWitness 134) = logical 273 :=
    placed agreement (position := 273) (by kernel_rfl)
  have p267 : physical (.BaseLayerWitness 128) = logical 267 :=
    placed agreement (position := 267) (by kernel_rfl)
  have p276 : physical (.BaseLayerWitness 137) = logical 276 :=
    placed agreement (position := 276) (by kernel_rfl)
  simp only [operand93, NativeLookups.Input.fields, sourceFields93, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p273, p267, p276]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement93 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup93).Contains (Verification.environment logical) ↔
      ∃ index, operand93.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields93 physical logical agreement]
  exact source_semantics93 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields94 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand94.input.fields physical = sourceFields94 logical := by
  have p275 : physical (.BaseLayerWitness 136) = logical 275 :=
    placed agreement (position := 275) (by kernel_rfl)
  have p270 : physical (.BaseLayerWitness 131) = logical 270 :=
    placed agreement (position := 270) (by kernel_rfl)
  have p277 : physical (.BaseLayerWitness 138) = logical 277 :=
    placed agreement (position := 277) (by kernel_rfl)
  simp only [operand94, NativeLookups.Input.fields, sourceFields94, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p275, p270, p277]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement94 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup94).Contains (Verification.environment logical) ↔
      ∃ index, operand94.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields94 physical logical agreement]
  exact source_semantics94 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields95 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand95.input.fields physical = sourceFields95 logical := by
  have p171 : physical (.BaseLayerWitness 32) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  have p272 : physical (.BaseLayerWitness 133) = logical 272 :=
    placed agreement (position := 272) (by kernel_rfl)
  have p273 : physical (.BaseLayerWitness 134) = logical 273 :=
    placed agreement (position := 273) (by kernel_rfl)
  have p274 : physical (.BaseLayerWitness 135) = logical 274 :=
    placed agreement (position := 274) (by kernel_rfl)
  have p186 : physical (.BaseLayerWitness 47) = logical 186 :=
    placed agreement (position := 186) (by kernel_rfl)
  have p264 : physical (.BaseLayerWitness 125) = logical 264 :=
    placed agreement (position := 264) (by kernel_rfl)
  have p265 : physical (.BaseLayerWitness 126) = logical 265 :=
    placed agreement (position := 265) (by kernel_rfl)
  have p266 : physical (.BaseLayerWitness 127) = logical 266 :=
    placed agreement (position := 266) (by kernel_rfl)
  have p267 : physical (.BaseLayerWitness 128) = logical 267 :=
    placed agreement (position := 267) (by kernel_rfl)
  have p268 : physical (.BaseLayerWitness 129) = logical 268 :=
    placed agreement (position := 268) (by kernel_rfl)
  have p269 : physical (.BaseLayerWitness 130) = logical 269 :=
    placed agreement (position := 269) (by kernel_rfl)
  have p278 : physical (.BaseLayerWitness 139) = logical 278 :=
    placed agreement (position := 278) (by kernel_rfl)
  simp only [operand95, NativeLookups.Input.fields, sourceFields95, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p171, p272, p273, p274, p186, p264, p265, p266, p267, p268, p269, p278]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement95 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup95).Contains (Verification.environment logical) ↔
      ∃ index, operand95.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields95 physical logical agreement]
  exact source_semantics95 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
