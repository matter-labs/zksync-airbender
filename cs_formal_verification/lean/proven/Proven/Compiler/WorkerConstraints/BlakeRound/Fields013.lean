module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries008
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries009

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields104 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand104.input.fields physical = sourceFields104 logical := by
  have p279 : physical (.BaseLayerWitness 140) = logical 279 :=
    placed agreement (position := 279) (by kernel_rfl)
  have p290 : physical (.BaseLayerWitness 151) = logical 290 :=
    placed agreement (position := 290) (by kernel_rfl)
  have p295 : physical (.BaseLayerWitness 156) = logical 295 :=
    placed agreement (position := 295) (by kernel_rfl)
  simp only [operand104, NativeLookups.Input.fields, sourceFields104, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p279, p290, p295]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement104 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup104).Contains (Verification.environment logical) ↔
      ∃ index, operand104.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields104 physical logical agreement]
  exact source_semantics104 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields105 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand105.input.fields physical = sourceFields105 logical := by
  have p300 : physical (.BaseLayerWitness 161) = logical 300 :=
    placed agreement (position := 300) (by kernel_rfl)
  have p296 : physical (.BaseLayerWitness 157) = logical 296 :=
    placed agreement (position := 296) (by kernel_rfl)
  have p297 : physical (.BaseLayerWitness 158) = logical 297 :=
    placed agreement (position := 297) (by kernel_rfl)
  have p302 : physical (.BaseLayerWitness 163) = logical 302 :=
    placed agreement (position := 302) (by kernel_rfl)
  simp only [operand105, NativeLookups.Input.fields, sourceFields105, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p300, p296, p297, p302]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement105 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup105).Contains (Verification.environment logical) ↔
      ∃ index, operand105.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields105 physical logical agreement]
  exact source_semantics105 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields106 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand106.input.fields physical = sourceFields106 logical := by
  have p194 : physical (.BaseLayerWitness 55) = logical 194 :=
    placed agreement (position := 194) (by kernel_rfl)
  have p300 : physical (.BaseLayerWitness 161) = logical 300 :=
    placed agreement (position := 300) (by kernel_rfl)
  have p159 : physical (.BaseLayerWitness 20) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p175 : physical (.BaseLayerWitness 36) = logical 175 :=
    placed agreement (position := 175) (by kernel_rfl)
  have p228 : physical (.BaseLayerWitness 89) = logical 228 :=
    placed agreement (position := 228) (by kernel_rfl)
  have p296 : physical (.BaseLayerWitness 157) = logical 296 :=
    placed agreement (position := 296) (by kernel_rfl)
  have p297 : physical (.BaseLayerWitness 158) = logical 297 :=
    placed agreement (position := 297) (by kernel_rfl)
  have p303 : physical (.BaseLayerWitness 164) = logical 303 :=
    placed agreement (position := 303) (by kernel_rfl)
  simp only [operand106, NativeLookups.Input.fields, sourceFields106, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p194, p300, p159, p175, p228, p296, p297, p303]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement106 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup106).Contains (Verification.environment logical) ↔
      ∃ index, operand106.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields106 physical logical agreement]
  exact source_semantics106 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields107 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand107.input.fields physical = sourceFields107 logical := by
  have p301 : physical (.BaseLayerWitness 162) = logical 301 :=
    placed agreement (position := 301) (by kernel_rfl)
  have p298 : physical (.BaseLayerWitness 159) = logical 298 :=
    placed agreement (position := 298) (by kernel_rfl)
  have p299 : physical (.BaseLayerWitness 160) = logical 299 :=
    placed agreement (position := 299) (by kernel_rfl)
  have p304 : physical (.BaseLayerWitness 165) = logical 304 :=
    placed agreement (position := 304) (by kernel_rfl)
  simp only [operand107, NativeLookups.Input.fields, sourceFields107, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p301, p298, p299, p304]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement107 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup107).Contains (Verification.environment logical) ↔
      ∃ index, operand107.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields107 physical logical agreement]
  exact source_semantics107 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields108 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand108.input.fields physical = sourceFields108 logical := by
  have p195 : physical (.BaseLayerWitness 56) = logical 195 :=
    placed agreement (position := 195) (by kernel_rfl)
  have p301 : physical (.BaseLayerWitness 162) = logical 301 :=
    placed agreement (position := 301) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 22) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  have p177 : physical (.BaseLayerWitness 38) = logical 177 :=
    placed agreement (position := 177) (by kernel_rfl)
  have p229 : physical (.BaseLayerWitness 90) = logical 229 :=
    placed agreement (position := 229) (by kernel_rfl)
  have p297 : physical (.BaseLayerWitness 158) = logical 297 :=
    placed agreement (position := 297) (by kernel_rfl)
  have p298 : physical (.BaseLayerWitness 159) = logical 298 :=
    placed agreement (position := 298) (by kernel_rfl)
  have p299 : physical (.BaseLayerWitness 160) = logical 299 :=
    placed agreement (position := 299) (by kernel_rfl)
  have p305 : physical (.BaseLayerWitness 166) = logical 305 :=
    placed agreement (position := 305) (by kernel_rfl)
  simp only [operand108, NativeLookups.Input.fields, sourceFields108, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p195, p301, p161, p177, p229, p297, p298, p299, p305]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement108 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup108).Contains (Verification.environment logical) ↔
      ∃ index, operand108.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields108 physical logical agreement]
  exact source_semantics108 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields109 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand109.input.fields physical = sourceFields109 logical := by
  have p313 : physical (.BaseLayerWitness 174) = logical 313 :=
    placed agreement (position := 313) (by kernel_rfl)
  have p307 : physical (.BaseLayerWitness 168) = logical 307 :=
    placed agreement (position := 307) (by kernel_rfl)
  have p316 : physical (.BaseLayerWitness 177) = logical 316 :=
    placed agreement (position := 316) (by kernel_rfl)
  simp only [operand109, NativeLookups.Input.fields, sourceFields109, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p313, p307, p316]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement109 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup109).Contains (Verification.environment logical) ↔
      ∃ index, operand109.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields109 physical logical agreement]
  exact source_semantics109 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields110 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand110.input.fields physical = sourceFields110 logical := by
  have p315 : physical (.BaseLayerWitness 176) = logical 315 :=
    placed agreement (position := 315) (by kernel_rfl)
  have p310 : physical (.BaseLayerWitness 171) = logical 310 :=
    placed agreement (position := 310) (by kernel_rfl)
  have p317 : physical (.BaseLayerWitness 178) = logical 317 :=
    placed agreement (position := 317) (by kernel_rfl)
  simp only [operand110, NativeLookups.Input.fields, sourceFields110, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p315, p310, p317]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement110 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup110).Contains (Verification.environment logical) ↔
      ∃ index, operand110.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields110 physical logical agreement]
  exact source_semantics110 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields111 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand111.input.fields physical = sourceFields111 logical := by
  have p175 : physical (.BaseLayerWitness 36) = logical 175 :=
    placed agreement (position := 175) (by kernel_rfl)
  have p312 : physical (.BaseLayerWitness 173) = logical 312 :=
    placed agreement (position := 312) (by kernel_rfl)
  have p313 : physical (.BaseLayerWitness 174) = logical 313 :=
    placed agreement (position := 313) (by kernel_rfl)
  have p314 : physical (.BaseLayerWitness 175) = logical 314 :=
    placed agreement (position := 314) (by kernel_rfl)
  have p188 : physical (.BaseLayerWitness 49) = logical 188 :=
    placed agreement (position := 188) (by kernel_rfl)
  have p304 : physical (.BaseLayerWitness 165) = logical 304 :=
    placed agreement (position := 304) (by kernel_rfl)
  have p305 : physical (.BaseLayerWitness 166) = logical 305 :=
    placed agreement (position := 305) (by kernel_rfl)
  have p306 : physical (.BaseLayerWitness 167) = logical 306 :=
    placed agreement (position := 306) (by kernel_rfl)
  have p307 : physical (.BaseLayerWitness 168) = logical 307 :=
    placed agreement (position := 307) (by kernel_rfl)
  have p308 : physical (.BaseLayerWitness 169) = logical 308 :=
    placed agreement (position := 308) (by kernel_rfl)
  have p309 : physical (.BaseLayerWitness 170) = logical 309 :=
    placed agreement (position := 309) (by kernel_rfl)
  have p318 : physical (.BaseLayerWitness 179) = logical 318 :=
    placed agreement (position := 318) (by kernel_rfl)
  simp only [operand111, NativeLookups.Input.fields, sourceFields111, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p175, p312, p313, p314, p188, p304, p305, p306, p307, p308, p309, p318]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement111 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup111).Contains (Verification.environment logical) ↔
      ∃ index, operand111.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields111 physical logical agreement]
  exact source_semantics111 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
