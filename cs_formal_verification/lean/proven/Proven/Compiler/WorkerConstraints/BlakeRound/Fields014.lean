module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries009

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields112 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand112.input.fields physical = sourceFields112 logical := by
  have p177 : physical (.BaseLayerWitness 38) = logical 177 :=
    placed agreement (position := 177) (by kernel_rfl)
  have p314 : physical (.BaseLayerWitness 175) = logical 314 :=
    placed agreement (position := 314) (by kernel_rfl)
  have p315 : physical (.BaseLayerWitness 176) = logical 315 :=
    placed agreement (position := 315) (by kernel_rfl)
  have p312 : physical (.BaseLayerWitness 173) = logical 312 :=
    placed agreement (position := 312) (by kernel_rfl)
  have p189 : physical (.BaseLayerWitness 50) = logical 189 :=
    placed agreement (position := 189) (by kernel_rfl)
  have p302 : physical (.BaseLayerWitness 163) = logical 302 :=
    placed agreement (position := 302) (by kernel_rfl)
  have p303 : physical (.BaseLayerWitness 164) = logical 303 :=
    placed agreement (position := 303) (by kernel_rfl)
  have p308 : physical (.BaseLayerWitness 169) = logical 308 :=
    placed agreement (position := 308) (by kernel_rfl)
  have p309 : physical (.BaseLayerWitness 170) = logical 309 :=
    placed agreement (position := 309) (by kernel_rfl)
  have p310 : physical (.BaseLayerWitness 171) = logical 310 :=
    placed agreement (position := 310) (by kernel_rfl)
  have p311 : physical (.BaseLayerWitness 172) = logical 311 :=
    placed agreement (position := 311) (by kernel_rfl)
  have p306 : physical (.BaseLayerWitness 167) = logical 306 :=
    placed agreement (position := 306) (by kernel_rfl)
  have p319 : physical (.BaseLayerWitness 180) = logical 319 :=
    placed agreement (position := 319) (by kernel_rfl)
  simp only [operand112, NativeLookups.Input.fields, sourceFields112, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p177, p314, p315, p312, p189, p302, p303, p308, p309, p310, p311, p306, p319]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement112 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup112).Contains (Verification.environment logical) ↔
      ∃ index, operand112.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields112 physical logical agreement]
  exact source_semantics112 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields113 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand113.input.fields physical = sourceFields113 logical := by
  have p305 : physical (.BaseLayerWitness 166) = logical 305 :=
    placed agreement (position := 305) (by kernel_rfl)
  have p159 : physical (.BaseLayerWitness 20) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p175 : physical (.BaseLayerWitness 36) = logical 175 :=
    placed agreement (position := 175) (by kernel_rfl)
  have p228 : physical (.BaseLayerWitness 89) = logical 228 :=
    placed agreement (position := 228) (by kernel_rfl)
  have p230 : physical (.BaseLayerWitness 91) = logical 230 :=
    placed agreement (position := 230) (by kernel_rfl)
  have p297 : physical (.BaseLayerWitness 158) = logical 297 :=
    placed agreement (position := 297) (by kernel_rfl)
  have p317 : physical (.BaseLayerWitness 178) = logical 317 :=
    placed agreement (position := 317) (by kernel_rfl)
  have p318 : physical (.BaseLayerWitness 179) = logical 318 :=
    placed agreement (position := 318) (by kernel_rfl)
  have p320 : physical (.BaseLayerWitness 181) = logical 320 :=
    placed agreement (position := 320) (by kernel_rfl)
  have p321 : physical (.BaseLayerWitness 182) = logical 321 :=
    placed agreement (position := 321) (by kernel_rfl)
  have p324 : physical (.BaseLayerWitness 185) = logical 324 :=
    placed agreement (position := 324) (by kernel_rfl)
  simp only [operand113, NativeLookups.Input.fields, sourceFields113, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p305, p159, p175, p228, p230, p297, p317, p318, p320, p321, p324]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement113 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup113).Contains (Verification.environment logical) ↔
      ∃ index, operand113.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields113 physical logical agreement]
  exact source_semantics113 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields114 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand114.input.fields physical = sourceFields114 logical := by
  have p303 : physical (.BaseLayerWitness 164) = logical 303 :=
    placed agreement (position := 303) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 22) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  have p177 : physical (.BaseLayerWitness 38) = logical 177 :=
    placed agreement (position := 177) (by kernel_rfl)
  have p229 : physical (.BaseLayerWitness 90) = logical 229 :=
    placed agreement (position := 229) (by kernel_rfl)
  have p231 : physical (.BaseLayerWitness 92) = logical 231 :=
    placed agreement (position := 231) (by kernel_rfl)
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
  have p322 : physical (.BaseLayerWitness 183) = logical 322 :=
    placed agreement (position := 322) (by kernel_rfl)
  have p323 : physical (.BaseLayerWitness 184) = logical 323 :=
    placed agreement (position := 323) (by kernel_rfl)
  have p325 : physical (.BaseLayerWitness 186) = logical 325 :=
    placed agreement (position := 325) (by kernel_rfl)
  simp only [operand114, NativeLookups.Input.fields, sourceFields114, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p303, p161, p177, p229, p231, p297, p299, p316, p319, p321, p322, p323, p325]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement114 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup114).Contains (Verification.environment logical) ↔
      ∃ index, operand114.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields114 physical logical agreement]
  exact source_semantics114 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields115 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand115.input.fields physical = sourceFields115 logical := by
  have p304 : physical (.BaseLayerWitness 165) = logical 304 :=
    placed agreement (position := 304) (by kernel_rfl)
  have p320 : physical (.BaseLayerWitness 181) = logical 320 :=
    placed agreement (position := 320) (by kernel_rfl)
  have p321 : physical (.BaseLayerWitness 182) = logical 321 :=
    placed agreement (position := 321) (by kernel_rfl)
  have p326 : physical (.BaseLayerWitness 187) = logical 326 :=
    placed agreement (position := 326) (by kernel_rfl)
  simp only [operand115, NativeLookups.Input.fields, sourceFields115, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p304, p320, p321, p326]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement115 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup115).Contains (Verification.environment logical) ↔
      ∃ index, operand115.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields115 physical logical agreement]
  exact source_semantics115 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields116 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand116.input.fields physical = sourceFields116 logical := by
  have p302 : physical (.BaseLayerWitness 163) = logical 302 :=
    placed agreement (position := 302) (by kernel_rfl)
  have p322 : physical (.BaseLayerWitness 183) = logical 322 :=
    placed agreement (position := 322) (by kernel_rfl)
  have p323 : physical (.BaseLayerWitness 184) = logical 323 :=
    placed agreement (position := 323) (by kernel_rfl)
  have p327 : physical (.BaseLayerWitness 188) = logical 327 :=
    placed agreement (position := 327) (by kernel_rfl)
  simp only [operand116, NativeLookups.Input.fields, sourceFields116, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p302, p322, p323, p327]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement116 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup116).Contains (Verification.environment logical) ↔
      ∃ index, operand116.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields116 physical logical agreement]
  exact source_semantics116 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields117 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand117.input.fields physical = sourceFields117 logical := by
  have p317 : physical (.BaseLayerWitness 178) = logical 317 :=
    placed agreement (position := 317) (by kernel_rfl)
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
  have p328 : physical (.BaseLayerWitness 189) = logical 328 :=
    placed agreement (position := 328) (by kernel_rfl)
  have p329 : physical (.BaseLayerWitness 190) = logical 329 :=
    placed agreement (position := 329) (by kernel_rfl)
  have p332 : physical (.BaseLayerWitness 193) = logical 332 :=
    placed agreement (position := 332) (by kernel_rfl)
  simp only [operand117, NativeLookups.Input.fields, sourceFields117, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p317, p188, p304, p305, p308, p324, p327, p328, p329, p332]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement117 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup117).Contains (Verification.environment logical) ↔
      ∃ index, operand117.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields117 physical logical agreement]
  exact source_semantics117 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields118 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand118.input.fields physical = sourceFields118 logical := by
  have p316 : physical (.BaseLayerWitness 177) = logical 316 :=
    placed agreement (position := 316) (by kernel_rfl)
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
  have p330 : physical (.BaseLayerWitness 191) = logical 330 :=
    placed agreement (position := 330) (by kernel_rfl)
  have p331 : physical (.BaseLayerWitness 192) = logical 331 :=
    placed agreement (position := 331) (by kernel_rfl)
  have p333 : physical (.BaseLayerWitness 194) = logical 333 :=
    placed agreement (position := 333) (by kernel_rfl)
  simp only [operand118, NativeLookups.Input.fields, sourceFields118, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p316, p189, p302, p303, p308, p311, p325, p326, p329, p330, p331, p333]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement118 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup118).Contains (Verification.environment logical) ↔
      ∃ index, operand118.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields118 physical logical agreement]
  exact source_semantics118 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields119 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand119.input.fields physical = sourceFields119 logical := by
  have p318 : physical (.BaseLayerWitness 179) = logical 318 :=
    placed agreement (position := 318) (by kernel_rfl)
  have p328 : physical (.BaseLayerWitness 189) = logical 328 :=
    placed agreement (position := 328) (by kernel_rfl)
  have p334 : physical (.BaseLayerWitness 195) = logical 334 :=
    placed agreement (position := 334) (by kernel_rfl)
  simp only [operand119, NativeLookups.Input.fields, sourceFields119, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p318, p328, p334]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement119 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup119).Contains (Verification.environment logical) ↔
      ∃ index, operand119.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields119 physical logical agreement]
  exact source_semantics119 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
