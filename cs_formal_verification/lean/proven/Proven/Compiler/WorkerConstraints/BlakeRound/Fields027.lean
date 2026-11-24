module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries018

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields216 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand216.input.fields physical = sourceFields216 logical := by
  have p527 : physical (.BaseLayerWitness 388) = logical 527 :=
    placed agreement (position := 527) (by kernel_rfl)
  have p533 : physical (.BaseLayerWitness 394) = logical 533 :=
    placed agreement (position := 533) (by kernel_rfl)
  have p75 : physical (.BaseLayerMemory 110) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p76 : physical (.BaseLayerMemory 111) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p95 : physical (.BaseLayerMemory 140) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p96 : physical (.BaseLayerMemory 141) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p188 : physical (.BaseLayerWitness 49) = logical 188 :=
    placed agreement (position := 188) (by kernel_rfl)
  have p189 : physical (.BaseLayerWitness 50) = logical 189 :=
    placed agreement (position := 189) (by kernel_rfl)
  have p302 : physical (.BaseLayerWitness 163) = logical 302 :=
    placed agreement (position := 302) (by kernel_rfl)
  have p303 : physical (.BaseLayerWitness 164) = logical 303 :=
    placed agreement (position := 303) (by kernel_rfl)
  have p304 : physical (.BaseLayerWitness 165) = logical 304 :=
    placed agreement (position := 304) (by kernel_rfl)
  have p305 : physical (.BaseLayerWitness 166) = logical 305 :=
    placed agreement (position := 305) (by kernel_rfl)
  have p311 : physical (.BaseLayerWitness 172) = logical 311 :=
    placed agreement (position := 311) (by kernel_rfl)
  have p324 : physical (.BaseLayerWitness 185) = logical 324 :=
    placed agreement (position := 324) (by kernel_rfl)
  have p325 : physical (.BaseLayerWitness 186) = logical 325 :=
    placed agreement (position := 325) (by kernel_rfl)
  have p326 : physical (.BaseLayerWitness 187) = logical 326 :=
    placed agreement (position := 326) (by kernel_rfl)
  have p327 : physical (.BaseLayerWitness 188) = logical 327 :=
    placed agreement (position := 327) (by kernel_rfl)
  have p331 : physical (.BaseLayerWitness 192) = logical 331 :=
    placed agreement (position := 331) (by kernel_rfl)
  have p510 : physical (.BaseLayerWitness 371) = logical 510 :=
    placed agreement (position := 510) (by kernel_rfl)
  have p511 : physical (.BaseLayerWitness 372) = logical 511 :=
    placed agreement (position := 511) (by kernel_rfl)
  have p512 : physical (.BaseLayerWitness 373) = logical 512 :=
    placed agreement (position := 512) (by kernel_rfl)
  have p513 : physical (.BaseLayerWitness 374) = logical 513 :=
    placed agreement (position := 513) (by kernel_rfl)
  have p519 : physical (.BaseLayerWitness 380) = logical 519 :=
    placed agreement (position := 519) (by kernel_rfl)
  have p55 : physical (.BaseLayerMemory 80) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  have p534 : physical (.BaseLayerWitness 395) = logical 534 :=
    placed agreement (position := 534) (by kernel_rfl)
  simp only [operand216, NativeLookups.Input.fields, sourceFields216, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p527, p533, p75, p76, p95, p96, p188, p189, p302, p303, p304, p305, p311, p324, p325, p326, p327, p331, p510, p511, p512, p513, p519, p55, p534]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement216 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup216).Contains (Verification.environment logical) ↔
      ∃ index, operand216.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields216 physical logical agreement]
  exact source_semantics216 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields217 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand217.input.fields physical = sourceFields217 logical := by
  have p536 : physical (.BaseLayerWitness 397) = logical 536 :=
    placed agreement (position := 536) (by kernel_rfl)
  have p502 : physical (.BaseLayerWitness 363) = logical 502 :=
    placed agreement (position := 502) (by kernel_rfl)
  have p537 : physical (.BaseLayerWitness 398) = logical 537 :=
    placed agreement (position := 537) (by kernel_rfl)
  simp only [operand217, NativeLookups.Input.fields, sourceFields217, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p536, p502, p537]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement217 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup217).Contains (Verification.environment logical) ↔
      ∃ index, operand217.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields217 physical logical agreement]
  exact source_semantics217 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields218 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand218.input.fields physical = sourceFields218 logical := by
  have p154 : physical (.BaseLayerWitness 15) = logical 154 :=
    placed agreement (position := 154) (by kernel_rfl)
  have p536 : physical (.BaseLayerWitness 397) = logical 536 :=
    placed agreement (position := 536) (by kernel_rfl)
  have p71 : physical (.BaseLayerMemory 104) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p502 : physical (.BaseLayerWitness 363) = logical 502 :=
    placed agreement (position := 502) (by kernel_rfl)
  have p538 : physical (.BaseLayerWitness 399) = logical 538 :=
    placed agreement (position := 538) (by kernel_rfl)
  simp only [operand218, NativeLookups.Input.fields, sourceFields218, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p154, p536, p71, p502, p538]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement218 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup218).Contains (Verification.environment logical) ↔
      ∃ index, operand218.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields218 physical logical agreement]
  exact source_semantics218 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields219 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand219.input.fields physical = sourceFields219 logical := by
  have p537 : physical (.BaseLayerWitness 398) = logical 537 :=
    placed agreement (position := 537) (by kernel_rfl)
  have p438 : physical (.BaseLayerWitness 299) = logical 438 :=
    placed agreement (position := 438) (by kernel_rfl)
  have p539 : physical (.BaseLayerWitness 400) = logical 539 :=
    placed agreement (position := 539) (by kernel_rfl)
  have p540 : physical (.BaseLayerWitness 401) = logical 540 :=
    placed agreement (position := 540) (by kernel_rfl)
  simp only [operand219, NativeLookups.Input.fields, sourceFields219, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p537, p438, p539, p540]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement219 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup219).Contains (Verification.environment logical) ↔
      ∃ index, operand219.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields219 physical logical agreement]
  exact source_semantics219 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields220 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand220.input.fields physical = sourceFields220 logical := by
  have p538 : physical (.BaseLayerWitness 399) = logical 538 :=
    placed agreement (position := 538) (by kernel_rfl)
  have p39 : physical (.BaseLayerMemory 56) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p438 : physical (.BaseLayerWitness 299) = logical 438 :=
    placed agreement (position := 438) (by kernel_rfl)
  have p539 : physical (.BaseLayerWitness 400) = logical 539 :=
    placed agreement (position := 539) (by kernel_rfl)
  have p541 : physical (.BaseLayerWitness 402) = logical 541 :=
    placed agreement (position := 541) (by kernel_rfl)
  simp only [operand220, NativeLookups.Input.fields, sourceFields220, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p538, p39, p438, p539, p541]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement220 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup220).Contains (Verification.environment logical) ↔
      ∃ index, operand220.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields220 physical logical agreement]
  exact source_semantics220 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields221 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand221.input.fields physical = sourceFields221 logical := by
  have p542 : physical (.BaseLayerWitness 403) = logical 542 :=
    placed agreement (position := 542) (by kernel_rfl)
  have p503 : physical (.BaseLayerWitness 364) = logical 503 :=
    placed agreement (position := 503) (by kernel_rfl)
  have p543 : physical (.BaseLayerWitness 404) = logical 543 :=
    placed agreement (position := 543) (by kernel_rfl)
  simp only [operand221, NativeLookups.Input.fields, sourceFields221, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p542, p503, p543]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement221 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup221).Contains (Verification.environment logical) ↔
      ∃ index, operand221.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields221 physical logical agreement]
  exact source_semantics221 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields222 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand222.input.fields physical = sourceFields222 logical := by
  have p156 : physical (.BaseLayerWitness 17) = logical 156 :=
    placed agreement (position := 156) (by kernel_rfl)
  have p542 : physical (.BaseLayerWitness 403) = logical 542 :=
    placed agreement (position := 542) (by kernel_rfl)
  have p72 : physical (.BaseLayerMemory 105) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p503 : physical (.BaseLayerWitness 364) = logical 503 :=
    placed agreement (position := 503) (by kernel_rfl)
  have p544 : physical (.BaseLayerWitness 405) = logical 544 :=
    placed agreement (position := 544) (by kernel_rfl)
  simp only [operand222, NativeLookups.Input.fields, sourceFields222, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p156, p542, p72, p503, p544]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement222 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup222).Contains (Verification.environment logical) ↔
      ∃ index, operand222.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields222 physical logical agreement]
  exact source_semantics222 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields223 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    operand223.input.fields physical = sourceFields223 logical := by
  have p543 : physical (.BaseLayerWitness 404) = logical 543 :=
    placed agreement (position := 543) (by kernel_rfl)
  have p439 : physical (.BaseLayerWitness 300) = logical 439 :=
    placed agreement (position := 439) (by kernel_rfl)
  have p545 : physical (.BaseLayerWitness 406) = logical 545 :=
    placed agreement (position := 545) (by kernel_rfl)
  have p546 : physical (.BaseLayerWitness 407) = logical 546 :=
    placed agreement (position := 546) (by kernel_rfl)
  simp only [operand223, NativeLookups.Input.fields, sourceFields223, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p543, p439, p545, p546]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement223 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical) :
    (sourceLookup223).Contains (Verification.environment logical) ↔
      ∃ index, operand223.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  rw [fields223 physical logical agreement]
  exact source_semantics223 logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
