module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries002
public import Proven.Compiler.WorkerConstraints.Bigint.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand32.input.fields physical = sourceFields32 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p240 : physical (.BaseLayerMemory 46) = logical 240 :=
    placed agreement (position := 240) (by kernel_rfl)
  have p242 : physical (.BaseLayerWitness 146) = logical 242 :=
    placed agreement (position := 242) (by kernel_rfl)
  simp only [operand32, NativeLookups.Input.fields, sourceFields32]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p240, p242]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields32 physical logical agreement]
  exact source_semantics32 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand33.input.fields physical = sourceFields33 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p241 : physical (.BaseLayerMemory 47) = logical 241 :=
    placed agreement (position := 241) (by kernel_rfl)
  have p242 : physical (.BaseLayerWitness 146) = logical 242 :=
    placed agreement (position := 242) (by kernel_rfl)
  simp only [operand33, NativeLookups.Input.fields, sourceFields33]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p241, p242]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields33 physical logical agreement]
  exact source_semantics33 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand34.input.fields physical = sourceFields34 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p243 : physical (.BaseLayerMemory 52) = logical 243 :=
    placed agreement (position := 243) (by kernel_rfl)
  have p245 : physical (.BaseLayerWitness 147) = logical 245 :=
    placed agreement (position := 245) (by kernel_rfl)
  simp only [operand34, NativeLookups.Input.fields, sourceFields34]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p243, p245]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields34 physical logical agreement]
  exact source_semantics34 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand35.input.fields physical = sourceFields35 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p244 : physical (.BaseLayerMemory 53) = logical 244 :=
    placed agreement (position := 244) (by kernel_rfl)
  have p245 : physical (.BaseLayerWitness 147) = logical 245 :=
    placed agreement (position := 245) (by kernel_rfl)
  simp only [operand35, NativeLookups.Input.fields, sourceFields35]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p244, p245]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields35 physical logical agreement]
  exact source_semantics35 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand36.input.fields physical = sourceFields36 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p246 : physical (.BaseLayerMemory 56) = logical 246 :=
    placed agreement (position := 246) (by kernel_rfl)
  have p248 : physical (.BaseLayerWitness 148) = logical 248 :=
    placed agreement (position := 248) (by kernel_rfl)
  simp only [operand36, NativeLookups.Input.fields, sourceFields36]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p246, p248]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields36 physical logical agreement]
  exact source_semantics36 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand37.input.fields physical = sourceFields37 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p247 : physical (.BaseLayerMemory 57) = logical 247 :=
    placed agreement (position := 247) (by kernel_rfl)
  have p248 : physical (.BaseLayerWitness 148) = logical 248 :=
    placed agreement (position := 248) (by kernel_rfl)
  simp only [operand37, NativeLookups.Input.fields, sourceFields37]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p247, p248]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields37 physical logical agreement]
  exact source_semantics37 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand38.input.fields physical = sourceFields38 logical := by
  have p1 : physical (.BaseLayerMemory 95) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p249 : physical (.BaseLayerMemory 60) = logical 249 :=
    placed agreement (position := 249) (by kernel_rfl)
  have p251 : physical (.BaseLayerWitness 149) = logical 251 :=
    placed agreement (position := 251) (by kernel_rfl)
  simp only [operand38, NativeLookups.Input.fields, sourceFields38]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p249, p251]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields38 physical logical agreement]
  exact source_semantics38 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand39.input.fields physical = sourceFields39 logical := by
  have p2 : physical (.BaseLayerMemory 96) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p250 : physical (.BaseLayerMemory 61) = logical 250 :=
    placed agreement (position := 250) (by kernel_rfl)
  have p251 : physical (.BaseLayerWitness 149) = logical 251 :=
    placed agreement (position := 251) (by kernel_rfl)
  simp only [operand39, NativeLookups.Input.fields, sourceFields39]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p250, p251]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  rw [fields39 physical logical agreement]
  exact source_semantics39 logical


end Airbender.Compiler.WorkerConstraints.Bigint
