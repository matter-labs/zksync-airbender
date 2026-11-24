module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand24.input.fields physical = sourceFields24 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p157 : physical (.BaseLayerMemory 56) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p158 : physical (.BaseLayerWitness 87) = logical 158 :=
    placed agreement (position := 158) (by kernel_rfl)
  simp only [operand24, NativeLookups.Input.fields, sourceFields24]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p157, p158]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields24 physical logical agreement]
  exact source_semantics24 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand25.input.fields physical = sourceFields25 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p159 : physical (.BaseLayerMemory 59) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 88) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  simp only [operand25, NativeLookups.Input.fields, sourceFields25]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p159, p161]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields25 physical logical agreement]
  exact source_semantics25 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand26.input.fields physical = sourceFields26 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p160 : physical (.BaseLayerMemory 60) = logical 160 :=
    placed agreement (position := 160) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 88) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  simp only [operand26, NativeLookups.Input.fields, sourceFields26]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p160, p161]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields26 physical logical agreement]
  exact source_semantics26 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand27.input.fields physical = sourceFields27 logical := by
  have p1 : physical (.BaseLayerMemory 73) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p162 : physical (.BaseLayerMemory 66) = logical 162 :=
    placed agreement (position := 162) (by kernel_rfl)
  have p164 : physical (.BaseLayerWitness 89) = logical 164 :=
    placed agreement (position := 164) (by kernel_rfl)
  simp only [operand27, NativeLookups.Input.fields, sourceFields27]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p162, p164]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields27 physical logical agreement]
  exact source_semantics27 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand28.input.fields physical = sourceFields28 logical := by
  have p2 : physical (.BaseLayerMemory 74) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p163 : physical (.BaseLayerMemory 67) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  have p164 : physical (.BaseLayerWitness 89) = logical 164 :=
    placed agreement (position := 164) (by kernel_rfl)
  simp only [operand28, NativeLookups.Input.fields, sourceFields28]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p163, p164]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields28 physical logical agreement]
  exact source_semantics28 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand29.input.fields physical = sourceFields29 logical := by
  have p0 : physical (.BaseLayerMemory 72) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p3 : physical (.BaseLayerMemory 2) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p7 : physical (.BaseLayerMemory 14) = logical 7 :=
    placed agreement (position := 7) (by kernel_rfl)
  have p8 : physical (.BaseLayerMemory 27) = logical 8 :=
    placed agreement (position := 8) (by kernel_rfl)
  have p9 : physical (.BaseLayerMemory 36) = logical 9 :=
    placed agreement (position := 9) (by kernel_rfl)
  have p10 : physical (.BaseLayerMemory 45) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p11 : physical (.BaseLayerMemory 54) = logical 11 :=
    placed agreement (position := 11) (by kernel_rfl)
  have p12 : physical (.BaseLayerMemory 63) = logical 12 :=
    placed agreement (position := 12) (by kernel_rfl)
  simp only [operand29, NativeLookups.Input.fields, sourceFields29, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p0, p3, p7, p8, p9, p10, p11, p12]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields29 physical logical agreement]
  exact source_semantics29 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand30.input.fields physical = sourceFields30 logical := by
  have p3 : physical (.BaseLayerMemory 2) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p0 : physical (.BaseLayerMemory 72) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p5 : physical (.BaseLayerMemory 4) = logical 5 :=
    placed agreement (position := 5) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 0) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  simp only [operand30, NativeLookups.Input.fields, sourceFields30, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p0, p5, p47]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields30 physical logical agreement]
  exact source_semantics30 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand31.input.fields physical = sourceFields31 logical := by
  have p48 : physical (.BaseLayerWitness 1) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 0) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p51 : physical (.BaseLayerWitness 4) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p52 : physical (.BaseLayerWitness 5) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  simp only [operand31, NativeLookups.Input.fields, sourceFields31, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p48, p47, p51, p52]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields31 physical logical agreement]
  exact source_semantics31 logical


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
