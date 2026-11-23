module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries006
public import Proven.Compiler.WorkerConstraints.Bigint.Queries007

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields80 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand80.input.fields physical = sourceFields80 logical := by
  have p47 : physical (.BaseLayerMemory 74) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p123 : physical (.BaseLayerWitness 64) = logical 123 :=
    placed agreement (position := 123) (by kernel_rfl)
  simp only [operand80, NativeLookups.Input.fields, sourceFields80, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p47, p123]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement80 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup80).Contains (Verification.environment logical) ↔
      ∃ index, operand80.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields80 physical logical agreement]
  exact source_semantics80 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields81 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand81.input.fields physical = sourceFields81 logical := by
  have p48 : physical (.BaseLayerMemory 75) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p124 : physical (.BaseLayerWitness 65) = logical 124 :=
    placed agreement (position := 124) (by kernel_rfl)
  simp only [operand81, NativeLookups.Input.fields, sourceFields81, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p48, p124]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement81 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup81).Contains (Verification.environment logical) ↔
      ∃ index, operand81.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields81 physical logical agreement]
  exact source_semantics81 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields82 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand82.input.fields physical = sourceFields82 logical := by
  have p49 : physical (.BaseLayerMemory 78) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  have p125 : physical (.BaseLayerWitness 66) = logical 125 :=
    placed agreement (position := 125) (by kernel_rfl)
  simp only [operand82, NativeLookups.Input.fields, sourceFields82, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p49, p125]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement82 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup82).Contains (Verification.environment logical) ↔
      ∃ index, operand82.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields82 physical logical agreement]
  exact source_semantics82 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields83 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand83.input.fields physical = sourceFields83 logical := by
  have p50 : physical (.BaseLayerMemory 79) = logical 50 :=
    placed agreement (position := 50) (by kernel_rfl)
  have p126 : physical (.BaseLayerWitness 67) = logical 126 :=
    placed agreement (position := 126) (by kernel_rfl)
  simp only [operand83, NativeLookups.Input.fields, sourceFields83, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p50, p126]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement83 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup83).Contains (Verification.environment logical) ↔
      ∃ index, operand83.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields83 physical logical agreement]
  exact source_semantics83 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields84 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand84.input.fields physical = sourceFields84 logical := by
  have p51 : physical (.BaseLayerMemory 82) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p127 : physical (.BaseLayerWitness 68) = logical 127 :=
    placed agreement (position := 127) (by kernel_rfl)
  simp only [operand84, NativeLookups.Input.fields, sourceFields84, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p51, p127]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement84 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup84).Contains (Verification.environment logical) ↔
      ∃ index, operand84.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields84 physical logical agreement]
  exact source_semantics84 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields85 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand85.input.fields physical = sourceFields85 logical := by
  have p52 : physical (.BaseLayerMemory 83) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p128 : physical (.BaseLayerWitness 69) = logical 128 :=
    placed agreement (position := 128) (by kernel_rfl)
  simp only [operand85, NativeLookups.Input.fields, sourceFields85, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p52, p128]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement85 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup85).Contains (Verification.environment logical) ↔
      ∃ index, operand85.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields85 physical logical agreement]
  exact source_semantics85 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields86 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand86.input.fields physical = sourceFields86 logical := by
  have p53 : physical (.BaseLayerMemory 86) = logical 53 :=
    placed agreement (position := 53) (by kernel_rfl)
  have p129 : physical (.BaseLayerWitness 70) = logical 129 :=
    placed agreement (position := 129) (by kernel_rfl)
  simp only [operand86, NativeLookups.Input.fields, sourceFields86, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p53, p129]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement86 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup86).Contains (Verification.environment logical) ↔
      ∃ index, operand86.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields86 physical logical agreement]
  exact source_semantics86 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields87 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand87.input.fields physical = sourceFields87 logical := by
  have p54 : physical (.BaseLayerMemory 87) = logical 54 :=
    placed agreement (position := 54) (by kernel_rfl)
  have p130 : physical (.BaseLayerWitness 71) = logical 130 :=
    placed agreement (position := 130) (by kernel_rfl)
  simp only [operand87, NativeLookups.Input.fields, sourceFields87, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p54, p130]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement87 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup87).Contains (Verification.environment logical) ↔
      ∃ index, operand87.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields87 physical logical agreement]
  exact source_semantics87 logical


end Airbender.Compiler.WorkerConstraints.Bigint
