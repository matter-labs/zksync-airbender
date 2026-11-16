module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries008
public import Proven.Compiler.WorkerConstraints.Bigint.Queries009

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields104 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand104.input.fields physical = sourceFields104 logical := by
  have p141 : physical (.BaseLayerWitness 82) = logical 141 :=
    placed agreement (position := 141) (by kernel_rfl)
  have p173 : physical (.BaseLayerWitness 114) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  simp only [operand104, NativeLookups.Input.fields, sourceFields104, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p141, p173]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement104 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup104).Contains (Verification.environment logical) ↔
      ∃ index, operand104.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields104 physical logical agreement]
  exact source_semantics104 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields105 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand105.input.fields physical = sourceFields105 logical := by
  have p142 : physical (.BaseLayerWitness 83) = logical 142 :=
    placed agreement (position := 142) (by kernel_rfl)
  have p174 : physical (.BaseLayerWitness 115) = logical 174 :=
    placed agreement (position := 174) (by kernel_rfl)
  simp only [operand105, NativeLookups.Input.fields, sourceFields105, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p142, p174]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement105 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup105).Contains (Verification.environment logical) ↔
      ∃ index, operand105.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields105 physical logical agreement]
  exact source_semantics105 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields106 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand106.input.fields physical = sourceFields106 logical := by
  have p143 : physical (.BaseLayerWitness 84) = logical 143 :=
    placed agreement (position := 143) (by kernel_rfl)
  have p175 : physical (.BaseLayerWitness 116) = logical 175 :=
    placed agreement (position := 175) (by kernel_rfl)
  simp only [operand106, NativeLookups.Input.fields, sourceFields106, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p143, p175]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement106 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup106).Contains (Verification.environment logical) ↔
      ∃ index, operand106.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields106 physical logical agreement]
  exact source_semantics106 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields107 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand107.input.fields physical = sourceFields107 logical := by
  have p144 : physical (.BaseLayerWitness 85) = logical 144 :=
    placed agreement (position := 144) (by kernel_rfl)
  have p176 : physical (.BaseLayerWitness 117) = logical 176 :=
    placed agreement (position := 176) (by kernel_rfl)
  simp only [operand107, NativeLookups.Input.fields, sourceFields107, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p144, p176]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement107 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup107).Contains (Verification.environment logical) ↔
      ∃ index, operand107.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields107 physical logical agreement]
  exact source_semantics107 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields108 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand108.input.fields physical = sourceFields108 logical := by
  have p145 : physical (.BaseLayerWitness 86) = logical 145 :=
    placed agreement (position := 145) (by kernel_rfl)
  have p177 : physical (.BaseLayerWitness 118) = logical 177 :=
    placed agreement (position := 177) (by kernel_rfl)
  simp only [operand108, NativeLookups.Input.fields, sourceFields108, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p145, p177]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement108 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup108).Contains (Verification.environment logical) ↔
      ∃ index, operand108.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields108 physical logical agreement]
  exact source_semantics108 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields109 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand109.input.fields physical = sourceFields109 logical := by
  have p146 : physical (.BaseLayerWitness 87) = logical 146 :=
    placed agreement (position := 146) (by kernel_rfl)
  have p178 : physical (.BaseLayerWitness 119) = logical 178 :=
    placed agreement (position := 178) (by kernel_rfl)
  simp only [operand109, NativeLookups.Input.fields, sourceFields109, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p146, p178]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement109 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup109).Contains (Verification.environment logical) ↔
      ∃ index, operand109.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields109 physical logical agreement]
  exact source_semantics109 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields110 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand110.input.fields physical = sourceFields110 logical := by
  have p147 : physical (.BaseLayerWitness 88) = logical 147 :=
    placed agreement (position := 147) (by kernel_rfl)
  have p179 : physical (.BaseLayerWitness 120) = logical 179 :=
    placed agreement (position := 179) (by kernel_rfl)
  simp only [operand110, NativeLookups.Input.fields, sourceFields110, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p147, p179]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement110 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup110).Contains (Verification.environment logical) ↔
      ∃ index, operand110.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields110 physical logical agreement]
  exact source_semantics110 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields111 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand111.input.fields physical = sourceFields111 logical := by
  have p148 : physical (.BaseLayerWitness 89) = logical 148 :=
    placed agreement (position := 148) (by kernel_rfl)
  have p180 : physical (.BaseLayerWitness 121) = logical 180 :=
    placed agreement (position := 180) (by kernel_rfl)
  simp only [operand111, NativeLookups.Input.fields, sourceFields111, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p148, p180]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement111 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup111).Contains (Verification.environment logical) ↔
      ∃ index, operand111.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields111 physical logical agreement]
  exact source_semantics111 logical


end Airbender.Compiler.WorkerConstraints.Bigint
