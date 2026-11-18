module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries004
public import Proven.Compiler.WorkerConstraints.Bigint.Queries005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields56 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand56.input.fields physical = sourceFields56 logical := by
  have p5 : physical (.BaseLayerMemory 6) = logical 5 :=
    placed agreement (position := 5) (by kernel_rfl)
  have p99 : physical (.BaseLayerWitness 40) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  simp only [operand56, NativeLookups.Input.fields, sourceFields56, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p5, p99]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement56 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup56).Contains (Verification.environment logical) ↔
      ∃ index, operand56.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields56 physical logical agreement]
  exact source_semantics56 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields57 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand57.input.fields physical = sourceFields57 logical := by
  have p6 : physical (.BaseLayerMemory 7) = logical 6 :=
    placed agreement (position := 6) (by kernel_rfl)
  have p100 : physical (.BaseLayerWitness 41) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  simp only [operand57, NativeLookups.Input.fields, sourceFields57, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p6, p100]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement57 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup57).Contains (Verification.environment logical) ↔
      ∃ index, operand57.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields57 physical logical agreement]
  exact source_semantics57 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields58 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand58.input.fields physical = sourceFields58 logical := by
  have p9 : physical (.BaseLayerMemory 12) = logical 9 :=
    placed agreement (position := 9) (by kernel_rfl)
  have p101 : physical (.BaseLayerWitness 42) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  simp only [operand58, NativeLookups.Input.fields, sourceFields58, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p9, p101]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement58 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup58).Contains (Verification.environment logical) ↔
      ∃ index, operand58.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields58 physical logical agreement]
  exact source_semantics58 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields59 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand59.input.fields physical = sourceFields59 logical := by
  have p10 : physical (.BaseLayerMemory 13) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p102 : physical (.BaseLayerWitness 43) = logical 102 :=
    placed agreement (position := 102) (by kernel_rfl)
  simp only [operand59, NativeLookups.Input.fields, sourceFields59, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p10, p102]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement59 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup59).Contains (Verification.environment logical) ↔
      ∃ index, operand59.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields59 physical logical agreement]
  exact source_semantics59 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields60 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand60.input.fields physical = sourceFields60 logical := by
  have p13 : physical (.BaseLayerMemory 18) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  have p103 : physical (.BaseLayerWitness 44) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  simp only [operand60, NativeLookups.Input.fields, sourceFields60, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p13, p103]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement60 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup60).Contains (Verification.environment logical) ↔
      ∃ index, operand60.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields60 physical logical agreement]
  exact source_semantics60 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields61 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand61.input.fields physical = sourceFields61 logical := by
  have p14 : physical (.BaseLayerMemory 19) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  have p104 : physical (.BaseLayerWitness 45) = logical 104 :=
    placed agreement (position := 104) (by kernel_rfl)
  simp only [operand61, NativeLookups.Input.fields, sourceFields61, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p14, p104]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement61 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup61).Contains (Verification.environment logical) ↔
      ∃ index, operand61.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields61 physical logical agreement]
  exact source_semantics61 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields62 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand62.input.fields physical = sourceFields62 logical := by
  have p17 : physical (.BaseLayerMemory 24) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  have p105 : physical (.BaseLayerWitness 46) = logical 105 :=
    placed agreement (position := 105) (by kernel_rfl)
  simp only [operand62, NativeLookups.Input.fields, sourceFields62, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p17, p105]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement62 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup62).Contains (Verification.environment logical) ↔
      ∃ index, operand62.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields62 physical logical agreement]
  exact source_semantics62 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields63 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand63.input.fields physical = sourceFields63 logical := by
  have p18 : physical (.BaseLayerMemory 25) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  have p106 : physical (.BaseLayerWitness 47) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  simp only [operand63, NativeLookups.Input.fields, sourceFields63, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p18, p106]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement63 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup63).Contains (Verification.environment logical) ↔
      ∃ index, operand63.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields63 physical logical agreement]
  exact source_semantics63 logical


end Airbender.Compiler.WorkerConstraints.Bigint
