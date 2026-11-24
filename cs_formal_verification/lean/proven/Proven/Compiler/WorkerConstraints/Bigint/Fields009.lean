module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields72 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand72.input.fields physical = sourceFields72 logical := by
  have p39 : physical (.BaseLayerMemory 58) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p115 : physical (.BaseLayerWitness 56) = logical 115 :=
    placed agreement (position := 115) (by kernel_rfl)
  simp only [operand72, NativeLookups.Input.fields, sourceFields72, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p39, p115]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement72 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup72).Contains (Verification.environment logical) ↔
      ∃ index, operand72.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields72 physical logical agreement]
  exact source_semantics72 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields73 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand73.input.fields physical = sourceFields73 logical := by
  have p40 : physical (.BaseLayerMemory 59) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p116 : physical (.BaseLayerWitness 57) = logical 116 :=
    placed agreement (position := 116) (by kernel_rfl)
  simp only [operand73, NativeLookups.Input.fields, sourceFields73, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p40, p116]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement73 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup73).Contains (Verification.environment logical) ↔
      ∃ index, operand73.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields73 physical logical agreement]
  exact source_semantics73 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields74 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand74.input.fields physical = sourceFields74 logical := by
  have p41 : physical (.BaseLayerMemory 62) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p117 : physical (.BaseLayerWitness 58) = logical 117 :=
    placed agreement (position := 117) (by kernel_rfl)
  simp only [operand74, NativeLookups.Input.fields, sourceFields74, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p41, p117]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement74 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup74).Contains (Verification.environment logical) ↔
      ∃ index, operand74.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields74 physical logical agreement]
  exact source_semantics74 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields75 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand75.input.fields physical = sourceFields75 logical := by
  have p42 : physical (.BaseLayerMemory 63) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  have p118 : physical (.BaseLayerWitness 59) = logical 118 :=
    placed agreement (position := 118) (by kernel_rfl)
  simp only [operand75, NativeLookups.Input.fields, sourceFields75, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p42, p118]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement75 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup75).Contains (Verification.environment logical) ↔
      ∃ index, operand75.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields75 physical logical agreement]
  exact source_semantics75 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields76 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand76.input.fields physical = sourceFields76 logical := by
  have p43 : physical (.BaseLayerMemory 66) = logical 43 :=
    placed agreement (position := 43) (by kernel_rfl)
  have p119 : physical (.BaseLayerWitness 60) = logical 119 :=
    placed agreement (position := 119) (by kernel_rfl)
  simp only [operand76, NativeLookups.Input.fields, sourceFields76, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p43, p119]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement76 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup76).Contains (Verification.environment logical) ↔
      ∃ index, operand76.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields76 physical logical agreement]
  exact source_semantics76 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields77 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand77.input.fields physical = sourceFields77 logical := by
  have p44 : physical (.BaseLayerMemory 67) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  have p120 : physical (.BaseLayerWitness 61) = logical 120 :=
    placed agreement (position := 120) (by kernel_rfl)
  simp only [operand77, NativeLookups.Input.fields, sourceFields77, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p44, p120]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement77 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup77).Contains (Verification.environment logical) ↔
      ∃ index, operand77.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields77 physical logical agreement]
  exact source_semantics77 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields78 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand78.input.fields physical = sourceFields78 logical := by
  have p45 : physical (.BaseLayerMemory 70) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  have p121 : physical (.BaseLayerWitness 62) = logical 121 :=
    placed agreement (position := 121) (by kernel_rfl)
  simp only [operand78, NativeLookups.Input.fields, sourceFields78, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p45, p121]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement78 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup78).Contains (Verification.environment logical) ↔
      ∃ index, operand78.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields78 physical logical agreement]
  exact source_semantics78 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields79 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand79.input.fields physical = sourceFields79 logical := by
  have p46 : physical (.BaseLayerMemory 71) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  have p122 : physical (.BaseLayerWitness 63) = logical 122 :=
    placed agreement (position := 122) (by kernel_rfl)
  simp only [operand79, NativeLookups.Input.fields, sourceFields79, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p46, p122]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement79 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup79).Contains (Verification.environment logical) ↔
      ∃ index, operand79.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields79 physical logical agreement]
  exact source_semantics79 logical


end Airbender.Compiler.WorkerConstraints.Bigint
