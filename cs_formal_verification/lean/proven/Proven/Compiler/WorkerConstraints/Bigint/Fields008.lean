module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields64 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand64.input.fields physical = sourceFields64 logical := by
  have p21 : physical (.BaseLayerMemory 30) = logical 21 :=
    placed agreement (position := 21) (by kernel_rfl)
  have p107 : physical (.BaseLayerWitness 48) = logical 107 :=
    placed agreement (position := 107) (by kernel_rfl)
  simp only [operand64, NativeLookups.Input.fields, sourceFields64, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p21, p107]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement64 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup64).Contains (Verification.environment logical) ↔
      ∃ index, operand64.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields64 physical logical agreement]
  exact source_semantics64 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields65 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand65.input.fields physical = sourceFields65 logical := by
  have p22 : physical (.BaseLayerMemory 31) = logical 22 :=
    placed agreement (position := 22) (by kernel_rfl)
  have p108 : physical (.BaseLayerWitness 49) = logical 108 :=
    placed agreement (position := 108) (by kernel_rfl)
  simp only [operand65, NativeLookups.Input.fields, sourceFields65, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p22, p108]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement65 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup65).Contains (Verification.environment logical) ↔
      ∃ index, operand65.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields65 physical logical agreement]
  exact source_semantics65 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields66 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand66.input.fields physical = sourceFields66 logical := by
  have p25 : physical (.BaseLayerMemory 36) = logical 25 :=
    placed agreement (position := 25) (by kernel_rfl)
  have p109 : physical (.BaseLayerWitness 50) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  simp only [operand66, NativeLookups.Input.fields, sourceFields66, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p25, p109]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement66 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup66).Contains (Verification.environment logical) ↔
      ∃ index, operand66.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields66 physical logical agreement]
  exact source_semantics66 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields67 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand67.input.fields physical = sourceFields67 logical := by
  have p26 : physical (.BaseLayerMemory 37) = logical 26 :=
    placed agreement (position := 26) (by kernel_rfl)
  have p110 : physical (.BaseLayerWitness 51) = logical 110 :=
    placed agreement (position := 110) (by kernel_rfl)
  simp only [operand67, NativeLookups.Input.fields, sourceFields67, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p26, p110]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement67 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup67).Contains (Verification.environment logical) ↔
      ∃ index, operand67.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields67 physical logical agreement]
  exact source_semantics67 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields68 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand68.input.fields physical = sourceFields68 logical := by
  have p29 : physical (.BaseLayerMemory 42) = logical 29 :=
    placed agreement (position := 29) (by kernel_rfl)
  have p111 : physical (.BaseLayerWitness 52) = logical 111 :=
    placed agreement (position := 111) (by kernel_rfl)
  simp only [operand68, NativeLookups.Input.fields, sourceFields68, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p29, p111]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement68 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup68).Contains (Verification.environment logical) ↔
      ∃ index, operand68.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields68 physical logical agreement]
  exact source_semantics68 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields69 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand69.input.fields physical = sourceFields69 logical := by
  have p30 : physical (.BaseLayerMemory 43) = logical 30 :=
    placed agreement (position := 30) (by kernel_rfl)
  have p112 : physical (.BaseLayerWitness 53) = logical 112 :=
    placed agreement (position := 112) (by kernel_rfl)
  simp only [operand69, NativeLookups.Input.fields, sourceFields69, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p30, p112]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement69 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup69).Contains (Verification.environment logical) ↔
      ∃ index, operand69.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields69 physical logical agreement]
  exact source_semantics69 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields70 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand70.input.fields physical = sourceFields70 logical := by
  have p33 : physical (.BaseLayerMemory 48) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  have p113 : physical (.BaseLayerWitness 54) = logical 113 :=
    placed agreement (position := 113) (by kernel_rfl)
  simp only [operand70, NativeLookups.Input.fields, sourceFields70, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p33, p113]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement70 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup70).Contains (Verification.environment logical) ↔
      ∃ index, operand70.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields70 physical logical agreement]
  exact source_semantics70 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields71 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand71.input.fields physical = sourceFields71 logical := by
  have p34 : physical (.BaseLayerMemory 49) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  have p114 : physical (.BaseLayerWitness 55) = logical 114 :=
    placed agreement (position := 114) (by kernel_rfl)
  simp only [operand71, NativeLookups.Input.fields, sourceFields71, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p34, p114]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement71 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup71).Contains (Verification.environment logical) ↔
      ∃ index, operand71.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields71 physical logical agreement]
  exact source_semantics71 logical


end Airbender.Compiler.WorkerConstraints.Bigint
