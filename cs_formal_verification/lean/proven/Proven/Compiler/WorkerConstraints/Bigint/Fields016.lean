module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries010
public import Proven.Compiler.WorkerConstraints.Bigint.Queries011

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields128 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand128.input.fields physical = sourceFields128 logical := by
  have p205 : physical (.InnerLayer 1 32) = logical 205 :=
    placed agreement (position := 205) (by kernel_rfl)
  simp only [operand128, NativeLookups.Input.fields, sourceFields128]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p205]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement128 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup128).Contains (Verification.environment logical) ↔
      ∃ index, operand128.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields128 physical logical agreement]
  exact source_semantics128 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields129 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand129.input.fields physical = sourceFields129 logical := by
  have p206 : physical (.InnerLayer 1 33) = logical 206 :=
    placed agreement (position := 206) (by kernel_rfl)
  simp only [operand129, NativeLookups.Input.fields, sourceFields129]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p206]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement129 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup129).Contains (Verification.environment logical) ↔
      ∃ index, operand129.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields129 physical logical agreement]
  exact source_semantics129 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields130 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand130.input.fields physical = sourceFields130 logical := by
  have p207 : physical (.InnerLayer 1 34) = logical 207 :=
    placed agreement (position := 207) (by kernel_rfl)
  simp only [operand130, NativeLookups.Input.fields, sourceFields130]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p207]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement130 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup130).Contains (Verification.environment logical) ↔
      ∃ index, operand130.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields130 physical logical agreement]
  exact source_semantics130 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields131 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand131.input.fields physical = sourceFields131 logical := by
  have p208 : physical (.InnerLayer 1 35) = logical 208 :=
    placed agreement (position := 208) (by kernel_rfl)
  simp only [operand131, NativeLookups.Input.fields, sourceFields131]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p208]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement131 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup131).Contains (Verification.environment logical) ↔
      ∃ index, operand131.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields131 physical logical agreement]
  exact source_semantics131 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields132 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand132.input.fields physical = sourceFields132 logical := by
  have p209 : physical (.InnerLayer 1 36) = logical 209 :=
    placed agreement (position := 209) (by kernel_rfl)
  simp only [operand132, NativeLookups.Input.fields, sourceFields132]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p209]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement132 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup132).Contains (Verification.environment logical) ↔
      ∃ index, operand132.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields132 physical logical agreement]
  exact source_semantics132 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields133 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand133.input.fields physical = sourceFields133 logical := by
  have p162 : physical (.BaseLayerWitness 103) = logical 162 :=
    placed agreement (position := 162) (by kernel_rfl)
  simp only [operand133, NativeLookups.Input.fields, sourceFields133]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p162]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement133 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup133).Contains (Verification.environment logical) ↔
      ∃ index, operand133.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields133 physical logical agreement]
  exact source_semantics133 logical


end Airbender.Compiler.WorkerConstraints.Bigint
