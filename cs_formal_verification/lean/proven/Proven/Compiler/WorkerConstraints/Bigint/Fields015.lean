module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries010

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields120 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand120.input.fields physical = sourceFields120 logical := by
  have p197 : physical (.InnerLayer 1 24) = logical 197 :=
    placed agreement (position := 197) (by kernel_rfl)
  simp only [operand120, NativeLookups.Input.fields, sourceFields120]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p197]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement120 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup120).Contains (Verification.environment logical) ↔
      ∃ index, operand120.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields120 physical logical agreement]
  exact source_semantics120 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields121 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand121.input.fields physical = sourceFields121 logical := by
  have p198 : physical (.InnerLayer 1 25) = logical 198 :=
    placed agreement (position := 198) (by kernel_rfl)
  simp only [operand121, NativeLookups.Input.fields, sourceFields121]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p198]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement121 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup121).Contains (Verification.environment logical) ↔
      ∃ index, operand121.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields121 physical logical agreement]
  exact source_semantics121 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields122 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand122.input.fields physical = sourceFields122 logical := by
  have p199 : physical (.InnerLayer 1 26) = logical 199 :=
    placed agreement (position := 199) (by kernel_rfl)
  simp only [operand122, NativeLookups.Input.fields, sourceFields122]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p199]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement122 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup122).Contains (Verification.environment logical) ↔
      ∃ index, operand122.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields122 physical logical agreement]
  exact source_semantics122 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields123 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand123.input.fields physical = sourceFields123 logical := by
  have p200 : physical (.InnerLayer 1 27) = logical 200 :=
    placed agreement (position := 200) (by kernel_rfl)
  simp only [operand123, NativeLookups.Input.fields, sourceFields123]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p200]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement123 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup123).Contains (Verification.environment logical) ↔
      ∃ index, operand123.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields123 physical logical agreement]
  exact source_semantics123 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields124 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand124.input.fields physical = sourceFields124 logical := by
  have p201 : physical (.InnerLayer 1 28) = logical 201 :=
    placed agreement (position := 201) (by kernel_rfl)
  simp only [operand124, NativeLookups.Input.fields, sourceFields124]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p201]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement124 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup124).Contains (Verification.environment logical) ↔
      ∃ index, operand124.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields124 physical logical agreement]
  exact source_semantics124 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields125 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand125.input.fields physical = sourceFields125 logical := by
  have p202 : physical (.InnerLayer 1 29) = logical 202 :=
    placed agreement (position := 202) (by kernel_rfl)
  simp only [operand125, NativeLookups.Input.fields, sourceFields125]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p202]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement125 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup125).Contains (Verification.environment logical) ↔
      ∃ index, operand125.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields125 physical logical agreement]
  exact source_semantics125 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields126 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand126.input.fields physical = sourceFields126 logical := by
  have p203 : physical (.InnerLayer 1 30) = logical 203 :=
    placed agreement (position := 203) (by kernel_rfl)
  simp only [operand126, NativeLookups.Input.fields, sourceFields126]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p203]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement126 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup126).Contains (Verification.environment logical) ↔
      ∃ index, operand126.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields126 physical logical agreement]
  exact source_semantics126 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields127 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand127.input.fields physical = sourceFields127 logical := by
  have p204 : physical (.InnerLayer 1 31) = logical 204 :=
    placed agreement (position := 204) (by kernel_rfl)
  simp only [operand127, NativeLookups.Input.fields, sourceFields127]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p204]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement127 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup127).Contains (Verification.environment logical) ↔
      ∃ index, operand127.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields127 physical logical agreement]
  exact source_semantics127 logical


end Airbender.Compiler.WorkerConstraints.Bigint
