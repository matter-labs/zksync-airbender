module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries000

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p147 : physical (.BaseLayerWitness 88) = logical 147 :=
    placed agreement (position := 147) (by kernel_rfl)
  simp only [operand0, NativeLookups.Input.fields, sourceFields0]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p147]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup0).Contains (Verification.environment logical) ↔
      ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields0 physical logical agreement]
  exact source_semantics0 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p148 : physical (.BaseLayerWitness 89) = logical 148 :=
    placed agreement (position := 148) (by kernel_rfl)
  simp only [operand1, NativeLookups.Input.fields, sourceFields1]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p148]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields1 physical logical agreement]
  exact source_semantics1 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p149 : physical (.BaseLayerWitness 90) = logical 149 :=
    placed agreement (position := 149) (by kernel_rfl)
  simp only [operand2, NativeLookups.Input.fields, sourceFields2]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p149]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields2 physical logical agreement]
  exact source_semantics2 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p150 : physical (.BaseLayerWitness 91) = logical 150 :=
    placed agreement (position := 150) (by kernel_rfl)
  simp only [operand3, NativeLookups.Input.fields, sourceFields3]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p150]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields3 physical logical agreement]
  exact source_semantics3 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p151 : physical (.BaseLayerWitness 92) = logical 151 :=
    placed agreement (position := 151) (by kernel_rfl)
  simp only [operand4, NativeLookups.Input.fields, sourceFields4]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p151]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields4 physical logical agreement]
  exact source_semantics4 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p152 : physical (.BaseLayerWitness 93) = logical 152 :=
    placed agreement (position := 152) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p152]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields5 physical logical agreement]
  exact source_semantics5 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p153 : physical (.BaseLayerWitness 94) = logical 153 :=
    placed agreement (position := 153) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p153]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields6 physical logical agreement]
  exact source_semantics6 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p154 : physical (.BaseLayerWitness 95) = logical 154 :=
    placed agreement (position := 154) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p154]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields7 physical logical agreement]
  exact source_semantics7 logical


end Airbender.Compiler.WorkerConstraints.Bigint
