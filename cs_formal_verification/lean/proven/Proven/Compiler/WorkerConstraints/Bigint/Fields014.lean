module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries009

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields112 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand112.input.fields physical = sourceFields112 logical := by
  have p149 : physical (.BaseLayerWitness 90) = logical 149 :=
    placed agreement (position := 149) (by kernel_rfl)
  have p181 : physical (.BaseLayerWitness 122) = logical 181 :=
    placed agreement (position := 181) (by kernel_rfl)
  simp only [operand112, NativeLookups.Input.fields, sourceFields112, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p149, p181]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement112 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup112).Contains (Verification.environment logical) ↔
      ∃ index, operand112.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields112 physical logical agreement]
  exact source_semantics112 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields113 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand113.input.fields physical = sourceFields113 logical := by
  have p150 : physical (.BaseLayerWitness 91) = logical 150 :=
    placed agreement (position := 150) (by kernel_rfl)
  have p182 : physical (.BaseLayerWitness 123) = logical 182 :=
    placed agreement (position := 182) (by kernel_rfl)
  simp only [operand113, NativeLookups.Input.fields, sourceFields113, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p150, p182]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement113 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup113).Contains (Verification.environment logical) ↔
      ∃ index, operand113.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields113 physical logical agreement]
  exact source_semantics113 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields114 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand114.input.fields physical = sourceFields114 logical := by
  have p151 : physical (.BaseLayerWitness 92) = logical 151 :=
    placed agreement (position := 151) (by kernel_rfl)
  have p183 : physical (.BaseLayerWitness 124) = logical 183 :=
    placed agreement (position := 183) (by kernel_rfl)
  simp only [operand114, NativeLookups.Input.fields, sourceFields114, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p151, p183]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement114 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup114).Contains (Verification.environment logical) ↔
      ∃ index, operand114.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields114 physical logical agreement]
  exact source_semantics114 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields115 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand115.input.fields physical = sourceFields115 logical := by
  have p152 : physical (.BaseLayerWitness 93) = logical 152 :=
    placed agreement (position := 152) (by kernel_rfl)
  have p184 : physical (.BaseLayerWitness 125) = logical 184 :=
    placed agreement (position := 184) (by kernel_rfl)
  simp only [operand115, NativeLookups.Input.fields, sourceFields115, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p152, p184]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement115 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup115).Contains (Verification.environment logical) ↔
      ∃ index, operand115.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields115 physical logical agreement]
  exact source_semantics115 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields116 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand116.input.fields physical = sourceFields116 logical := by
  have p153 : physical (.BaseLayerWitness 94) = logical 153 :=
    placed agreement (position := 153) (by kernel_rfl)
  have p185 : physical (.BaseLayerWitness 126) = logical 185 :=
    placed agreement (position := 185) (by kernel_rfl)
  simp only [operand116, NativeLookups.Input.fields, sourceFields116, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p153, p185]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement116 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup116).Contains (Verification.environment logical) ↔
      ∃ index, operand116.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  rw [fields116 physical logical agreement]
  exact source_semantics116 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields117 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand117.input.fields physical = sourceFields117 logical := by
  have p194 : physical (.InnerLayer 1 21) = logical 194 :=
    placed agreement (position := 194) (by kernel_rfl)
  simp only [operand117, NativeLookups.Input.fields, sourceFields117]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p194]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement117 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup117).Contains (Verification.environment logical) ↔
      ∃ index, operand117.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields117 physical logical agreement]
  exact source_semantics117 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields118 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand118.input.fields physical = sourceFields118 logical := by
  have p195 : physical (.InnerLayer 1 22) = logical 195 :=
    placed agreement (position := 195) (by kernel_rfl)
  simp only [operand118, NativeLookups.Input.fields, sourceFields118]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p195]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement118 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup118).Contains (Verification.environment logical) ↔
      ∃ index, operand118.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields118 physical logical agreement]
  exact source_semantics118 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields119 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    operand119.input.fields physical = sourceFields119 logical := by
  have p196 : physical (.InnerLayer 1 23) = logical 196 :=
    placed agreement (position := 196) (by kernel_rfl)
  simp only [operand119, NativeLookups.Input.fields, sourceFields119]
  simp only [Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p196]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement119 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical) :
    (sourceLookup119).Contains (Verification.environment logical) ↔
      ∃ index, operand119.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  rw [fields119 physical logical agreement]
  exact source_semantics119 logical


end Airbender.Compiler.WorkerConstraints.Bigint
