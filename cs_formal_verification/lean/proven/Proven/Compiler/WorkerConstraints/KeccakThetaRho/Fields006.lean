module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand48.input.fields physical = sourceFields48 logical := by
  have p52 : physical (.BaseLayerMemory 51) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p171 : physical (.BaseLayerWitness 107) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 17) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p183 : physical (.BaseLayerWitness 119) = logical 183 :=
    placed agreement (position := 183) (by kernel_rfl)
  have p184 : physical (.BaseLayerWitness 120) = logical 184 :=
    placed agreement (position := 184) (by kernel_rfl)
  simp only [operand48, NativeLookups.Input.fields, sourceFields48, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p52, p171, p81, p84, p85, p86, p88, p183, p184]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup48).Contains (Verification.environment logical) ↔
      ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields48 physical logical agreement]
  exact source_semantics48 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand49.input.fields physical = sourceFields49 logical := by
  have p172 : physical (.BaseLayerWitness 108) = logical 172 :=
    placed agreement (position := 172) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 18) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p185 : physical (.BaseLayerWitness 121) = logical 185 :=
    placed agreement (position := 185) (by kernel_rfl)
  have p186 : physical (.BaseLayerWitness 122) = logical 186 :=
    placed agreement (position := 186) (by kernel_rfl)
  simp only [operand49, NativeLookups.Input.fields, sourceFields49, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p172, p82, p84, p85, p86, p88, p185, p186]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup49).Contains (Verification.environment logical) ↔
      ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields49 physical logical agreement]
  exact source_semantics49 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand50.input.fields physical = sourceFields50 logical := by
  have p14 : physical (.BaseLayerMemory 6) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  simp only [operand50, NativeLookups.Input.fields, sourceFields50]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p14]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup50).Contains (Verification.environment logical) ↔
      ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .thetaRho 2 index := by
  rw [fields50 physical logical agreement]
  exact source_semantics50 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand51.input.fields physical = sourceFields51 logical := by
  have p53 : physical (.BaseLayerMemory 52) = logical 53 :=
    placed agreement (position := 53) (by kernel_rfl)
  have p172 : physical (.BaseLayerWitness 108) = logical 172 :=
    placed agreement (position := 172) (by kernel_rfl)
  have p83 : physical (.BaseLayerWitness 19) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p187 : physical (.BaseLayerWitness 123) = logical 187 :=
    placed agreement (position := 187) (by kernel_rfl)
  have p188 : physical (.BaseLayerWitness 124) = logical 188 :=
    placed agreement (position := 188) (by kernel_rfl)
  simp only [operand51, NativeLookups.Input.fields, sourceFields51, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p53, p172, p83, p84, p85, p86, p88, p187, p188]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup51).Contains (Verification.environment logical) ↔
      ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields51 physical logical agreement]
  exact source_semantics51 logical


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
