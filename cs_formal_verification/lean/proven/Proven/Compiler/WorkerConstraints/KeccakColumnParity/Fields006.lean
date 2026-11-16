module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand48.input.fields physical = sourceFields48 logical := by
  have p61 : physical (.BaseLayerWitness 14) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  have p73 : physical (.BaseLayerWitness 26) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 38) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p97 : physical (.BaseLayerWitness 50) = logical 97 :=
    placed agreement (position := 97) (by kernel_rfl)
  have p109 : physical (.BaseLayerWitness 62) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  have p121 : physical (.BaseLayerWitness 74) = logical 121 :=
    placed agreement (position := 121) (by kernel_rfl)
  simp only [operand48, NativeLookups.Input.fields, sourceFields48, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p61, p73, p85, p97, p109, p121]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup48).Contains (Verification.environment logical) ↔
      ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields48 physical logical agreement]
  exact source_semantics48 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand49.input.fields physical = sourceFields49 logical := by
  have p62 : physical (.BaseLayerWitness 15) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  have p74 : physical (.BaseLayerWitness 27) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 39) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p98 : physical (.BaseLayerWitness 51) = logical 98 :=
    placed agreement (position := 98) (by kernel_rfl)
  have p110 : physical (.BaseLayerWitness 63) = logical 110 :=
    placed agreement (position := 110) (by kernel_rfl)
  have p122 : physical (.BaseLayerWitness 75) = logical 122 :=
    placed agreement (position := 122) (by kernel_rfl)
  simp only [operand49, NativeLookups.Input.fields, sourceFields49, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p62, p74, p86, p98, p110, p122]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup49).Contains (Verification.environment logical) ↔
      ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields49 physical logical agreement]
  exact source_semantics49 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand50.input.fields physical = sourceFields50 logical := by
  have p13 : physical (.BaseLayerMemory 8) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  simp only [operand50, NativeLookups.Input.fields, sourceFields50]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p13]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup50).Contains (Verification.environment logical) ↔
      ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  rw [fields50 physical logical agreement]
  exact source_semantics50 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand51.input.fields physical = sourceFields51 logical := by
  have p22 : physical (.BaseLayerMemory 22) = logical 22 :=
    placed agreement (position := 22) (by kernel_rfl)
  have p60 : physical (.BaseLayerWitness 13) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p61 : physical (.BaseLayerWitness 14) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  have p62 : physical (.BaseLayerWitness 15) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  have p26 : physical (.BaseLayerMemory 31) = logical 26 :=
    placed agreement (position := 26) (by kernel_rfl)
  have p72 : physical (.BaseLayerWitness 25) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p73 : physical (.BaseLayerWitness 26) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  have p74 : physical (.BaseLayerWitness 27) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  have p30 : physical (.BaseLayerMemory 40) = logical 30 :=
    placed agreement (position := 30) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 37) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 38) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 39) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p34 : physical (.BaseLayerMemory 49) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  have p96 : physical (.BaseLayerWitness 49) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p97 : physical (.BaseLayerWitness 50) = logical 97 :=
    placed agreement (position := 97) (by kernel_rfl)
  have p98 : physical (.BaseLayerWitness 51) = logical 98 :=
    placed agreement (position := 98) (by kernel_rfl)
  have p38 : physical (.BaseLayerMemory 58) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  have p108 : physical (.BaseLayerWitness 61) = logical 108 :=
    placed agreement (position := 108) (by kernel_rfl)
  have p109 : physical (.BaseLayerWitness 62) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  have p110 : physical (.BaseLayerWitness 63) = logical 110 :=
    placed agreement (position := 110) (by kernel_rfl)
  have p46 : physical (.BaseLayerMemory 71) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  have p120 : physical (.BaseLayerWitness 73) = logical 120 :=
    placed agreement (position := 120) (by kernel_rfl)
  have p121 : physical (.BaseLayerWitness 74) = logical 121 :=
    placed agreement (position := 121) (by kernel_rfl)
  have p122 : physical (.BaseLayerWitness 75) = logical 122 :=
    placed agreement (position := 122) (by kernel_rfl)
  simp only [operand51, NativeLookups.Input.fields, sourceFields51, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p22, p60, p61, p62, p26, p72, p73, p74, p30, p84, p85, p86, p34, p96, p97, p98, p38, p108, p109, p110, p46, p120, p121, p122]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup51).Contains (Verification.environment logical) ↔
      ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields51 physical logical agreement]
  exact source_semantics51 logical


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
