module
public import Proven.Compiler.WorkerConstraints.BlakeG.Queries002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand24.input.fields physical = sourceFields24 logical := by
  have p46 : physical (.BaseLayerWitness 9) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  have p42 : physical (.BaseLayerWitness 5) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 10) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  simp only [operand24, NativeLookups.Input.fields, sourceFields24, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p46, p42, p47]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields24 physical logical agreement]
  exact source_semantics24 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand25.input.fields physical = sourceFields25 logical := by
  have p28 : physical (.BaseLayerMemory 28) = logical 28 :=
    placed agreement (position := 28) (by kernel_rfl)
  have p46 : physical (.BaseLayerWitness 9) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  have p16 : physical (.BaseLayerMemory 7) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  have p20 : physical (.BaseLayerMemory 14) = logical 20 :=
    placed agreement (position := 20) (by kernel_rfl)
  have p34 : physical (.BaseLayerMemory 39) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  have p37 : physical (.BaseLayerWitness 0) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  have p38 : physical (.BaseLayerWitness 1) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  have p39 : physical (.BaseLayerWitness 2) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p40 : physical (.BaseLayerWitness 3) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p42 : physical (.BaseLayerWitness 5) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  have p48 : physical (.BaseLayerWitness 11) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  simp only [operand25, NativeLookups.Input.fields, sourceFields25, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p28, p46, p16, p20, p34, p37, p38, p39, p40, p42, p48]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields25 physical logical agreement]
  exact source_semantics25 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand26.input.fields physical = sourceFields26 logical := by
  have p55 : physical (.BaseLayerWitness 18) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  have p51 : physical (.BaseLayerWitness 14) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p57 : physical (.BaseLayerWitness 20) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  simp only [operand26, NativeLookups.Input.fields, sourceFields26, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p55, p51, p57]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields26 physical logical agreement]
  exact source_semantics26 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand27.input.fields physical = sourceFields27 logical := by
  have p56 : physical (.BaseLayerWitness 19) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p52 : physical (.BaseLayerWitness 15) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p58 : physical (.BaseLayerWitness 21) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
  simp only [operand27, NativeLookups.Input.fields, sourceFields27, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p56, p52, p58]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields27 physical logical agreement]
  exact source_semantics27 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand28.input.fields physical = sourceFields28 logical := by
  have p19 : physical (.BaseLayerMemory 13) = logical 19 :=
    placed agreement (position := 19) (by kernel_rfl)
  have p55 : physical (.BaseLayerWitness 18) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  have p56 : physical (.BaseLayerWitness 19) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p23 : physical (.BaseLayerMemory 20) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 10) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p48 : physical (.BaseLayerWitness 11) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p49 : physical (.BaseLayerWitness 12) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  have p51 : physical (.BaseLayerWitness 14) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p52 : physical (.BaseLayerWitness 15) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p59 : physical (.BaseLayerWitness 22) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  simp only [operand28, NativeLookups.Input.fields, sourceFields28, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p19, p55, p56, p23, p47, p48, p49, p51, p52, p59]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields28 physical logical agreement]
  exact source_semantics28 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand29.input.fields physical = sourceFields29 logical := by
  have p60 : physical (.BaseLayerWitness 23) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p53 : physical (.BaseLayerWitness 16) = logical 53 :=
    placed agreement (position := 53) (by kernel_rfl)
  have p62 : physical (.BaseLayerWitness 25) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  simp only [operand29, NativeLookups.Input.fields, sourceFields29, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p60, p53, p62]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields29 physical logical agreement]
  exact source_semantics29 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand30.input.fields physical = sourceFields30 logical := by
  have p61 : physical (.BaseLayerWitness 24) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  have p54 : physical (.BaseLayerWitness 17) = logical 54 :=
    placed agreement (position := 54) (by kernel_rfl)
  have p63 : physical (.BaseLayerWitness 26) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  simp only [operand30, NativeLookups.Input.fields, sourceFields30, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p61, p54, p63]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields30 physical logical agreement]
  exact source_semantics30 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand31.input.fields physical = sourceFields31 logical := by
  have p20 : physical (.BaseLayerMemory 14) = logical 20 :=
    placed agreement (position := 20) (by kernel_rfl)
  have p60 : physical (.BaseLayerWitness 23) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p61 : physical (.BaseLayerWitness 24) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  have p24 : physical (.BaseLayerMemory 21) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p44 : physical (.BaseLayerWitness 7) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  have p45 : physical (.BaseLayerWitness 8) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  have p49 : physical (.BaseLayerWitness 12) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  have p50 : physical (.BaseLayerWitness 13) = logical 50 :=
    placed agreement (position := 50) (by kernel_rfl)
  have p53 : physical (.BaseLayerWitness 16) = logical 53 :=
    placed agreement (position := 53) (by kernel_rfl)
  have p54 : physical (.BaseLayerWitness 17) = logical 54 :=
    placed agreement (position := 54) (by kernel_rfl)
  have p64 : physical (.BaseLayerWitness 27) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  simp only [operand31, NativeLookups.Input.fields, sourceFields31, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p20, p60, p61, p24, p44, p45, p49, p50, p53, p54, p64]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields31 physical logical agreement]
  exact source_semantics31 logical


end Airbender.Compiler.WorkerConstraints.BlakeG
