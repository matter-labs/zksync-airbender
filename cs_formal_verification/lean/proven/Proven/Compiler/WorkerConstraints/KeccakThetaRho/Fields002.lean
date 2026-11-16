module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand16.input.fields physical = sourceFields16 logical := by
  have p20 : physical (.BaseLayerMemory 15) = logical 20 :=
    placed agreement (position := 20) (by kernel_rfl)
  have p91 : physical (.BaseLayerWitness 27) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 17) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p103 : physical (.BaseLayerWitness 39) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  have p104 : physical (.BaseLayerWitness 40) = logical 104 :=
    placed agreement (position := 104) (by kernel_rfl)
  simp only [operand16, NativeLookups.Input.fields, sourceFields16, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p20, p91, p81, p85, p86, p87, p88, p103, p104]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields16 physical logical agreement]
  exact source_semantics16 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand17.input.fields physical = sourceFields17 logical := by
  have p92 : physical (.BaseLayerWitness 28) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 18) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p105 : physical (.BaseLayerWitness 41) = logical 105 :=
    placed agreement (position := 105) (by kernel_rfl)
  have p106 : physical (.BaseLayerWitness 42) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  simp only [operand17, NativeLookups.Input.fields, sourceFields17, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p92, p82, p85, p86, p87, p88, p105, p106]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields17 physical logical agreement]
  exact source_semantics17 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand18.input.fields physical = sourceFields18 logical := by
  have p21 : physical (.BaseLayerMemory 16) = logical 21 :=
    placed agreement (position := 21) (by kernel_rfl)
  have p92 : physical (.BaseLayerWitness 28) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p83 : physical (.BaseLayerWitness 19) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p107 : physical (.BaseLayerWitness 43) = logical 107 :=
    placed agreement (position := 107) (by kernel_rfl)
  have p108 : physical (.BaseLayerWitness 44) = logical 108 :=
    placed agreement (position := 108) (by kernel_rfl)
  simp only [operand18, NativeLookups.Input.fields, sourceFields18, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p21, p92, p83, p85, p86, p87, p88, p107, p108]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields18 physical logical agreement]
  exact source_semantics18 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand19.input.fields physical = sourceFields19 logical := by
  have p109 : physical (.BaseLayerWitness 45) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 12) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p113 : physical (.BaseLayerWitness 49) = logical 113 :=
    placed agreement (position := 113) (by kernel_rfl)
  have p114 : physical (.BaseLayerWitness 50) = logical 114 :=
    placed agreement (position := 114) (by kernel_rfl)
  simp only [operand19, NativeLookups.Input.fields, sourceFields19, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p109, p76, p84, p85, p86, p87, p88, p113, p114]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup19).Contains (Verification.environment logical) ↔
      ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields19 physical logical agreement]
  exact source_semantics19 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand20.input.fields physical = sourceFields20 logical := by
  have p24 : physical (.BaseLayerMemory 19) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p109 : physical (.BaseLayerWitness 45) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 13) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p115 : physical (.BaseLayerWitness 51) = logical 115 :=
    placed agreement (position := 115) (by kernel_rfl)
  have p116 : physical (.BaseLayerWitness 52) = logical 116 :=
    placed agreement (position := 116) (by kernel_rfl)
  simp only [operand20, NativeLookups.Input.fields, sourceFields20, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p24, p109, p77, p84, p85, p86, p87, p88, p115, p116]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup20).Contains (Verification.environment logical) ↔
      ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields20 physical logical agreement]
  exact source_semantics20 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand21.input.fields physical = sourceFields21 logical := by
  have p110 : physical (.BaseLayerWitness 46) = logical 110 :=
    placed agreement (position := 110) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 14) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p117 : physical (.BaseLayerWitness 53) = logical 117 :=
    placed agreement (position := 117) (by kernel_rfl)
  have p118 : physical (.BaseLayerWitness 54) = logical 118 :=
    placed agreement (position := 118) (by kernel_rfl)
  simp only [operand21, NativeLookups.Input.fields, sourceFields21, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p110, p78, p84, p85, p86, p87, p88, p117, p118]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup21).Contains (Verification.environment logical) ↔
      ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields21 physical logical agreement]
  exact source_semantics21 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand22.input.fields physical = sourceFields22 logical := by
  have p25 : physical (.BaseLayerMemory 20) = logical 25 :=
    placed agreement (position := 25) (by kernel_rfl)
  have p110 : physical (.BaseLayerWitness 46) = logical 110 :=
    placed agreement (position := 110) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 15) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p119 : physical (.BaseLayerWitness 55) = logical 119 :=
    placed agreement (position := 119) (by kernel_rfl)
  have p120 : physical (.BaseLayerWitness 56) = logical 120 :=
    placed agreement (position := 120) (by kernel_rfl)
  simp only [operand22, NativeLookups.Input.fields, sourceFields22, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p25, p110, p79, p84, p85, p86, p87, p88, p119, p120]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup22).Contains (Verification.environment logical) ↔
      ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields22 physical logical agreement]
  exact source_semantics22 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand23.input.fields physical = sourceFields23 logical := by
  have p111 : physical (.BaseLayerWitness 47) = logical 111 :=
    placed agreement (position := 111) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 16) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p121 : physical (.BaseLayerWitness 57) = logical 121 :=
    placed agreement (position := 121) (by kernel_rfl)
  have p122 : physical (.BaseLayerWitness 58) = logical 122 :=
    placed agreement (position := 122) (by kernel_rfl)
  simp only [operand23, NativeLookups.Input.fields, sourceFields23, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p111, p80, p84, p85, p86, p87, p88, p121, p122]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup23).Contains (Verification.environment logical) ↔
      ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields23 physical logical agreement]
  exact source_semantics23 logical


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
