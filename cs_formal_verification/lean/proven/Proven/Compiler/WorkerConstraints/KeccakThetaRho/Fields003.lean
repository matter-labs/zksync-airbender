module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand24.input.fields physical = sourceFields24 logical := by
  have p28 : physical (.BaseLayerMemory 24) = logical 28 :=
    placed agreement (position := 28) (by kernel_rfl)
  have p111 : physical (.BaseLayerWitness 47) = logical 111 :=
    placed agreement (position := 111) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 17) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
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
  have p123 : physical (.BaseLayerWitness 59) = logical 123 :=
    placed agreement (position := 123) (by kernel_rfl)
  have p124 : physical (.BaseLayerWitness 60) = logical 124 :=
    placed agreement (position := 124) (by kernel_rfl)
  simp only [operand24, NativeLookups.Input.fields, sourceFields24, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p28, p111, p81, p84, p85, p86, p87, p88, p123, p124]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields24 physical logical agreement]
  exact source_semantics24 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand25.input.fields physical = sourceFields25 logical := by
  have p112 : physical (.BaseLayerWitness 48) = logical 112 :=
    placed agreement (position := 112) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 18) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
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
  have p125 : physical (.BaseLayerWitness 61) = logical 125 :=
    placed agreement (position := 125) (by kernel_rfl)
  have p126 : physical (.BaseLayerWitness 62) = logical 126 :=
    placed agreement (position := 126) (by kernel_rfl)
  simp only [operand25, NativeLookups.Input.fields, sourceFields25, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p112, p82, p84, p85, p86, p87, p88, p125, p126]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields25 physical logical agreement]
  exact source_semantics25 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand26.input.fields physical = sourceFields26 logical := by
  have p29 : physical (.BaseLayerMemory 25) = logical 29 :=
    placed agreement (position := 29) (by kernel_rfl)
  have p112 : physical (.BaseLayerWitness 48) = logical 112 :=
    placed agreement (position := 112) (by kernel_rfl)
  have p83 : physical (.BaseLayerWitness 19) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
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
  have p127 : physical (.BaseLayerWitness 63) = logical 127 :=
    placed agreement (position := 127) (by kernel_rfl)
  have p128 : physical (.BaseLayerWitness 64) = logical 128 :=
    placed agreement (position := 128) (by kernel_rfl)
  simp only [operand26, NativeLookups.Input.fields, sourceFields26, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p29, p112, p83, p84, p85, p86, p87, p88, p127, p128]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields26 physical logical agreement]
  exact source_semantics26 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand27.input.fields physical = sourceFields27 logical := by
  have p129 : physical (.BaseLayerWitness 65) = logical 129 :=
    placed agreement (position := 129) (by kernel_rfl)
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
  have p133 : physical (.BaseLayerWitness 69) = logical 133 :=
    placed agreement (position := 133) (by kernel_rfl)
  have p134 : physical (.BaseLayerWitness 70) = logical 134 :=
    placed agreement (position := 134) (by kernel_rfl)
  simp only [operand27, NativeLookups.Input.fields, sourceFields27, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p129, p76, p84, p85, p86, p87, p88, p133, p134]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields27 physical logical agreement]
  exact source_semantics27 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand28.input.fields physical = sourceFields28 logical := by
  have p32 : physical (.BaseLayerMemory 28) = logical 32 :=
    placed agreement (position := 32) (by kernel_rfl)
  have p129 : physical (.BaseLayerWitness 65) = logical 129 :=
    placed agreement (position := 129) (by kernel_rfl)
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
  have p135 : physical (.BaseLayerWitness 71) = logical 135 :=
    placed agreement (position := 135) (by kernel_rfl)
  have p136 : physical (.BaseLayerWitness 72) = logical 136 :=
    placed agreement (position := 136) (by kernel_rfl)
  simp only [operand28, NativeLookups.Input.fields, sourceFields28, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p32, p129, p77, p84, p85, p86, p87, p88, p135, p136]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields28 physical logical agreement]
  exact source_semantics28 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand29.input.fields physical = sourceFields29 logical := by
  have p130 : physical (.BaseLayerWitness 66) = logical 130 :=
    placed agreement (position := 130) (by kernel_rfl)
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
  have p137 : physical (.BaseLayerWitness 73) = logical 137 :=
    placed agreement (position := 137) (by kernel_rfl)
  have p138 : physical (.BaseLayerWitness 74) = logical 138 :=
    placed agreement (position := 138) (by kernel_rfl)
  simp only [operand29, NativeLookups.Input.fields, sourceFields29, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p130, p78, p84, p85, p86, p87, p88, p137, p138]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields29 physical logical agreement]
  exact source_semantics29 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand30.input.fields physical = sourceFields30 logical := by
  have p33 : physical (.BaseLayerMemory 29) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  have p130 : physical (.BaseLayerWitness 66) = logical 130 :=
    placed agreement (position := 130) (by kernel_rfl)
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
  have p139 : physical (.BaseLayerWitness 75) = logical 139 :=
    placed agreement (position := 139) (by kernel_rfl)
  have p140 : physical (.BaseLayerWitness 76) = logical 140 :=
    placed agreement (position := 140) (by kernel_rfl)
  simp only [operand30, NativeLookups.Input.fields, sourceFields30, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p33, p130, p79, p84, p85, p86, p87, p88, p139, p140]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields30 physical logical agreement]
  exact source_semantics30 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand31.input.fields physical = sourceFields31 logical := by
  have p131 : physical (.BaseLayerWitness 67) = logical 131 :=
    placed agreement (position := 131) (by kernel_rfl)
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
  have p141 : physical (.BaseLayerWitness 77) = logical 141 :=
    placed agreement (position := 141) (by kernel_rfl)
  have p142 : physical (.BaseLayerWitness 78) = logical 142 :=
    placed agreement (position := 142) (by kernel_rfl)
  simp only [operand31, NativeLookups.Input.fields, sourceFields31, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p131, p80, p84, p85, p86, p87, p88, p141, p142]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields31 physical logical agreement]
  exact source_semantics31 logical


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
