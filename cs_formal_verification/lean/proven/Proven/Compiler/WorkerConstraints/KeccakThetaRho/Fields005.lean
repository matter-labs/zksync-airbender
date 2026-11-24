module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand40.input.fields physical = sourceFields40 logical := by
  have p44 : physical (.BaseLayerMemory 42) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  have p151 : physical (.BaseLayerWitness 87) = logical 151 :=
    placed agreement (position := 151) (by kernel_rfl)
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
  have p163 : physical (.BaseLayerWitness 99) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  have p164 : physical (.BaseLayerWitness 100) = logical 164 :=
    placed agreement (position := 164) (by kernel_rfl)
  simp only [operand40, NativeLookups.Input.fields, sourceFields40, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p44, p151, p81, p84, p85, p86, p87, p163, p164]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup40).Contains (Verification.environment logical) ↔
      ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields40 physical logical agreement]
  exact source_semantics40 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand41.input.fields physical = sourceFields41 logical := by
  have p152 : physical (.BaseLayerWitness 88) = logical 152 :=
    placed agreement (position := 152) (by kernel_rfl)
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
  have p165 : physical (.BaseLayerWitness 101) = logical 165 :=
    placed agreement (position := 165) (by kernel_rfl)
  have p166 : physical (.BaseLayerWitness 102) = logical 166 :=
    placed agreement (position := 166) (by kernel_rfl)
  simp only [operand41, NativeLookups.Input.fields, sourceFields41, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p152, p82, p84, p85, p86, p87, p165, p166]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup41).Contains (Verification.environment logical) ↔
      ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields41 physical logical agreement]
  exact source_semantics41 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand42.input.fields physical = sourceFields42 logical := by
  have p45 : physical (.BaseLayerMemory 43) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  have p152 : physical (.BaseLayerWitness 88) = logical 152 :=
    placed agreement (position := 152) (by kernel_rfl)
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
  have p167 : physical (.BaseLayerWitness 103) = logical 167 :=
    placed agreement (position := 167) (by kernel_rfl)
  have p168 : physical (.BaseLayerWitness 104) = logical 168 :=
    placed agreement (position := 168) (by kernel_rfl)
  simp only [operand42, NativeLookups.Input.fields, sourceFields42, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p45, p152, p83, p84, p85, p86, p87, p167, p168]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup42).Contains (Verification.environment logical) ↔
      ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields42 physical logical agreement]
  exact source_semantics42 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand43.input.fields physical = sourceFields43 logical := by
  have p169 : physical (.BaseLayerWitness 105) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 12) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p173 : physical (.BaseLayerWitness 109) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  have p174 : physical (.BaseLayerWitness 110) = logical 174 :=
    placed agreement (position := 174) (by kernel_rfl)
  simp only [operand43, NativeLookups.Input.fields, sourceFields43, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p169, p76, p84, p85, p86, p88, p173, p174]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup43).Contains (Verification.environment logical) ↔
      ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields43 physical logical agreement]
  exact source_semantics43 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand44.input.fields physical = sourceFields44 logical := by
  have p48 : physical (.BaseLayerMemory 46) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p169 : physical (.BaseLayerWitness 105) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 13) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p175 : physical (.BaseLayerWitness 111) = logical 175 :=
    placed agreement (position := 175) (by kernel_rfl)
  have p176 : physical (.BaseLayerWitness 112) = logical 176 :=
    placed agreement (position := 176) (by kernel_rfl)
  simp only [operand44, NativeLookups.Input.fields, sourceFields44, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p48, p169, p77, p84, p85, p86, p88, p175, p176]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup44).Contains (Verification.environment logical) ↔
      ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields44 physical logical agreement]
  exact source_semantics44 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand45.input.fields physical = sourceFields45 logical := by
  have p170 : physical (.BaseLayerWitness 106) = logical 170 :=
    placed agreement (position := 170) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 14) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p177 : physical (.BaseLayerWitness 113) = logical 177 :=
    placed agreement (position := 177) (by kernel_rfl)
  have p178 : physical (.BaseLayerWitness 114) = logical 178 :=
    placed agreement (position := 178) (by kernel_rfl)
  simp only [operand45, NativeLookups.Input.fields, sourceFields45, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p170, p78, p84, p85, p86, p88, p177, p178]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup45).Contains (Verification.environment logical) ↔
      ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields45 physical logical agreement]
  exact source_semantics45 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand46.input.fields physical = sourceFields46 logical := by
  have p49 : physical (.BaseLayerMemory 47) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  have p170 : physical (.BaseLayerWitness 106) = logical 170 :=
    placed agreement (position := 170) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 15) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p179 : physical (.BaseLayerWitness 115) = logical 179 :=
    placed agreement (position := 179) (by kernel_rfl)
  have p180 : physical (.BaseLayerWitness 116) = logical 180 :=
    placed agreement (position := 180) (by kernel_rfl)
  simp only [operand46, NativeLookups.Input.fields, sourceFields46, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p49, p170, p79, p84, p85, p86, p88, p179, p180]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup46).Contains (Verification.environment logical) ↔
      ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields46 physical logical agreement]
  exact source_semantics46 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand47.input.fields physical = sourceFields47 logical := by
  have p171 : physical (.BaseLayerWitness 107) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 16) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 20) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p181 : physical (.BaseLayerWitness 117) = logical 181 :=
    placed agreement (position := 181) (by kernel_rfl)
  have p182 : physical (.BaseLayerWitness 118) = logical 182 :=
    placed agreement (position := 182) (by kernel_rfl)
  simp only [operand47, NativeLookups.Input.fields, sourceFields47, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p171, p80, p84, p85, p86, p88, p181, p182]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup47).Contains (Verification.environment logical) ↔
      ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields47 physical logical agreement]
  exact source_semantics47 logical


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
