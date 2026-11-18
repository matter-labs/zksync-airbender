module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries002
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand32.input.fields physical = sourceFields32 logical := by
  have p36 : physical (.BaseLayerMemory 33) = logical 36 :=
    placed agreement (position := 36) (by kernel_rfl)
  have p131 : physical (.BaseLayerWitness 67) = logical 131 :=
    placed agreement (position := 131) (by kernel_rfl)
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
  have p143 : physical (.BaseLayerWitness 79) = logical 143 :=
    placed agreement (position := 143) (by kernel_rfl)
  have p144 : physical (.BaseLayerWitness 80) = logical 144 :=
    placed agreement (position := 144) (by kernel_rfl)
  simp only [operand32, NativeLookups.Input.fields, sourceFields32, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p36, p131, p81, p84, p85, p86, p87, p88, p143, p144]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields32 physical logical agreement]
  exact source_semantics32 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand33.input.fields physical = sourceFields33 logical := by
  have p132 : physical (.BaseLayerWitness 68) = logical 132 :=
    placed agreement (position := 132) (by kernel_rfl)
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
  have p145 : physical (.BaseLayerWitness 81) = logical 145 :=
    placed agreement (position := 145) (by kernel_rfl)
  have p146 : physical (.BaseLayerWitness 82) = logical 146 :=
    placed agreement (position := 146) (by kernel_rfl)
  simp only [operand33, NativeLookups.Input.fields, sourceFields33, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p132, p82, p84, p85, p86, p87, p88, p145, p146]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields33 physical logical agreement]
  exact source_semantics33 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand34.input.fields physical = sourceFields34 logical := by
  have p37 : physical (.BaseLayerMemory 34) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  have p132 : physical (.BaseLayerWitness 68) = logical 132 :=
    placed agreement (position := 132) (by kernel_rfl)
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
  have p147 : physical (.BaseLayerWitness 83) = logical 147 :=
    placed agreement (position := 147) (by kernel_rfl)
  have p148 : physical (.BaseLayerWitness 84) = logical 148 :=
    placed agreement (position := 148) (by kernel_rfl)
  simp only [operand34, NativeLookups.Input.fields, sourceFields34, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p37, p132, p83, p84, p85, p86, p87, p88, p147, p148]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields34 physical logical agreement]
  exact source_semantics34 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand35.input.fields physical = sourceFields35 logical := by
  have p149 : physical (.BaseLayerWitness 85) = logical 149 :=
    placed agreement (position := 149) (by kernel_rfl)
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
  have p153 : physical (.BaseLayerWitness 89) = logical 153 :=
    placed agreement (position := 153) (by kernel_rfl)
  have p154 : physical (.BaseLayerWitness 90) = logical 154 :=
    placed agreement (position := 154) (by kernel_rfl)
  simp only [operand35, NativeLookups.Input.fields, sourceFields35, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p149, p76, p84, p85, p86, p87, p153, p154]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields35 physical logical agreement]
  exact source_semantics35 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand36.input.fields physical = sourceFields36 logical := by
  have p40 : physical (.BaseLayerMemory 37) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p149 : physical (.BaseLayerWitness 85) = logical 149 :=
    placed agreement (position := 149) (by kernel_rfl)
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
  have p155 : physical (.BaseLayerWitness 91) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  have p156 : physical (.BaseLayerWitness 92) = logical 156 :=
    placed agreement (position := 156) (by kernel_rfl)
  simp only [operand36, NativeLookups.Input.fields, sourceFields36, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p40, p149, p77, p84, p85, p86, p87, p155, p156]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields36 physical logical agreement]
  exact source_semantics36 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand37.input.fields physical = sourceFields37 logical := by
  have p150 : physical (.BaseLayerWitness 86) = logical 150 :=
    placed agreement (position := 150) (by kernel_rfl)
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
  have p157 : physical (.BaseLayerWitness 93) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p158 : physical (.BaseLayerWitness 94) = logical 158 :=
    placed agreement (position := 158) (by kernel_rfl)
  simp only [operand37, NativeLookups.Input.fields, sourceFields37, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p150, p78, p84, p85, p86, p87, p157, p158]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields37 physical logical agreement]
  exact source_semantics37 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand38.input.fields physical = sourceFields38 logical := by
  have p41 : physical (.BaseLayerMemory 38) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p150 : physical (.BaseLayerWitness 86) = logical 150 :=
    placed agreement (position := 150) (by kernel_rfl)
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
  have p159 : physical (.BaseLayerWitness 95) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p160 : physical (.BaseLayerWitness 96) = logical 160 :=
    placed agreement (position := 160) (by kernel_rfl)
  simp only [operand38, NativeLookups.Input.fields, sourceFields38, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p41, p150, p79, p84, p85, p86, p87, p159, p160]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields38 physical logical agreement]
  exact source_semantics38 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand39.input.fields physical = sourceFields39 logical := by
  have p151 : physical (.BaseLayerWitness 87) = logical 151 :=
    placed agreement (position := 151) (by kernel_rfl)
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
  have p161 : physical (.BaseLayerWitness 97) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  have p162 : physical (.BaseLayerWitness 98) = logical 162 :=
    placed agreement (position := 162) (by kernel_rfl)
  simp only [operand39, NativeLookups.Input.fields, sourceFields39, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p151, p80, p84, p85, p86, p87, p161, p162]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields39 physical logical agreement]
  exact source_semantics39 logical


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
