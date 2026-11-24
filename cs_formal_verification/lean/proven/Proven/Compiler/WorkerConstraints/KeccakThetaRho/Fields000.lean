module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries000

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p1 : physical (.BaseLayerMemory 70) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p0 : physical (.BaseLayerMemory 69) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  simp only [operand0, NativeLookups.Input.fields, sourceFields0]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p0]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup0).Contains (Verification.environment logical) ↔
      ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .thetaRho 2 index := by
  rw [fields0 physical logical agreement]
  exact source_semantics0 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p0 : physical (.BaseLayerMemory 69) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p3 : physical (.BaseLayerMemory 2) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p7 : physical (.BaseLayerMemory 12) = logical 7 :=
    placed agreement (position := 7) (by kernel_rfl)
  have p8 : physical (.BaseLayerMemory 21) = logical 8 :=
    placed agreement (position := 8) (by kernel_rfl)
  have p9 : physical (.BaseLayerMemory 30) = logical 9 :=
    placed agreement (position := 9) (by kernel_rfl)
  have p10 : physical (.BaseLayerMemory 39) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p11 : physical (.BaseLayerMemory 48) = logical 11 :=
    placed agreement (position := 11) (by kernel_rfl)
  have p12 : physical (.BaseLayerMemory 59) = logical 12 :=
    placed agreement (position := 12) (by kernel_rfl)
  have p13 : physical (.BaseLayerMemory 66) = logical 13 :=
    placed agreement (position := 13) (by kernel_rfl)
  simp only [operand1, NativeLookups.Input.fields, sourceFields1, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p0, p3, p7, p8, p9, p10, p11, p12, p13]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields1 physical logical agreement]
  exact source_semantics1 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p64 : physical (.BaseLayerWitness 0) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p72 : physical (.BaseLayerWitness 8) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 12) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  simp only [operand2, NativeLookups.Input.fields, sourceFields2, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p64, p72, p76]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields2 physical logical agreement]
  exact source_semantics2 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p56 : physical (.BaseLayerMemory 57) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p64 : physical (.BaseLayerWitness 0) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p60 : physical (.BaseLayerMemory 64) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p68 : physical (.BaseLayerWitness 4) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p71 : physical (.BaseLayerWitness 7) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p72 : physical (.BaseLayerWitness 8) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 13) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  simp only [operand3, NativeLookups.Input.fields, sourceFields3, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p56, p64, p60, p68, p71, p72, p77]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields3 physical logical agreement]
  exact source_semantics3 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p65 : physical (.BaseLayerWitness 1) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p73 : physical (.BaseLayerWitness 9) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 14) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  simp only [operand4, NativeLookups.Input.fields, sourceFields4, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p65, p73, p78]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields4 physical logical agreement]
  exact source_semantics4 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p57 : physical (.BaseLayerMemory 58) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  have p65 : physical (.BaseLayerWitness 1) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p61 : physical (.BaseLayerMemory 65) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  have p68 : physical (.BaseLayerWitness 4) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p69 : physical (.BaseLayerWitness 5) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p73 : physical (.BaseLayerWitness 9) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 15) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p57, p65, p61, p68, p69, p73, p79]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields5 physical logical agreement]
  exact source_semantics5 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p66 : physical (.BaseLayerWitness 2) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p74 : physical (.BaseLayerWitness 10) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 16) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p66, p74, p80]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields6 physical logical agreement]
  exact source_semantics6 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p58 : physical (.BaseLayerMemory 60) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
  have p66 : physical (.BaseLayerWitness 2) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p62 : physical (.BaseLayerMemory 67) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  have p69 : physical (.BaseLayerWitness 5) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p70 : physical (.BaseLayerWitness 6) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p74 : physical (.BaseLayerWitness 10) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 17) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p58, p66, p62, p69, p70, p74, p81]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields7 physical logical agreement]
  exact source_semantics7 logical


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
