module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries000
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p67 : physical (.BaseLayerWitness 3) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p75 : physical (.BaseLayerWitness 11) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 18) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  simp only [operand8, NativeLookups.Input.fields, sourceFields8, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p67, p75, p82]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields8 physical logical agreement]
  exact source_semantics8 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p59 : physical (.BaseLayerMemory 61) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p67 : physical (.BaseLayerWitness 3) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p63 : physical (.BaseLayerMemory 68) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p70 : physical (.BaseLayerWitness 6) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p71 : physical (.BaseLayerWitness 7) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p75 : physical (.BaseLayerWitness 11) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p83 : physical (.BaseLayerWitness 19) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  simp only [operand9, NativeLookups.Input.fields, sourceFields9, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p59, p67, p63, p70, p71, p75, p83]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields9 physical logical agreement]
  exact source_semantics9 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p3 : physical (.BaseLayerMemory 2) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p0 : physical (.BaseLayerMemory 69) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p5 : physical (.BaseLayerMemory 4) = logical 5 :=
    placed agreement (position := 5) (by kernel_rfl)
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
  simp only [operand10, NativeLookups.Input.fields, sourceFields10, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p0, p5, p84, p85, p86, p87, p88]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields10 physical logical agreement]
  exact source_semantics10 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p89 : physical (.BaseLayerWitness 25) = logical 89 :=
    placed agreement (position := 89) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 12) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p93 : physical (.BaseLayerWitness 29) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  have p94 : physical (.BaseLayerWitness 30) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  simp only [operand11, NativeLookups.Input.fields, sourceFields11, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p89, p76, p85, p86, p87, p88, p93, p94]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields11 physical logical agreement]
  exact source_semantics11 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p16 : physical (.BaseLayerMemory 10) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  have p89 : physical (.BaseLayerWitness 25) = logical 89 :=
    placed agreement (position := 89) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 13) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p95 : physical (.BaseLayerWitness 31) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p96 : physical (.BaseLayerWitness 32) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p16, p89, p77, p85, p86, p87, p88, p95, p96]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields12 physical logical agreement]
  exact source_semantics12 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p90 : physical (.BaseLayerWitness 26) = logical 90 :=
    placed agreement (position := 90) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 14) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p97 : physical (.BaseLayerWitness 33) = logical 97 :=
    placed agreement (position := 97) (by kernel_rfl)
  have p98 : physical (.BaseLayerWitness 34) = logical 98 :=
    placed agreement (position := 98) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p90, p78, p85, p86, p87, p88, p97, p98]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields13 physical logical agreement]
  exact source_semantics13 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p17 : physical (.BaseLayerMemory 11) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  have p90 : physical (.BaseLayerWitness 26) = logical 90 :=
    placed agreement (position := 90) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 15) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p99 : physical (.BaseLayerWitness 35) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p100 : physical (.BaseLayerWitness 36) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p17, p90, p79, p85, p86, p87, p88, p99, p100]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields14 physical logical agreement]
  exact source_semantics14 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p91 : physical (.BaseLayerWitness 27) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 16) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 21) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 22) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 23) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 24) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p101 : physical (.BaseLayerWitness 37) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  have p102 : physical (.BaseLayerWitness 38) = logical 102 :=
    placed agreement (position := 102) (by kernel_rfl)
  simp only [operand15, NativeLookups.Input.fields, sourceFields15, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p91, p80, p85, p86, p87, p88, p101, p102]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  rw [fields15 physical logical agreement]
  exact source_semantics15 logical


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
