module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries002
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand32.input.fields physical = sourceFields32 logical := by
  have p15 : physical (.BaseLayerMemory 12) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  have p48 : physical (.BaseLayerWitness 1) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 0) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p17 : physical (.BaseLayerMemory 15) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  have p51 : physical (.BaseLayerWitness 4) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p52 : physical (.BaseLayerWitness 5) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  simp only [operand32, NativeLookups.Input.fields, sourceFields32, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p15, p48, p47, p17, p51, p52]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields32 physical logical agreement]
  exact source_semantics32 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand33.input.fields physical = sourceFields33 logical := by
  have p16 : physical (.BaseLayerMemory 13) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  have p49 : physical (.BaseLayerWitness 2) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 0) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p18 : physical (.BaseLayerMemory 16) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  have p54 : physical (.BaseLayerWitness 7) = logical 54 :=
    placed agreement (position := 54) (by kernel_rfl)
  have p55 : physical (.BaseLayerWitness 8) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  simp only [operand33, NativeLookups.Input.fields, sourceFields33, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p16, p49, p47, p18, p54, p55]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields33 physical logical agreement]
  exact source_semantics33 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand34.input.fields physical = sourceFields34 logical := by
  have p20 : physical (.BaseLayerMemory 20) = logical 20 :=
    placed agreement (position := 20) (by kernel_rfl)
  have p50 : physical (.BaseLayerWitness 3) = logical 50 :=
    placed agreement (position := 50) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 0) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p22 : physical (.BaseLayerMemory 22) = logical 22 :=
    placed agreement (position := 22) (by kernel_rfl)
  have p60 : physical (.BaseLayerWitness 13) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p61 : physical (.BaseLayerWitness 14) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  simp only [operand34, NativeLookups.Input.fields, sourceFields34, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p20, p50, p47, p22, p60, p61]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields34 physical logical agreement]
  exact source_semantics34 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand35.input.fields physical = sourceFields35 logical := by
  have p51 : physical (.BaseLayerWitness 4) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p63 : physical (.BaseLayerWitness 16) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p75 : physical (.BaseLayerWitness 28) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 40) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p99 : physical (.BaseLayerWitness 52) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p111 : physical (.BaseLayerWitness 64) = logical 111 :=
    placed agreement (position := 111) (by kernel_rfl)
  simp only [operand35, NativeLookups.Input.fields, sourceFields35, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p51, p63, p75, p87, p99, p111]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields35 physical logical agreement]
  exact source_semantics35 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand36.input.fields physical = sourceFields36 logical := by
  have p52 : physical (.BaseLayerWitness 5) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p64 : physical (.BaseLayerWitness 17) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 29) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 41) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p100 : physical (.BaseLayerWitness 53) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  have p112 : physical (.BaseLayerWitness 65) = logical 112 :=
    placed agreement (position := 112) (by kernel_rfl)
  simp only [operand36, NativeLookups.Input.fields, sourceFields36, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p52, p64, p76, p88, p100, p112]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields36 physical logical agreement]
  exact source_semantics36 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand37.input.fields physical = sourceFields37 logical := by
  have p53 : physical (.BaseLayerWitness 6) = logical 53 :=
    placed agreement (position := 53) (by kernel_rfl)
  have p65 : physical (.BaseLayerWitness 18) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 30) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p89 : physical (.BaseLayerWitness 42) = logical 89 :=
    placed agreement (position := 89) (by kernel_rfl)
  have p101 : physical (.BaseLayerWitness 54) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  have p113 : physical (.BaseLayerWitness 66) = logical 113 :=
    placed agreement (position := 113) (by kernel_rfl)
  simp only [operand37, NativeLookups.Input.fields, sourceFields37, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p53, p65, p77, p89, p101, p113]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields37 physical logical agreement]
  exact source_semantics37 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand38.input.fields physical = sourceFields38 logical := by
  have p17 : physical (.BaseLayerMemory 15) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  have p51 : physical (.BaseLayerWitness 4) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  have p52 : physical (.BaseLayerWitness 5) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p53 : physical (.BaseLayerWitness 6) = logical 53 :=
    placed agreement (position := 53) (by kernel_rfl)
  have p23 : physical (.BaseLayerMemory 25) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p63 : physical (.BaseLayerWitness 16) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p64 : physical (.BaseLayerWitness 17) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p65 : physical (.BaseLayerWitness 18) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p27 : physical (.BaseLayerMemory 34) = logical 27 :=
    placed agreement (position := 27) (by kernel_rfl)
  have p75 : physical (.BaseLayerWitness 28) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 29) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 30) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p31 : physical (.BaseLayerMemory 43) = logical 31 :=
    placed agreement (position := 31) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 40) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 41) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p89 : physical (.BaseLayerWitness 42) = logical 89 :=
    placed agreement (position := 89) (by kernel_rfl)
  have p35 : physical (.BaseLayerMemory 52) = logical 35 :=
    placed agreement (position := 35) (by kernel_rfl)
  have p99 : physical (.BaseLayerWitness 52) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p100 : physical (.BaseLayerWitness 53) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  have p101 : physical (.BaseLayerWitness 54) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  have p41 : physical (.BaseLayerMemory 64) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p111 : physical (.BaseLayerWitness 64) = logical 111 :=
    placed agreement (position := 111) (by kernel_rfl)
  have p112 : physical (.BaseLayerWitness 65) = logical 112 :=
    placed agreement (position := 112) (by kernel_rfl)
  have p113 : physical (.BaseLayerWitness 66) = logical 113 :=
    placed agreement (position := 113) (by kernel_rfl)
  simp only [operand38, NativeLookups.Input.fields, sourceFields38, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p17, p51, p52, p53, p23, p63, p64, p65, p27, p75, p76, p77, p31, p87, p88, p89, p35, p99, p100, p101, p41, p111, p112, p113]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields38 physical logical agreement]
  exact source_semantics38 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand39.input.fields physical = sourceFields39 logical := by
  have p54 : physical (.BaseLayerWitness 7) = logical 54 :=
    placed agreement (position := 54) (by kernel_rfl)
  have p66 : physical (.BaseLayerWitness 19) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 31) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p90 : physical (.BaseLayerWitness 43) = logical 90 :=
    placed agreement (position := 90) (by kernel_rfl)
  have p102 : physical (.BaseLayerWitness 55) = logical 102 :=
    placed agreement (position := 102) (by kernel_rfl)
  have p114 : physical (.BaseLayerWitness 67) = logical 114 :=
    placed agreement (position := 114) (by kernel_rfl)
  simp only [operand39, NativeLookups.Input.fields, sourceFields39, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p54, p66, p78, p90, p102, p114]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields39 physical logical agreement]
  exact source_semantics39 logical


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
