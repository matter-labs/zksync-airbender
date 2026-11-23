module
public import Proven.Compiler.WorkerConstraints.BlakeG.Queries002
public import Proven.Compiler.WorkerConstraints.BlakeG.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand32.input.fields physical = sourceFields32 logical := by
  have p47 : physical (.BaseLayerWitness 10) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p69 : physical (.BaseLayerWitness 32) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p71 : physical (.BaseLayerWitness 34) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  simp only [operand32, NativeLookups.Input.fields, sourceFields32, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p47, p69, p71]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields32 physical logical agreement]
  exact source_semantics32 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand33.input.fields physical = sourceFields33 logical := by
  have p48 : physical (.BaseLayerWitness 11) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p15 : physical (.BaseLayerMemory 6) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  have p19 : physical (.BaseLayerMemory 13) = logical 19 :=
    placed agreement (position := 19) (by kernel_rfl)
  have p33 : physical (.BaseLayerMemory 38) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  have p35 : physical (.BaseLayerMemory 43) = logical 35 :=
    placed agreement (position := 35) (by kernel_rfl)
  have p37 : physical (.BaseLayerWitness 0) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  have p38 : physical (.BaseLayerWitness 1) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  have p59 : physical (.BaseLayerWitness 22) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p62 : physical (.BaseLayerWitness 25) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  have p63 : physical (.BaseLayerWitness 26) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p65 : physical (.BaseLayerWitness 28) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p66 : physical (.BaseLayerWitness 29) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p69 : physical (.BaseLayerWitness 32) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p72 : physical (.BaseLayerWitness 35) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  simp only [operand33, NativeLookups.Input.fields, sourceFields33, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p48, p15, p19, p33, p35, p37, p38, p59, p62, p63, p65, p66, p69, p72]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields33 physical logical agreement]
  exact source_semantics33 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand34.input.fields physical = sourceFields34 logical := by
  have p44 : physical (.BaseLayerWitness 7) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  have p70 : physical (.BaseLayerWitness 33) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p73 : physical (.BaseLayerWitness 36) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  simp only [operand34, NativeLookups.Input.fields, sourceFields34, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p44, p70, p73]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields34 physical logical agreement]
  exact source_semantics34 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand35.input.fields physical = sourceFields35 logical := by
  have p45 : physical (.BaseLayerWitness 8) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  have p16 : physical (.BaseLayerMemory 7) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  have p20 : physical (.BaseLayerMemory 14) = logical 20 :=
    placed agreement (position := 20) (by kernel_rfl)
  have p34 : physical (.BaseLayerMemory 39) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  have p36 : physical (.BaseLayerMemory 44) = logical 36 :=
    placed agreement (position := 36) (by kernel_rfl)
  have p37 : physical (.BaseLayerWitness 0) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  have p38 : physical (.BaseLayerWitness 1) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  have p39 : physical (.BaseLayerWitness 2) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p40 : physical (.BaseLayerWitness 3) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p57 : physical (.BaseLayerWitness 20) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  have p58 : physical (.BaseLayerWitness 21) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
  have p64 : physical (.BaseLayerWitness 27) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p65 : physical (.BaseLayerWitness 28) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p66 : physical (.BaseLayerWitness 29) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p67 : physical (.BaseLayerWitness 30) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p68 : physical (.BaseLayerWitness 31) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p70 : physical (.BaseLayerWitness 33) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p74 : physical (.BaseLayerWitness 37) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  simp only [operand35, NativeLookups.Input.fields, sourceFields35, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p45, p16, p20, p34, p36, p37, p38, p39, p40, p57, p58, p64, p65, p66, p67, p68, p70, p74]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields35 physical logical agreement]
  exact source_semantics35 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand36.input.fields physical = sourceFields36 logical := by
  have p59 : physical (.BaseLayerWitness 22) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p62 : physical (.BaseLayerWitness 25) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 40) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 42) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  simp only [operand36, NativeLookups.Input.fields, sourceFields36, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p59, p62, p77, p79]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields36 physical logical agreement]
  exact source_semantics36 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand37.input.fields physical = sourceFields37 logical := by
  have p63 : physical (.BaseLayerWitness 26) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p23 : physical (.BaseLayerMemory 20) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p47 : physical (.BaseLayerWitness 10) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p48 : physical (.BaseLayerWitness 11) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p49 : physical (.BaseLayerWitness 12) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  have p72 : physical (.BaseLayerWitness 35) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p73 : physical (.BaseLayerWitness 36) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  have p75 : physical (.BaseLayerWitness 38) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 40) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 43) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  simp only [operand37, NativeLookups.Input.fields, sourceFields37, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p63, p23, p47, p48, p49, p72, p73, p75, p77, p80]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields37 physical logical agreement]
  exact source_semantics37 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand38.input.fields physical = sourceFields38 logical := by
  have p57 : physical (.BaseLayerWitness 20) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  have p64 : physical (.BaseLayerWitness 27) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 41) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 44) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  simp only [operand38, NativeLookups.Input.fields, sourceFields38, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p57, p64, p78, p81]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields38 physical logical agreement]
  exact source_semantics38 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    operand39.input.fields physical = sourceFields39 logical := by
  have p58 : physical (.BaseLayerWitness 21) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
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
  have p71 : physical (.BaseLayerWitness 34) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p74 : physical (.BaseLayerWitness 37) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  have p75 : physical (.BaseLayerWitness 38) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 39) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 41) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 45) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  simp only [operand39, NativeLookups.Input.fields, sourceFields39, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p58, p24, p44, p45, p49, p50, p71, p74, p75, p76, p78, p82]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  rw [fields39 physical logical agreement]
  exact source_semantics39 logical


end Airbender.Compiler.WorkerConstraints.BlakeG
