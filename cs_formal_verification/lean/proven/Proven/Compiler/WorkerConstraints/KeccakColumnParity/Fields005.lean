module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand40.input.fields physical = sourceFields40 logical := by
  have p55 : physical (.BaseLayerWitness 8) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  have p67 : physical (.BaseLayerWitness 20) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 32) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p91 : physical (.BaseLayerWitness 44) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p103 : physical (.BaseLayerWitness 56) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  have p115 : physical (.BaseLayerWitness 68) = logical 115 :=
    placed agreement (position := 115) (by kernel_rfl)
  simp only [operand40, NativeLookups.Input.fields, sourceFields40, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p55, p67, p79, p91, p103, p115]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup40).Contains (Verification.environment logical) ↔
      ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields40 physical logical agreement]
  exact source_semantics40 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand41.input.fields physical = sourceFields41 logical := by
  have p56 : physical (.BaseLayerWitness 9) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p68 : physical (.BaseLayerWitness 21) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 33) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p92 : physical (.BaseLayerWitness 45) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p104 : physical (.BaseLayerWitness 57) = logical 104 :=
    placed agreement (position := 104) (by kernel_rfl)
  have p116 : physical (.BaseLayerWitness 69) = logical 116 :=
    placed agreement (position := 116) (by kernel_rfl)
  simp only [operand41, NativeLookups.Input.fields, sourceFields41, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p56, p68, p80, p92, p104, p116]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup41).Contains (Verification.environment logical) ↔
      ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields41 physical logical agreement]
  exact source_semantics41 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand42.input.fields physical = sourceFields42 logical := by
  have p18 : physical (.BaseLayerMemory 16) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  have p54 : physical (.BaseLayerWitness 7) = logical 54 :=
    placed agreement (position := 54) (by kernel_rfl)
  have p55 : physical (.BaseLayerWitness 8) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  have p56 : physical (.BaseLayerWitness 9) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p24 : physical (.BaseLayerMemory 26) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p66 : physical (.BaseLayerWitness 19) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p67 : physical (.BaseLayerWitness 20) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p68 : physical (.BaseLayerWitness 21) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p28 : physical (.BaseLayerMemory 35) = logical 28 :=
    placed agreement (position := 28) (by kernel_rfl)
  have p78 : physical (.BaseLayerWitness 31) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 32) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 33) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p32 : physical (.BaseLayerMemory 44) = logical 32 :=
    placed agreement (position := 32) (by kernel_rfl)
  have p90 : physical (.BaseLayerWitness 43) = logical 90 :=
    placed agreement (position := 90) (by kernel_rfl)
  have p91 : physical (.BaseLayerWitness 44) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p92 : physical (.BaseLayerWitness 45) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p36 : physical (.BaseLayerMemory 53) = logical 36 :=
    placed agreement (position := 36) (by kernel_rfl)
  have p102 : physical (.BaseLayerWitness 55) = logical 102 :=
    placed agreement (position := 102) (by kernel_rfl)
  have p103 : physical (.BaseLayerWitness 56) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  have p104 : physical (.BaseLayerWitness 57) = logical 104 :=
    placed agreement (position := 104) (by kernel_rfl)
  have p42 : physical (.BaseLayerMemory 65) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  have p114 : physical (.BaseLayerWitness 67) = logical 114 :=
    placed agreement (position := 114) (by kernel_rfl)
  have p115 : physical (.BaseLayerWitness 68) = logical 115 :=
    placed agreement (position := 115) (by kernel_rfl)
  have p116 : physical (.BaseLayerWitness 69) = logical 116 :=
    placed agreement (position := 116) (by kernel_rfl)
  simp only [operand42, NativeLookups.Input.fields, sourceFields42, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p18, p54, p55, p56, p24, p66, p67, p68, p28, p78, p79, p80, p32, p90, p91, p92, p36, p102, p103, p104, p42, p114, p115, p116]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup42).Contains (Verification.environment logical) ↔
      ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields42 physical logical agreement]
  exact source_semantics42 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand43.input.fields physical = sourceFields43 logical := by
  have p57 : physical (.BaseLayerWitness 10) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  have p69 : physical (.BaseLayerWitness 22) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 34) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  have p93 : physical (.BaseLayerWitness 46) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  have p105 : physical (.BaseLayerWitness 58) = logical 105 :=
    placed agreement (position := 105) (by kernel_rfl)
  have p117 : physical (.BaseLayerWitness 70) = logical 117 :=
    placed agreement (position := 117) (by kernel_rfl)
  simp only [operand43, NativeLookups.Input.fields, sourceFields43, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p57, p69, p81, p93, p105, p117]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup43).Contains (Verification.environment logical) ↔
      ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields43 physical logical agreement]
  exact source_semantics43 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand44.input.fields physical = sourceFields44 logical := by
  have p58 : physical (.BaseLayerWitness 11) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
  have p70 : physical (.BaseLayerWitness 23) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 35) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  have p94 : physical (.BaseLayerWitness 47) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  have p106 : physical (.BaseLayerWitness 59) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  have p118 : physical (.BaseLayerWitness 71) = logical 118 :=
    placed agreement (position := 118) (by kernel_rfl)
  simp only [operand44, NativeLookups.Input.fields, sourceFields44, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p58, p70, p82, p94, p106, p118]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup44).Contains (Verification.environment logical) ↔
      ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields44 physical logical agreement]
  exact source_semantics44 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand45.input.fields physical = sourceFields45 logical := by
  have p59 : physical (.BaseLayerWitness 12) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p71 : physical (.BaseLayerWitness 24) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p83 : physical (.BaseLayerWitness 36) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p95 : physical (.BaseLayerWitness 48) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p107 : physical (.BaseLayerWitness 60) = logical 107 :=
    placed agreement (position := 107) (by kernel_rfl)
  have p119 : physical (.BaseLayerWitness 72) = logical 119 :=
    placed agreement (position := 119) (by kernel_rfl)
  simp only [operand45, NativeLookups.Input.fields, sourceFields45, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p59, p71, p83, p95, p107, p119]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup45).Contains (Verification.environment logical) ↔
      ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields45 physical logical agreement]
  exact source_semantics45 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand46.input.fields physical = sourceFields46 logical := by
  have p21 : physical (.BaseLayerMemory 21) = logical 21 :=
    placed agreement (position := 21) (by kernel_rfl)
  have p57 : physical (.BaseLayerWitness 10) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  have p58 : physical (.BaseLayerWitness 11) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
  have p59 : physical (.BaseLayerWitness 12) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p25 : physical (.BaseLayerMemory 30) = logical 25 :=
    placed agreement (position := 25) (by kernel_rfl)
  have p69 : physical (.BaseLayerWitness 22) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p70 : physical (.BaseLayerWitness 23) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p71 : physical (.BaseLayerWitness 24) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p29 : physical (.BaseLayerMemory 39) = logical 29 :=
    placed agreement (position := 29) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 34) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 35) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  have p83 : physical (.BaseLayerWitness 36) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p33 : physical (.BaseLayerMemory 48) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  have p93 : physical (.BaseLayerWitness 46) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  have p94 : physical (.BaseLayerWitness 47) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  have p95 : physical (.BaseLayerWitness 48) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p37 : physical (.BaseLayerMemory 57) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  have p105 : physical (.BaseLayerWitness 58) = logical 105 :=
    placed agreement (position := 105) (by kernel_rfl)
  have p106 : physical (.BaseLayerWitness 59) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  have p107 : physical (.BaseLayerWitness 60) = logical 107 :=
    placed agreement (position := 107) (by kernel_rfl)
  have p45 : physical (.BaseLayerMemory 70) = logical 45 :=
    placed agreement (position := 45) (by kernel_rfl)
  have p117 : physical (.BaseLayerWitness 70) = logical 117 :=
    placed agreement (position := 117) (by kernel_rfl)
  have p118 : physical (.BaseLayerWitness 71) = logical 118 :=
    placed agreement (position := 118) (by kernel_rfl)
  have p119 : physical (.BaseLayerWitness 72) = logical 119 :=
    placed agreement (position := 119) (by kernel_rfl)
  simp only [operand46, NativeLookups.Input.fields, sourceFields46, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p21, p57, p58, p59, p25, p69, p70, p71, p29, p81, p82, p83, p33, p93, p94, p95, p37, p105, p106, p107, p45, p117, p118, p119]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup46).Contains (Verification.environment logical) ↔
      ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields46 physical logical agreement]
  exact source_semantics46 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    operand47.input.fields physical = sourceFields47 logical := by
  have p60 : physical (.BaseLayerWitness 13) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p72 : physical (.BaseLayerWitness 25) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 37) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p96 : physical (.BaseLayerWitness 49) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p108 : physical (.BaseLayerWitness 61) = logical 108 :=
    placed agreement (position := 108) (by kernel_rfl)
  have p120 : physical (.BaseLayerWitness 73) = logical 120 :=
    placed agreement (position := 120) (by kernel_rfl)
  simp only [operand47, NativeLookups.Input.fields, sourceFields47, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p60, p72, p84, p96, p108, p120]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical) :
    (sourceLookup47).Contains (Verification.environment logical) ↔
      ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  rw [fields47 physical logical agreement]
  exact source_semantics47 logical


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
