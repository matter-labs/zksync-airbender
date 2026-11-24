module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Queries000

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p1 : physical (.BaseLayerMemory 64) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p0 : physical (.BaseLayerMemory 63) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  simp only [operand0, NativeLookups.Input.fields, sourceFields0]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p1, p0]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup0).Contains (Verification.environment logical) ↔
      ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .chi5 2 index := by
  rw [fields0 physical logical agreement]
  exact source_semantics0 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p3 : physical (.BaseLayerMemory 2) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p0 : physical (.BaseLayerMemory 63) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p5 : physical (.BaseLayerMemory 4) = logical 5 :=
    placed agreement (position := 5) (by kernel_rfl)
  have p7 : physical (.BaseLayerMemory 12) = logical 7 :=
    placed agreement (position := 7) (by kernel_rfl)
  have p8 : physical (.BaseLayerMemory 23) = logical 8 :=
    placed agreement (position := 8) (by kernel_rfl)
  have p9 : physical (.BaseLayerMemory 34) = logical 9 :=
    placed agreement (position := 9) (by kernel_rfl)
  have p10 : physical (.BaseLayerMemory 45) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p11 : physical (.BaseLayerMemory 56) = logical 11 :=
    placed agreement (position := 11) (by kernel_rfl)
  have p54 : physical (.BaseLayerWitness 0) = logical 54 :=
    placed agreement (position := 54) (by kernel_rfl)
  simp only [operand1, NativeLookups.Input.fields, sourceFields1, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p0, p5, p7, p8, p9, p10, p11, p54]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields1 physical logical agreement]
  exact source_semantics1 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p55 : physical (.BaseLayerWitness 1) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  have p67 : physical (.BaseLayerWitness 13) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 25) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p91 : physical (.BaseLayerWitness 37) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p103 : physical (.BaseLayerWitness 49) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  have p115 : physical (.BaseLayerWitness 61) = logical 115 :=
    placed agreement (position := 115) (by kernel_rfl)
  have p127 : physical (.BaseLayerWitness 73) = logical 127 :=
    placed agreement (position := 127) (by kernel_rfl)
  have p139 : physical (.BaseLayerWitness 85) = logical 139 :=
    placed agreement (position := 139) (by kernel_rfl)
  have p151 : physical (.BaseLayerWitness 97) = logical 151 :=
    placed agreement (position := 151) (by kernel_rfl)
  have p163 : physical (.BaseLayerWitness 109) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  simp only [operand2, NativeLookups.Input.fields, sourceFields2, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p55, p67, p79, p91, p103, p115, p127, p139, p151, p163]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields2 physical logical agreement]
  exact source_semantics2 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p56 : physical (.BaseLayerWitness 2) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p68 : physical (.BaseLayerWitness 14) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 26) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p92 : physical (.BaseLayerWitness 38) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p104 : physical (.BaseLayerWitness 50) = logical 104 :=
    placed agreement (position := 104) (by kernel_rfl)
  have p116 : physical (.BaseLayerWitness 62) = logical 116 :=
    placed agreement (position := 116) (by kernel_rfl)
  have p128 : physical (.BaseLayerWitness 74) = logical 128 :=
    placed agreement (position := 128) (by kernel_rfl)
  have p140 : physical (.BaseLayerWitness 86) = logical 140 :=
    placed agreement (position := 140) (by kernel_rfl)
  have p152 : physical (.BaseLayerWitness 98) = logical 152 :=
    placed agreement (position := 152) (by kernel_rfl)
  have p164 : physical (.BaseLayerWitness 110) = logical 164 :=
    placed agreement (position := 164) (by kernel_rfl)
  simp only [operand3, NativeLookups.Input.fields, sourceFields3, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p56, p68, p80, p92, p104, p116, p128, p140, p152, p164]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields3 physical logical agreement]
  exact source_semantics3 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p57 : physical (.BaseLayerWitness 3) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  have p69 : physical (.BaseLayerWitness 15) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 27) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  have p93 : physical (.BaseLayerWitness 39) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  have p105 : physical (.BaseLayerWitness 51) = logical 105 :=
    placed agreement (position := 105) (by kernel_rfl)
  have p117 : physical (.BaseLayerWitness 63) = logical 117 :=
    placed agreement (position := 117) (by kernel_rfl)
  have p129 : physical (.BaseLayerWitness 75) = logical 129 :=
    placed agreement (position := 129) (by kernel_rfl)
  have p141 : physical (.BaseLayerWitness 87) = logical 141 :=
    placed agreement (position := 141) (by kernel_rfl)
  have p153 : physical (.BaseLayerWitness 99) = logical 153 :=
    placed agreement (position := 153) (by kernel_rfl)
  have p165 : physical (.BaseLayerWitness 111) = logical 165 :=
    placed agreement (position := 165) (by kernel_rfl)
  simp only [operand4, NativeLookups.Input.fields, sourceFields4, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p57, p69, p81, p93, p105, p117, p129, p141, p153, p165]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields4 physical logical agreement]
  exact source_semantics4 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p14 : physical (.BaseLayerMemory 10) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  have p55 : physical (.BaseLayerWitness 1) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  have p56 : physical (.BaseLayerWitness 2) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p57 : physical (.BaseLayerWitness 3) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  have p22 : physical (.BaseLayerMemory 21) = logical 22 :=
    placed agreement (position := 22) (by kernel_rfl)
  have p67 : physical (.BaseLayerWitness 13) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p68 : physical (.BaseLayerWitness 14) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p69 : physical (.BaseLayerWitness 15) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p30 : physical (.BaseLayerMemory 32) = logical 30 :=
    placed agreement (position := 30) (by kernel_rfl)
  have p79 : physical (.BaseLayerWitness 25) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p80 : physical (.BaseLayerWitness 26) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p81 : physical (.BaseLayerWitness 27) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  have p38 : physical (.BaseLayerMemory 43) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  have p91 : physical (.BaseLayerWitness 37) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  have p92 : physical (.BaseLayerWitness 38) = logical 92 :=
    placed agreement (position := 92) (by kernel_rfl)
  have p93 : physical (.BaseLayerWitness 39) = logical 93 :=
    placed agreement (position := 93) (by kernel_rfl)
  have p46 : physical (.BaseLayerMemory 54) = logical 46 :=
    placed agreement (position := 46) (by kernel_rfl)
  have p103 : physical (.BaseLayerWitness 49) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  have p104 : physical (.BaseLayerWitness 50) = logical 104 :=
    placed agreement (position := 104) (by kernel_rfl)
  have p105 : physical (.BaseLayerWitness 51) = logical 105 :=
    placed agreement (position := 105) (by kernel_rfl)
  have p16 : physical (.BaseLayerMemory 13) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  have p115 : physical (.BaseLayerWitness 61) = logical 115 :=
    placed agreement (position := 115) (by kernel_rfl)
  have p116 : physical (.BaseLayerWitness 62) = logical 116 :=
    placed agreement (position := 116) (by kernel_rfl)
  have p117 : physical (.BaseLayerWitness 63) = logical 117 :=
    placed agreement (position := 117) (by kernel_rfl)
  have p24 : physical (.BaseLayerMemory 24) = logical 24 :=
    placed agreement (position := 24) (by kernel_rfl)
  have p127 : physical (.BaseLayerWitness 73) = logical 127 :=
    placed agreement (position := 127) (by kernel_rfl)
  have p128 : physical (.BaseLayerWitness 74) = logical 128 :=
    placed agreement (position := 128) (by kernel_rfl)
  have p129 : physical (.BaseLayerWitness 75) = logical 129 :=
    placed agreement (position := 129) (by kernel_rfl)
  have p32 : physical (.BaseLayerMemory 35) = logical 32 :=
    placed agreement (position := 32) (by kernel_rfl)
  have p139 : physical (.BaseLayerWitness 85) = logical 139 :=
    placed agreement (position := 139) (by kernel_rfl)
  have p140 : physical (.BaseLayerWitness 86) = logical 140 :=
    placed agreement (position := 140) (by kernel_rfl)
  have p141 : physical (.BaseLayerWitness 87) = logical 141 :=
    placed agreement (position := 141) (by kernel_rfl)
  have p40 : physical (.BaseLayerMemory 46) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  have p151 : physical (.BaseLayerWitness 97) = logical 151 :=
    placed agreement (position := 151) (by kernel_rfl)
  have p152 : physical (.BaseLayerWitness 98) = logical 152 :=
    placed agreement (position := 152) (by kernel_rfl)
  have p153 : physical (.BaseLayerWitness 99) = logical 153 :=
    placed agreement (position := 153) (by kernel_rfl)
  have p48 : physical (.BaseLayerMemory 57) = logical 48 :=
    placed agreement (position := 48) (by kernel_rfl)
  have p163 : physical (.BaseLayerWitness 109) = logical 163 :=
    placed agreement (position := 163) (by kernel_rfl)
  have p164 : physical (.BaseLayerWitness 110) = logical 164 :=
    placed agreement (position := 164) (by kernel_rfl)
  have p165 : physical (.BaseLayerWitness 111) = logical 165 :=
    placed agreement (position := 165) (by kernel_rfl)
  simp only [operand5, NativeLookups.Input.fields, sourceFields5, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p14, p55, p56, p57, p22, p67, p68, p69, p30, p79, p80, p81, p38, p91, p92, p93, p46, p103, p104, p105, p16, p115, p116, p117, p24, p127, p128, p129, p32, p139, p140, p141, p40, p151, p152, p153, p48, p163, p164, p165]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields5 physical logical agreement]
  exact source_semantics5 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p58 : physical (.BaseLayerWitness 4) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
  have p70 : physical (.BaseLayerWitness 16) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 28) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  have p94 : physical (.BaseLayerWitness 40) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  have p106 : physical (.BaseLayerWitness 52) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  have p118 : physical (.BaseLayerWitness 64) = logical 118 :=
    placed agreement (position := 118) (by kernel_rfl)
  have p130 : physical (.BaseLayerWitness 76) = logical 130 :=
    placed agreement (position := 130) (by kernel_rfl)
  have p142 : physical (.BaseLayerWitness 88) = logical 142 :=
    placed agreement (position := 142) (by kernel_rfl)
  have p154 : physical (.BaseLayerWitness 100) = logical 154 :=
    placed agreement (position := 154) (by kernel_rfl)
  have p166 : physical (.BaseLayerWitness 112) = logical 166 :=
    placed agreement (position := 166) (by kernel_rfl)
  simp only [operand6, NativeLookups.Input.fields, sourceFields6, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p58, p70, p82, p94, p106, p118, p130, p142, p154, p166]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields6 physical logical agreement]
  exact source_semantics6 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p59 : physical (.BaseLayerWitness 5) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p71 : physical (.BaseLayerWitness 17) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p83 : physical (.BaseLayerWitness 29) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p95 : physical (.BaseLayerWitness 41) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p107 : physical (.BaseLayerWitness 53) = logical 107 :=
    placed agreement (position := 107) (by kernel_rfl)
  have p119 : physical (.BaseLayerWitness 65) = logical 119 :=
    placed agreement (position := 119) (by kernel_rfl)
  have p131 : physical (.BaseLayerWitness 77) = logical 131 :=
    placed agreement (position := 131) (by kernel_rfl)
  have p143 : physical (.BaseLayerWitness 89) = logical 143 :=
    placed agreement (position := 143) (by kernel_rfl)
  have p155 : physical (.BaseLayerWitness 101) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  have p167 : physical (.BaseLayerWitness 113) = logical 167 :=
    placed agreement (position := 167) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p59, p71, p83, p95, p107, p119, p131, p143, p155, p167]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields7 physical logical agreement]
  exact source_semantics7 logical


end Airbender.Compiler.WorkerConstraints.KeccakChi5
