module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Queries000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Queries001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p60 : physical (.BaseLayerWitness 6) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p72 : physical (.BaseLayerWitness 18) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 30) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p96 : physical (.BaseLayerWitness 42) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p108 : physical (.BaseLayerWitness 54) = logical 108 :=
    placed agreement (position := 108) (by kernel_rfl)
  have p120 : physical (.BaseLayerWitness 66) = logical 120 :=
    placed agreement (position := 120) (by kernel_rfl)
  have p132 : physical (.BaseLayerWitness 78) = logical 132 :=
    placed agreement (position := 132) (by kernel_rfl)
  have p144 : physical (.BaseLayerWitness 90) = logical 144 :=
    placed agreement (position := 144) (by kernel_rfl)
  have p156 : physical (.BaseLayerWitness 102) = logical 156 :=
    placed agreement (position := 156) (by kernel_rfl)
  have p168 : physical (.BaseLayerWitness 114) = logical 168 :=
    placed agreement (position := 168) (by kernel_rfl)
  simp only [operand8, NativeLookups.Input.fields, sourceFields8, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p60, p72, p84, p96, p108, p120, p132, p144, p156, p168]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields8 physical logical agreement]
  exact source_semantics8 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p15 : physical (.BaseLayerMemory 11) = logical 15 :=
    placed agreement (position := 15) (by kernel_rfl)
  have p58 : physical (.BaseLayerWitness 4) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
  have p59 : physical (.BaseLayerWitness 5) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p60 : physical (.BaseLayerWitness 6) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p23 : physical (.BaseLayerMemory 22) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p70 : physical (.BaseLayerWitness 16) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p71 : physical (.BaseLayerWitness 17) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p72 : physical (.BaseLayerWitness 18) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p31 : physical (.BaseLayerMemory 33) = logical 31 :=
    placed agreement (position := 31) (by kernel_rfl)
  have p82 : physical (.BaseLayerWitness 28) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  have p83 : physical (.BaseLayerWitness 29) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p84 : physical (.BaseLayerWitness 30) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p39 : physical (.BaseLayerMemory 44) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  have p94 : physical (.BaseLayerWitness 40) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  have p95 : physical (.BaseLayerWitness 41) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  have p96 : physical (.BaseLayerWitness 42) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p47 : physical (.BaseLayerMemory 55) = logical 47 :=
    placed agreement (position := 47) (by kernel_rfl)
  have p106 : physical (.BaseLayerWitness 52) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  have p107 : physical (.BaseLayerWitness 53) = logical 107 :=
    placed agreement (position := 107) (by kernel_rfl)
  have p108 : physical (.BaseLayerWitness 54) = logical 108 :=
    placed agreement (position := 108) (by kernel_rfl)
  have p17 : physical (.BaseLayerMemory 14) = logical 17 :=
    placed agreement (position := 17) (by kernel_rfl)
  have p118 : physical (.BaseLayerWitness 64) = logical 118 :=
    placed agreement (position := 118) (by kernel_rfl)
  have p119 : physical (.BaseLayerWitness 65) = logical 119 :=
    placed agreement (position := 119) (by kernel_rfl)
  have p120 : physical (.BaseLayerWitness 66) = logical 120 :=
    placed agreement (position := 120) (by kernel_rfl)
  have p25 : physical (.BaseLayerMemory 25) = logical 25 :=
    placed agreement (position := 25) (by kernel_rfl)
  have p130 : physical (.BaseLayerWitness 76) = logical 130 :=
    placed agreement (position := 130) (by kernel_rfl)
  have p131 : physical (.BaseLayerWitness 77) = logical 131 :=
    placed agreement (position := 131) (by kernel_rfl)
  have p132 : physical (.BaseLayerWitness 78) = logical 132 :=
    placed agreement (position := 132) (by kernel_rfl)
  have p33 : physical (.BaseLayerMemory 36) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  have p142 : physical (.BaseLayerWitness 88) = logical 142 :=
    placed agreement (position := 142) (by kernel_rfl)
  have p143 : physical (.BaseLayerWitness 89) = logical 143 :=
    placed agreement (position := 143) (by kernel_rfl)
  have p144 : physical (.BaseLayerWitness 90) = logical 144 :=
    placed agreement (position := 144) (by kernel_rfl)
  have p41 : physical (.BaseLayerMemory 47) = logical 41 :=
    placed agreement (position := 41) (by kernel_rfl)
  have p154 : physical (.BaseLayerWitness 100) = logical 154 :=
    placed agreement (position := 154) (by kernel_rfl)
  have p155 : physical (.BaseLayerWitness 101) = logical 155 :=
    placed agreement (position := 155) (by kernel_rfl)
  have p156 : physical (.BaseLayerWitness 102) = logical 156 :=
    placed agreement (position := 156) (by kernel_rfl)
  have p49 : physical (.BaseLayerMemory 58) = logical 49 :=
    placed agreement (position := 49) (by kernel_rfl)
  have p166 : physical (.BaseLayerWitness 112) = logical 166 :=
    placed agreement (position := 166) (by kernel_rfl)
  have p167 : physical (.BaseLayerWitness 113) = logical 167 :=
    placed agreement (position := 167) (by kernel_rfl)
  have p168 : physical (.BaseLayerWitness 114) = logical 168 :=
    placed agreement (position := 168) (by kernel_rfl)
  simp only [operand9, NativeLookups.Input.fields, sourceFields9, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p15, p58, p59, p60, p23, p70, p71, p72, p31, p82, p83, p84, p39, p94, p95, p96, p47, p106, p107, p108, p17, p118, p119, p120, p25, p130, p131, p132, p33, p142, p143, p144, p41, p154, p155, p156, p49, p166, p167, p168]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields9 physical logical agreement]
  exact source_semantics9 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p61 : physical (.BaseLayerWitness 7) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  have p73 : physical (.BaseLayerWitness 19) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 31) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p97 : physical (.BaseLayerWitness 43) = logical 97 :=
    placed agreement (position := 97) (by kernel_rfl)
  have p109 : physical (.BaseLayerWitness 55) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  have p121 : physical (.BaseLayerWitness 67) = logical 121 :=
    placed agreement (position := 121) (by kernel_rfl)
  have p133 : physical (.BaseLayerWitness 79) = logical 133 :=
    placed agreement (position := 133) (by kernel_rfl)
  have p145 : physical (.BaseLayerWitness 91) = logical 145 :=
    placed agreement (position := 145) (by kernel_rfl)
  have p157 : physical (.BaseLayerWitness 103) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p169 : physical (.BaseLayerWitness 115) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  simp only [operand10, NativeLookups.Input.fields, sourceFields10, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p61, p73, p85, p97, p109, p121, p133, p145, p157, p169]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields10 physical logical agreement]
  exact source_semantics10 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p62 : physical (.BaseLayerWitness 8) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  have p74 : physical (.BaseLayerWitness 20) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 32) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p98 : physical (.BaseLayerWitness 44) = logical 98 :=
    placed agreement (position := 98) (by kernel_rfl)
  have p110 : physical (.BaseLayerWitness 56) = logical 110 :=
    placed agreement (position := 110) (by kernel_rfl)
  have p122 : physical (.BaseLayerWitness 68) = logical 122 :=
    placed agreement (position := 122) (by kernel_rfl)
  have p134 : physical (.BaseLayerWitness 80) = logical 134 :=
    placed agreement (position := 134) (by kernel_rfl)
  have p146 : physical (.BaseLayerWitness 92) = logical 146 :=
    placed agreement (position := 146) (by kernel_rfl)
  have p158 : physical (.BaseLayerWitness 104) = logical 158 :=
    placed agreement (position := 158) (by kernel_rfl)
  have p170 : physical (.BaseLayerWitness 116) = logical 170 :=
    placed agreement (position := 170) (by kernel_rfl)
  simp only [operand11, NativeLookups.Input.fields, sourceFields11, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p62, p74, p86, p98, p110, p122, p134, p146, p158, p170]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields11 physical logical agreement]
  exact source_semantics11 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p63 : physical (.BaseLayerWitness 9) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p75 : physical (.BaseLayerWitness 21) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 33) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p99 : physical (.BaseLayerWitness 45) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p111 : physical (.BaseLayerWitness 57) = logical 111 :=
    placed agreement (position := 111) (by kernel_rfl)
  have p123 : physical (.BaseLayerWitness 69) = logical 123 :=
    placed agreement (position := 123) (by kernel_rfl)
  have p135 : physical (.BaseLayerWitness 81) = logical 135 :=
    placed agreement (position := 135) (by kernel_rfl)
  have p147 : physical (.BaseLayerWitness 93) = logical 147 :=
    placed agreement (position := 147) (by kernel_rfl)
  have p159 : physical (.BaseLayerWitness 105) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p171 : physical (.BaseLayerWitness 117) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p63, p75, p87, p99, p111, p123, p135, p147, p159, p171]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields12 physical logical agreement]
  exact source_semantics12 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p18 : physical (.BaseLayerMemory 15) = logical 18 :=
    placed agreement (position := 18) (by kernel_rfl)
  have p61 : physical (.BaseLayerWitness 7) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  have p62 : physical (.BaseLayerWitness 8) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  have p63 : physical (.BaseLayerWitness 9) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p26 : physical (.BaseLayerMemory 26) = logical 26 :=
    placed agreement (position := 26) (by kernel_rfl)
  have p73 : physical (.BaseLayerWitness 19) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  have p74 : physical (.BaseLayerWitness 20) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  have p75 : physical (.BaseLayerWitness 21) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p34 : physical (.BaseLayerMemory 37) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  have p85 : physical (.BaseLayerWitness 31) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.BaseLayerWitness 32) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.BaseLayerWitness 33) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p42 : physical (.BaseLayerMemory 48) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  have p97 : physical (.BaseLayerWitness 43) = logical 97 :=
    placed agreement (position := 97) (by kernel_rfl)
  have p98 : physical (.BaseLayerWitness 44) = logical 98 :=
    placed agreement (position := 98) (by kernel_rfl)
  have p99 : physical (.BaseLayerWitness 45) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p50 : physical (.BaseLayerMemory 59) = logical 50 :=
    placed agreement (position := 50) (by kernel_rfl)
  have p109 : physical (.BaseLayerWitness 55) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  have p110 : physical (.BaseLayerWitness 56) = logical 110 :=
    placed agreement (position := 110) (by kernel_rfl)
  have p111 : physical (.BaseLayerWitness 57) = logical 111 :=
    placed agreement (position := 111) (by kernel_rfl)
  have p20 : physical (.BaseLayerMemory 17) = logical 20 :=
    placed agreement (position := 20) (by kernel_rfl)
  have p121 : physical (.BaseLayerWitness 67) = logical 121 :=
    placed agreement (position := 121) (by kernel_rfl)
  have p122 : physical (.BaseLayerWitness 68) = logical 122 :=
    placed agreement (position := 122) (by kernel_rfl)
  have p123 : physical (.BaseLayerWitness 69) = logical 123 :=
    placed agreement (position := 123) (by kernel_rfl)
  have p28 : physical (.BaseLayerMemory 28) = logical 28 :=
    placed agreement (position := 28) (by kernel_rfl)
  have p133 : physical (.BaseLayerWitness 79) = logical 133 :=
    placed agreement (position := 133) (by kernel_rfl)
  have p134 : physical (.BaseLayerWitness 80) = logical 134 :=
    placed agreement (position := 134) (by kernel_rfl)
  have p135 : physical (.BaseLayerWitness 81) = logical 135 :=
    placed agreement (position := 135) (by kernel_rfl)
  have p36 : physical (.BaseLayerMemory 39) = logical 36 :=
    placed agreement (position := 36) (by kernel_rfl)
  have p145 : physical (.BaseLayerWitness 91) = logical 145 :=
    placed agreement (position := 145) (by kernel_rfl)
  have p146 : physical (.BaseLayerWitness 92) = logical 146 :=
    placed agreement (position := 146) (by kernel_rfl)
  have p147 : physical (.BaseLayerWitness 93) = logical 147 :=
    placed agreement (position := 147) (by kernel_rfl)
  have p44 : physical (.BaseLayerMemory 50) = logical 44 :=
    placed agreement (position := 44) (by kernel_rfl)
  have p157 : physical (.BaseLayerWitness 103) = logical 157 :=
    placed agreement (position := 157) (by kernel_rfl)
  have p158 : physical (.BaseLayerWitness 104) = logical 158 :=
    placed agreement (position := 158) (by kernel_rfl)
  have p159 : physical (.BaseLayerWitness 105) = logical 159 :=
    placed agreement (position := 159) (by kernel_rfl)
  have p52 : physical (.BaseLayerMemory 61) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p169 : physical (.BaseLayerWitness 115) = logical 169 :=
    placed agreement (position := 169) (by kernel_rfl)
  have p170 : physical (.BaseLayerWitness 116) = logical 170 :=
    placed agreement (position := 170) (by kernel_rfl)
  have p171 : physical (.BaseLayerWitness 117) = logical 171 :=
    placed agreement (position := 171) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p18, p61, p62, p63, p26, p73, p74, p75, p34, p85, p86, p87, p42, p97, p98, p99, p50, p109, p110, p111, p20, p121, p122, p123, p28, p133, p134, p135, p36, p145, p146, p147, p44, p157, p158, p159, p52, p169, p170, p171]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields13 physical logical agreement]
  exact source_semantics13 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p64 : physical (.BaseLayerWitness 10) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  have p76 : physical (.BaseLayerWitness 22) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p88 : physical (.BaseLayerWitness 34) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p100 : physical (.BaseLayerWitness 46) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  have p112 : physical (.BaseLayerWitness 58) = logical 112 :=
    placed agreement (position := 112) (by kernel_rfl)
  have p124 : physical (.BaseLayerWitness 70) = logical 124 :=
    placed agreement (position := 124) (by kernel_rfl)
  have p136 : physical (.BaseLayerWitness 82) = logical 136 :=
    placed agreement (position := 136) (by kernel_rfl)
  have p148 : physical (.BaseLayerWitness 94) = logical 148 :=
    placed agreement (position := 148) (by kernel_rfl)
  have p160 : physical (.BaseLayerWitness 106) = logical 160 :=
    placed agreement (position := 160) (by kernel_rfl)
  have p172 : physical (.BaseLayerWitness 118) = logical 172 :=
    placed agreement (position := 172) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p64, p76, p88, p100, p112, p124, p136, p148, p160, p172]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields14 physical logical agreement]
  exact source_semantics14 logical

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p65 : physical (.BaseLayerWitness 11) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p77 : physical (.BaseLayerWitness 23) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p89 : physical (.BaseLayerWitness 35) = logical 89 :=
    placed agreement (position := 89) (by kernel_rfl)
  have p101 : physical (.BaseLayerWitness 47) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  have p113 : physical (.BaseLayerWitness 59) = logical 113 :=
    placed agreement (position := 113) (by kernel_rfl)
  have p125 : physical (.BaseLayerWitness 71) = logical 125 :=
    placed agreement (position := 125) (by kernel_rfl)
  have p137 : physical (.BaseLayerWitness 83) = logical 137 :=
    placed agreement (position := 137) (by kernel_rfl)
  have p149 : physical (.BaseLayerWitness 95) = logical 149 :=
    placed agreement (position := 149) (by kernel_rfl)
  have p161 : physical (.BaseLayerWitness 107) = logical 161 :=
    placed agreement (position := 161) (by kernel_rfl)
  have p173 : physical (.BaseLayerWitness 119) = logical 173 :=
    placed agreement (position := 173) (by kernel_rfl)
  simp only [operand15, NativeLookups.Input.fields, sourceFields15, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p65, p77, p89, p101, p113, p125, p137, p149, p161, p173]
  simp only [coefficient_value]
  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]

/-- Source membership is equivalent to the actual placed native tuple membership. -/
theorem refinement15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  rw [fields15 physical logical agreement]
  exact source_semantics15 logical


end Airbender.Compiler.WorkerConstraints.KeccakChi5
