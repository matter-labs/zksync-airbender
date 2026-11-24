module
public import Proven.Compiler.CPUWitnesses.ShiftBinop.Queries001

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.ShiftBinop
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand8.input.fields physical = sourceFields8 logical := by
  have p0 : physical (.BaseLayerMemory 22) = logical 0 :=
    placed agreement (position := 0) (by kernel_rfl)
  have p1 : physical (.BaseLayerMemory 23) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  have p5 : physical (.BaseLayerMemory 6) = logical 5 :=
    placed agreement (position := 5) (by kernel_rfl)
  have p6 : physical (.BaseLayerMemory 13) = logical 6 :=
    placed agreement (position := 6) (by kernel_rfl)
  have p7 : physical (.BaseLayerMemory 18) = logical 7 :=
    placed agreement (position := 7) (by kernel_rfl)
  have p8 : physical (.BaseLayerWitness 0) = logical 8 :=
    placed agreement (position := 8) (by kernel_rfl)
  have p9 : physical (.BaseLayerWitness 1) = logical 9 :=
    placed agreement (position := 9) (by kernel_rfl)
  have p10 : physical (.BaseLayerWitness 2) = logical 10 :=
    placed agreement (position := 10) (by kernel_rfl)
  have p11 : physical (.BaseLayerWitness 3) = logical 11 :=
    placed agreement (position := 11) (by kernel_rfl)
  have p12 : physical (.BaseLayerWitness 4) = logical 12 :=
    placed agreement (position := 12) (by kernel_rfl)
  simp only [operand8, NativeLookups.Input.fields, sourceFields8, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p0, p1, p5, p6, p7, p8, p9, p10, p11, p12]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (active : logical 4 = 1) : operand8.weight.value physical ≠ 0 := by
  have placed : physical (.BaseLayerMemory 21) = logical 4 :=
    WorkerConstraints.placed agreement (position := 4) (by kernel_rfl)
  change physical (.BaseLayerMemory 21) ≠ 0
  rw [placed, active]
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand9.input.fields physical = sourceFields9 logical := by
  have p14 : physical (.BaseLayerMemory 27) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  change [physical (.BaseLayerMemory 27)] = [logical 14]
  exact congrArg (fun value => [value]) p14


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled9 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand9.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand10.input.fields physical = sourceFields10 logical := by
  have p3 : physical (.BaseLayerMemory 25) = logical 3 :=
    placed agreement (position := 3) (by kernel_rfl)
  have p34 : physical (.BaseLayerMemory 15) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  have p94 : physical (.BaseLayerWitness 24) = logical 94 :=
    placed agreement (position := 94) (by kernel_rfl)
  simp only [operand10, NativeLookups.Input.fields, sourceFields10]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p3, p34, p94]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled10 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand10.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand11.input.fields physical = sourceFields11 logical := by
  have p52 : physical (.InnerLayer 1 5) = logical 52 :=
    placed agreement (position := 52) (by kernel_rfl)
  have p53 : physical (.InnerLayer 1 6) = logical 53 :=
    placed agreement (position := 53) (by kernel_rfl)
  have p54 : physical (.InnerLayer 1 7) = logical 54 :=
    placed agreement (position := 54) (by kernel_rfl)
  have p55 : physical (.InnerLayer 1 8) = logical 55 :=
    placed agreement (position := 55) (by kernel_rfl)
  simp only [operand11, NativeLookups.Input.fields, sourceFields11, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p52, p53, p54, p55]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled11 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand11.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand12.input.fields physical = sourceFields12 logical := by
  have p56 : physical (.InnerLayer 1 9) = logical 56 :=
    placed agreement (position := 56) (by kernel_rfl)
  have p57 : physical (.InnerLayer 1 10) = logical 57 :=
    placed agreement (position := 57) (by kernel_rfl)
  have p58 : physical (.InnerLayer 1 11) = logical 58 :=
    placed agreement (position := 58) (by kernel_rfl)
  have p59 : physical (.InnerLayer 1 12) = logical 59 :=
    placed agreement (position := 59) (by kernel_rfl)
  have p60 : physical (.InnerLayer 1 13) = logical 60 :=
    placed agreement (position := 60) (by kernel_rfl)
  have p61 : physical (.InnerLayer 1 14) = logical 61 :=
    placed agreement (position := 61) (by kernel_rfl)
  have p62 : physical (.InnerLayer 1 15) = logical 62 :=
    placed agreement (position := 62) (by kernel_rfl)
  have p63 : physical (.InnerLayer 1 16) = logical 63 :=
    placed agreement (position := 63) (by kernel_rfl)
  have p64 : physical (.InnerLayer 1 17) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  simp only [operand12, NativeLookups.Input.fields, sourceFields12, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p56, p57, p58, p59, p60, p61, p62, p63, p64]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled12 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand12.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand13.input.fields physical = sourceFields13 logical := by
  have p65 : physical (.InnerLayer 1 18) = logical 65 :=
    placed agreement (position := 65) (by kernel_rfl)
  have p66 : physical (.InnerLayer 1 19) = logical 66 :=
    placed agreement (position := 66) (by kernel_rfl)
  have p67 : physical (.InnerLayer 1 20) = logical 67 :=
    placed agreement (position := 67) (by kernel_rfl)
  have p68 : physical (.InnerLayer 1 21) = logical 68 :=
    placed agreement (position := 68) (by kernel_rfl)
  have p69 : physical (.InnerLayer 1 22) = logical 69 :=
    placed agreement (position := 69) (by kernel_rfl)
  have p70 : physical (.InnerLayer 1 23) = logical 70 :=
    placed agreement (position := 70) (by kernel_rfl)
  have p71 : physical (.InnerLayer 1 24) = logical 71 :=
    placed agreement (position := 71) (by kernel_rfl)
  have p72 : physical (.InnerLayer 1 25) = logical 72 :=
    placed agreement (position := 72) (by kernel_rfl)
  have p73 : physical (.InnerLayer 1 26) = logical 73 :=
    placed agreement (position := 73) (by kernel_rfl)
  simp only [operand13, NativeLookups.Input.fields, sourceFields13, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p65, p66, p67, p68, p69, p70, p71, p72, p73]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled13 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand13.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand14.input.fields physical = sourceFields14 logical := by
  have p74 : physical (.InnerLayer 1 27) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  have p75 : physical (.InnerLayer 1 28) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  have p76 : physical (.InnerLayer 1 29) = logical 76 :=
    placed agreement (position := 76) (by kernel_rfl)
  have p77 : physical (.InnerLayer 1 30) = logical 77 :=
    placed agreement (position := 77) (by kernel_rfl)
  have p78 : physical (.InnerLayer 1 31) = logical 78 :=
    placed agreement (position := 78) (by kernel_rfl)
  have p79 : physical (.InnerLayer 1 32) = logical 79 :=
    placed agreement (position := 79) (by kernel_rfl)
  have p80 : physical (.InnerLayer 1 33) = logical 80 :=
    placed agreement (position := 80) (by kernel_rfl)
  have p81 : physical (.InnerLayer 1 34) = logical 81 :=
    placed agreement (position := 81) (by kernel_rfl)
  have p82 : physical (.InnerLayer 1 35) = logical 82 :=
    placed agreement (position := 82) (by kernel_rfl)
  simp only [operand14, NativeLookups.Input.fields, sourceFields14, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p74, p75, p76, p77, p78, p79, p80, p81, p82]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled14 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand14.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.ShiftBinop.imported.circuit) physical logical) :
    operand15.input.fields physical = sourceFields15 logical := by
  have p83 : physical (.InnerLayer 1 36) = logical 83 :=
    placed agreement (position := 83) (by kernel_rfl)
  have p84 : physical (.InnerLayer 1 37) = logical 84 :=
    placed agreement (position := 84) (by kernel_rfl)
  have p85 : physical (.InnerLayer 1 38) = logical 85 :=
    placed agreement (position := 85) (by kernel_rfl)
  have p86 : physical (.InnerLayer 1 39) = logical 86 :=
    placed agreement (position := 86) (by kernel_rfl)
  have p87 : physical (.InnerLayer 1 40) = logical 87 :=
    placed agreement (position := 87) (by kernel_rfl)
  have p88 : physical (.InnerLayer 1 41) = logical 88 :=
    placed agreement (position := 88) (by kernel_rfl)
  have p89 : physical (.InnerLayer 1 42) = logical 89 :=
    placed agreement (position := 89) (by kernel_rfl)
  have p90 : physical (.InnerLayer 1 43) = logical 90 :=
    placed agreement (position := 90) (by kernel_rfl)
  have p91 : physical (.InnerLayer 1 44) = logical 91 :=
    placed agreement (position := 91) (by kernel_rfl)
  simp only [operand15, NativeLookups.Input.fields, sourceFields15, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p83, p84, p85, p86, p87, p88, p89, p90, p91]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled15 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand15.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.ShiftBinop
