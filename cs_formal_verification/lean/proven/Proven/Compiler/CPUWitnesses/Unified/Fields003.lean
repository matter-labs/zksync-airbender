module
public import Proven.Compiler.CPUWitnesses.Unified.Queries003

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand24.input.fields physical = sourceFields24 logical := by
  have p96 : physical (.InnerLayer 1 22) = logical 96 :=
    placed agreement (position := 96) (by kernel_rfl)
  have p97 : physical (.InnerLayer 1 23) = logical 97 :=
    placed agreement (position := 97) (by kernel_rfl)
  have p98 : physical (.InnerLayer 1 24) = logical 98 :=
    placed agreement (position := 98) (by kernel_rfl)
  have p99 : physical (.InnerLayer 1 25) = logical 99 :=
    placed agreement (position := 99) (by kernel_rfl)
  have p100 : physical (.InnerLayer 1 26) = logical 100 :=
    placed agreement (position := 100) (by kernel_rfl)
  have p101 : physical (.InnerLayer 1 27) = logical 101 :=
    placed agreement (position := 101) (by kernel_rfl)
  have p102 : physical (.InnerLayer 1 28) = logical 102 :=
    placed agreement (position := 102) (by kernel_rfl)
  have p103 : physical (.InnerLayer 1 29) = logical 103 :=
    placed agreement (position := 103) (by kernel_rfl)
  have p95 : physical (.InnerLayer 1 21) = logical 95 :=
    placed agreement (position := 95) (by kernel_rfl)
  simp only [operand24, NativeLookups.Input.fields, sourceFields24, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p96, p97, p98, p99, p100, p101, p102, p103, p95]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled24 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand24.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand25.input.fields physical = sourceFields25 logical := by
  have p105 : physical (.InnerLayer 1 31) = logical 105 :=
    placed agreement (position := 105) (by kernel_rfl)
  have p106 : physical (.InnerLayer 1 32) = logical 106 :=
    placed agreement (position := 106) (by kernel_rfl)
  have p107 : physical (.InnerLayer 1 33) = logical 107 :=
    placed agreement (position := 107) (by kernel_rfl)
  have p108 : physical (.InnerLayer 1 34) = logical 108 :=
    placed agreement (position := 108) (by kernel_rfl)
  have p109 : physical (.InnerLayer 1 35) = logical 109 :=
    placed agreement (position := 109) (by kernel_rfl)
  have p110 : physical (.InnerLayer 1 36) = logical 110 :=
    placed agreement (position := 110) (by kernel_rfl)
  have p111 : physical (.InnerLayer 1 37) = logical 111 :=
    placed agreement (position := 111) (by kernel_rfl)
  have p112 : physical (.InnerLayer 1 38) = logical 112 :=
    placed agreement (position := 112) (by kernel_rfl)
  have p104 : physical (.InnerLayer 1 30) = logical 104 :=
    placed agreement (position := 104) (by kernel_rfl)
  simp only [operand25, NativeLookups.Input.fields, sourceFields25, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p105, p106, p107, p108, p109, p110, p111, p112, p104]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled25 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand25.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand26.input.fields physical = sourceFields26 logical := by
  have p114 : physical (.InnerLayer 1 40) = logical 114 :=
    placed agreement (position := 114) (by kernel_rfl)
  have p115 : physical (.InnerLayer 1 41) = logical 115 :=
    placed agreement (position := 115) (by kernel_rfl)
  have p116 : physical (.InnerLayer 1 42) = logical 116 :=
    placed agreement (position := 116) (by kernel_rfl)
  have p117 : physical (.InnerLayer 1 43) = logical 117 :=
    placed agreement (position := 117) (by kernel_rfl)
  have p118 : physical (.InnerLayer 1 44) = logical 118 :=
    placed agreement (position := 118) (by kernel_rfl)
  have p119 : physical (.InnerLayer 1 45) = logical 119 :=
    placed agreement (position := 119) (by kernel_rfl)
  have p120 : physical (.InnerLayer 1 46) = logical 120 :=
    placed agreement (position := 120) (by kernel_rfl)
  have p121 : physical (.InnerLayer 1 47) = logical 121 :=
    placed agreement (position := 121) (by kernel_rfl)
  have p113 : physical (.InnerLayer 1 39) = logical 113 :=
    placed agreement (position := 113) (by kernel_rfl)
  simp only [operand26, NativeLookups.Input.fields, sourceFields26, List.map_cons, List.map_nil]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p114, p115, p116, p117, p118, p119, p120, p121, p113]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled26 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand26.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.Unified
