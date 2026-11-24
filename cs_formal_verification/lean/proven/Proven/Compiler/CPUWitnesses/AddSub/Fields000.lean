module
public import Proven.Compiler.CPUWitnesses.AddSub.Queries000

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.AddSub
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.AddSub.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p37 : physical (.BaseLayerWitness 11) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  change [physical (.BaseLayerWitness 11)] = [logical 37]
  exact congrArg (fun value => [value]) p37


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled0 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.AddSub.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand0.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.AddSub.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p38 : physical (.BaseLayerWitness 12) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  change [physical (.BaseLayerWitness 12)] = [logical 38]
  exact congrArg (fun value => [value]) p38


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled1 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.AddSub.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand1.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.AddSub.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p33 : physical (.BaseLayerMemory 15) = logical 33 :=
    placed agreement (position := 33) (by kernel_rfl)
  change [physical (.BaseLayerMemory 15)] = [logical 33]
  exact congrArg (fun value => [value]) p33


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled2 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.AddSub.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand2.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.AddSub.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p34 : physical (.BaseLayerMemory 16) = logical 34 :=
    placed agreement (position := 34) (by kernel_rfl)
  change [physical (.BaseLayerMemory 16)] = [logical 34]
  exact congrArg (fun value => [value]) p34


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled3 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.AddSub.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand3.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.AddSub.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p19 : physical (.BaseLayerMemory 22) = logical 19 :=
    placed agreement (position := 19) (by kernel_rfl)
  change [physical (.BaseLayerMemory 22)] = [logical 19]
  exact congrArg (fun value => [value]) p19


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled4 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.AddSub.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand4.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.AddSub.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p21 : physical (.BaseLayerMemory 24) = logical 21 :=
    placed agreement (position := 21) (by kernel_rfl)
  change [physical (.BaseLayerMemory 24)] = [logical 21]
  exact congrArg (fun value => [value]) p21


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled5 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.AddSub.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand5.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.AddSub.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p22 : physical (.BaseLayerMemory 25) = logical 22 :=
    placed agreement (position := 22) (by kernel_rfl)
  change [physical (.BaseLayerMemory 25)] = [logical 22]
  exact congrArg (fun value => [value]) p22


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled6 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.AddSub.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand6.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.AddSub.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p2 : physical (.BaseLayerMemory 20) = logical 2 :=
    placed agreement (position := 2) (by kernel_rfl)
  have p23 : physical (.BaseLayerMemory 0) = logical 23 :=
    placed agreement (position := 23) (by kernel_rfl)
  have p42 : physical (.BaseLayerWitness 16) = logical 42 :=
    placed agreement (position := 42) (by kernel_rfl)
  simp only [operand7, NativeLookups.Input.fields, sourceFields7]
  simp only [linear, ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Import.expression, Import.sum, Import.product, Import.constant, Expression.eval, Verification.environment]
  rw [p2, p23, p42]
  simp only [coefficient_value]
  all_goals norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled7 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.AddSub.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand7.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.AddSub
