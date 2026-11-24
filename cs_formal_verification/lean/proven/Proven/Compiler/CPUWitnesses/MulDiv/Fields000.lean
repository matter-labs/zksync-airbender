module
public import Proven.Compiler.CPUWitnesses.MulDiv.Queries000

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.MulDiv
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p28 : physical (.BaseLayerMemory 15) = logical 28 :=
    placed agreement (position := 28) (by kernel_rfl)
  change [physical (.BaseLayerMemory 15)] = [logical 28]
  exact congrArg (fun value => [value]) p28


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled0 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand0.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p29 : physical (.BaseLayerMemory 16) = logical 29 :=
    placed agreement (position := 29) (by kernel_rfl)
  change [physical (.BaseLayerMemory 16)] = [logical 29]
  exact congrArg (fun value => [value]) p29


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled1 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand1.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p37 : physical (.BaseLayerWitness 11) = logical 37 :=
    placed agreement (position := 37) (by kernel_rfl)
  change [physical (.BaseLayerWitness 11)] = [logical 37]
  exact congrArg (fun value => [value]) p37


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled2 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand2.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p38 : physical (.BaseLayerWitness 12) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  change [physical (.BaseLayerWitness 12)] = [logical 38]
  exact congrArg (fun value => [value]) p38


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled3 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand3.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p39 : physical (.BaseLayerWitness 13) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  change [physical (.BaseLayerWitness 13)] = [logical 39]
  exact congrArg (fun value => [value]) p39


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled4 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand4.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p40 : physical (.BaseLayerWitness 14) = logical 40 :=
    placed agreement (position := 40) (by kernel_rfl)
  change [physical (.BaseLayerWitness 14)] = [logical 40]
  exact congrArg (fun value => [value]) p40


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled5 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand5.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p14 : physical (.BaseLayerMemory 22) = logical 14 :=
    placed agreement (position := 14) (by kernel_rfl)
  change [physical (.BaseLayerMemory 22)] = [logical 14]
  exact congrArg (fun value => [value]) p14


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled6 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand6.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.MulDiv.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p16 : physical (.BaseLayerMemory 24) = logical 16 :=
    placed agreement (position := 16) (by kernel_rfl)
  change [physical (.BaseLayerMemory 24)] = [logical 16]
  exact congrArg (fun value => [value]) p16


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled7 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.MulDiv.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand7.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.MulDiv
