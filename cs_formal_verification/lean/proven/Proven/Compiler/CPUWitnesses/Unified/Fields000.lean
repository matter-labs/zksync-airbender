module
public import Proven.Compiler.CPUWitnesses.Unified.Queries000

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand0.input.fields physical = sourceFields0 logical := by
  have p74 : physical (.BaseLayerWitness 44) = logical 74 :=
    placed agreement (position := 74) (by kernel_rfl)
  change [physical (.BaseLayerWitness 44)] = [logical 74]
  exact congrArg (fun value => [value]) p74


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled0 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand0.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand1.input.fields physical = sourceFields1 logical := by
  have p75 : physical (.BaseLayerWitness 45) = logical 75 :=
    placed agreement (position := 75) (by kernel_rfl)
  change [physical (.BaseLayerWitness 45)] = [logical 75]
  exact congrArg (fun value => [value]) p75


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled1 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand1.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand2.input.fields physical = sourceFields2 logical := by
  have p50 : physical (.BaseLayerMemory 19) = logical 50 :=
    placed agreement (position := 50) (by kernel_rfl)
  change [physical (.BaseLayerMemory 19)] = [logical 50]
  exact congrArg (fun value => [value]) p50


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled2 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand2.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand3.input.fields physical = sourceFields3 logical := by
  have p51 : physical (.BaseLayerMemory 20) = logical 51 :=
    placed agreement (position := 51) (by kernel_rfl)
  change [physical (.BaseLayerMemory 20)] = [logical 51]
  exact congrArg (fun value => [value]) p51


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled3 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand3.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand4.input.fields physical = sourceFields4 logical := by
  have p1 : physical (.BaseLayerMemory 23) = logical 1 :=
    placed agreement (position := 1) (by kernel_rfl)
  change [physical (.BaseLayerMemory 23)] = [logical 1]
  exact congrArg (fun value => [value]) p1


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled4 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand4.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand5.input.fields physical = sourceFields5 logical := by
  have p64 : physical (.BaseLayerWitness 34) = logical 64 :=
    placed agreement (position := 64) (by kernel_rfl)
  change [physical (.BaseLayerWitness 34)] = [logical 64]
  exact congrArg (fun value => [value]) p64


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled5 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand5.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand6.input.fields physical = sourceFields6 logical := by
  have p38 : physical (.BaseLayerMemory 10) = logical 38 :=
    placed agreement (position := 38) (by kernel_rfl)
  change [physical (.BaseLayerMemory 10)] = [logical 38]
  exact congrArg (fun value => [value]) p38


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled6 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand6.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

/-- The native tuple uses exactly the source lookup columns. -/
theorem fields7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Unified.imported.circuit) physical logical) :
    operand7.input.fields physical = sourceFields7 logical := by
  have p39 : physical (.BaseLayerMemory 11) = logical 39 :=
    placed agreement (position := 39) (by kernel_rfl)
  change [physical (.BaseLayerMemory 11)] = [logical 39]
  exact congrArg (fun value => [value]) p39


/-- Every retained primitive query is enabled on an active CPU row. -/
theorem enabled7 (physical : GKRAddress → F) (logical : Nat → F)
    (_agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (_active : logical 4 = 1) : operand7.weight.value physical ≠ 0 := by
  change (1 : F) ≠ 0
  exact one_ne_zero

end Airbender.Compiler.CPUWitnesses.Unified
