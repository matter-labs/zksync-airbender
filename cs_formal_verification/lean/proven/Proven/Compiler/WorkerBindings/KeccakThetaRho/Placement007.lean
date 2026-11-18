module
public import Proven.Compiler.WorkerArithmetic.KeccakThetaRho
public import Human.Compiler.Captures.KeccakThetaRho
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.WorkerBindings.KeccakThetaRho.Data
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakThetaRho
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- This source column has its actual captured physical placement. -/
theorem placement112 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 112 = logical 112 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 112) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[112]'(by decide) = (112, (.BaseLayerWitness 48)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement113 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 113 = logical 113 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 113) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[113]'(by decide) = (113, (.BaseLayerWitness 49)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement114 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 114 = logical 114 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 114) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[114]'(by decide) = (114, (.BaseLayerWitness 50)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement115 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 115 = logical 115 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 115) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[115]'(by decide) = (115, (.BaseLayerWitness 51)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement116 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 116 = logical 116 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 116) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[116]'(by decide) = (116, (.BaseLayerWitness 52)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement117 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 117 = logical 117 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 117) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[117]'(by decide) = (117, (.BaseLayerWitness 53)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement118 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 118 = logical 118 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 118) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[118]'(by decide) = (118, (.BaseLayerWitness 54)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement119 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 119 = logical 119 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 119) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[119]'(by decide) = (119, (.BaseLayerWitness 55)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement120 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 120 = logical 120 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 120) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[120]'(by decide) = (120, (.BaseLayerWitness 56)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement121 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 121 = logical 121 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 121) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[121]'(by decide) = (121, (.BaseLayerWitness 57)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement122 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 122 = logical 122 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 122) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[122]'(by decide) = (122, (.BaseLayerWitness 58)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement123 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 123 = logical 123 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 123) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[123]'(by decide) = (123, (.BaseLayerWitness 59)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement124 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 124 = logical 124 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 124) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[124]'(by decide) = (124, (.BaseLayerWitness 60)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement125 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 125 = logical 125 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 125) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[125]'(by decide) = (125, (.BaseLayerWitness 61)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement126 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 126 = logical 126 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 126) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[126]'(by decide) = (126, (.BaseLayerWitness 62)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement127 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 127 = logical 127 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 127) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[127]'(by decide) = (127, (.BaseLayerWitness 63)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements007 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    ∀ index ∈ List.range' 112 16, placed physical logical index = logical index :=
  (cons_placements (placement112 physical logical agreement) (cons_placements (placement113 physical logical agreement) (cons_placements (placement114 physical logical agreement) (cons_placements (placement115 physical logical agreement) (cons_placements (placement116 physical logical agreement) (cons_placements (placement117 physical logical agreement) (cons_placements (placement118 physical logical agreement) (cons_placements (placement119 physical logical agreement) (cons_placements (placement120 physical logical agreement) (cons_placements (placement121 physical logical agreement) (cons_placements (placement122 physical logical agreement) (cons_placements (placement123 physical logical agreement) (cons_placements (placement124 physical logical agreement) (cons_placements (placement125 physical logical agreement) (cons_placements (placement126 physical logical agreement) (cons_placements (placement127 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
