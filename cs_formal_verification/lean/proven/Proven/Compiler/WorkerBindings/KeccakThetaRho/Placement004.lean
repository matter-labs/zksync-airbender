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
theorem placement64 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 64 = logical 64 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 64) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[64]'(by decide) = (64, (.BaseLayerWitness 0)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement65 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 65 = logical 65 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 65) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[65]'(by decide) = (65, (.BaseLayerWitness 1)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement66 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 66 = logical 66 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 66) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[66]'(by decide) = (66, (.BaseLayerWitness 2)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement67 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 67 = logical 67 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 67) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[67]'(by decide) = (67, (.BaseLayerWitness 3)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement68 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 68 = logical 68 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 68) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[68]'(by decide) = (68, (.BaseLayerWitness 4)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement69 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 69 = logical 69 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 69) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[69]'(by decide) = (69, (.BaseLayerWitness 5)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement70 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 70 = logical 70 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 70) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[70]'(by decide) = (70, (.BaseLayerWitness 6)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement71 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 71 = logical 71 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 71) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[71]'(by decide) = (71, (.BaseLayerWitness 7)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement72 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 72 = logical 72 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 72) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[72]'(by decide) = (72, (.BaseLayerWitness 8)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement73 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 73 = logical 73 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 73) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[73]'(by decide) = (73, (.BaseLayerWitness 9)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement74 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 74 = logical 74 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 74) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[74]'(by decide) = (74, (.BaseLayerWitness 10)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement75 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 75 = logical 75 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 75) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[75]'(by decide) = (75, (.BaseLayerWitness 11)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement76 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 76 = logical 76 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 76) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[76]'(by decide) = (76, (.BaseLayerWitness 12)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement77 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 77 = logical 77 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 77) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[77]'(by decide) = (77, (.BaseLayerWitness 13)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement78 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 78 = logical 78 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 78) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[78]'(by decide) = (78, (.BaseLayerWitness 14)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement79 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 79 = logical 79 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 79) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[79]'(by decide) = (79, (.BaseLayerWitness 15)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements004 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    ∀ index ∈ List.range' 64 16, placed physical logical index = logical index :=
  (cons_placements (placement64 physical logical agreement) (cons_placements (placement65 physical logical agreement) (cons_placements (placement66 physical logical agreement) (cons_placements (placement67 physical logical agreement) (cons_placements (placement68 physical logical agreement) (cons_placements (placement69 physical logical agreement) (cons_placements (placement70 physical logical agreement) (cons_placements (placement71 physical logical agreement) (cons_placements (placement72 physical logical agreement) (cons_placements (placement73 physical logical agreement) (cons_placements (placement74 physical logical agreement) (cons_placements (placement75 physical logical agreement) (cons_placements (placement76 physical logical agreement) (cons_placements (placement77 physical logical agreement) (cons_placements (placement78 physical logical agreement) (cons_placements (placement79 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
