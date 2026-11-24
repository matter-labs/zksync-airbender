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
theorem placement0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 0 = logical 0 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 0) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[0]'(by decide) = (0, (.BaseLayerMemory 69)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 1 = logical 1 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 1) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[1]'(by decide) = (1, (.BaseLayerMemory 70)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 2 = logical 2 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 2) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[2]'(by decide) = (2, (.BaseLayerMemory 71)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 3 = logical 3 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 3) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[3]'(by decide) = (3, (.BaseLayerMemory 2)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 4 = logical 4 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 4) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[4]'(by decide) = (4, (.BaseLayerMemory 3)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 5 = logical 5 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 5) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[5]'(by decide) = (5, (.BaseLayerMemory 4)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 6 = logical 6 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 6) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[6]'(by decide) = (6, (.BaseLayerMemory 5)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 7 = logical 7 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 7) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[7]'(by decide) = (7, (.BaseLayerMemory 12)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 8 = logical 8 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 8) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[8]'(by decide) = (8, (.BaseLayerMemory 21)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 9 = logical 9 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 9) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[9]'(by decide) = (9, (.BaseLayerMemory 30)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 10 = logical 10 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 10) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[10]'(by decide) = (10, (.BaseLayerMemory 39)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 11 = logical 11 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 11) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[11]'(by decide) = (11, (.BaseLayerMemory 48)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 12 = logical 12 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 12) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[12]'(by decide) = (12, (.BaseLayerMemory 59)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 13 = logical 13 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 13) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[13]'(by decide) = (13, (.BaseLayerMemory 66)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 14 = logical 14 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 14) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[14]'(by decide) = (14, (.BaseLayerMemory 6)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 15 = logical 15 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 15) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[15]'(by decide) = (15, (.BaseLayerMemory 7)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    ∀ index ∈ List.range' 0 16, placed physical logical index = logical index :=
  (cons_placements (placement0 physical logical agreement) (cons_placements (placement1 physical logical agreement) (cons_placements (placement2 physical logical agreement) (cons_placements (placement3 physical logical agreement) (cons_placements (placement4 physical logical agreement) (cons_placements (placement5 physical logical agreement) (cons_placements (placement6 physical logical agreement) (cons_placements (placement7 physical logical agreement) (cons_placements (placement8 physical logical agreement) (cons_placements (placement9 physical logical agreement) (cons_placements (placement10 physical logical agreement) (cons_placements (placement11 physical logical agreement) (cons_placements (placement12 physical logical agreement) (cons_placements (placement13 physical logical agreement) (cons_placements (placement14 physical logical agreement) (cons_placements (placement15 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
