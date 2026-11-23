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
theorem placement192 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 192 = logical 192 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 192) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[192]'(by decide) = (192, (.BaseLayerMemory 9)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement193 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 193 = logical 193 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 193) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[193]'(by decide) = (193, (.BaseLayerMemory 55)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement194 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 194 = logical 194 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 194) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[194]'(by decide) = (194, (.BaseLayerMemory 56)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement195 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 195 = logical 195 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 195) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[195]'(by decide) = (195, (.BaseLayerMemory 62)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement196 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 196 = logical 196 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 196) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[196]'(by decide) = (196, (.BaseLayerMemory 63)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement197 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 197 = logical 197 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 197) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[197]'(by decide) = (197, (.BaseLayerWitness 125)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement198 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 198 = logical 198 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 198) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[198]'(by decide) = (198, (.BaseLayerWitness 126)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements012 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    ∀ index ∈ List.range' 192 7, placed physical logical index = logical index :=
  (cons_placements (placement192 physical logical agreement) (cons_placements (placement193 physical logical agreement) (cons_placements (placement194 physical logical agreement) (cons_placements (placement195 physical logical agreement) (cons_placements (placement196 physical logical agreement) (cons_placements (placement197 physical logical agreement) (cons_placements (placement198 physical logical agreement) (by intro index member; cases member))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
