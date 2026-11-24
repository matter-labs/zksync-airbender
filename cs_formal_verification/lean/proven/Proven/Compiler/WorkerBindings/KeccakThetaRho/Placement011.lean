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
theorem placement176 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 176 = logical 176 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 176) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[176]'(by decide) = (176, (.BaseLayerWitness 112)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement177 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 177 = logical 177 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 177) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[177]'(by decide) = (177, (.BaseLayerWitness 113)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement178 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 178 = logical 178 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 178) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[178]'(by decide) = (178, (.BaseLayerWitness 114)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement179 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 179 = logical 179 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 179) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[179]'(by decide) = (179, (.BaseLayerWitness 115)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement180 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 180 = logical 180 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 180) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[180]'(by decide) = (180, (.BaseLayerWitness 116)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement181 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 181 = logical 181 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 181) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[181]'(by decide) = (181, (.BaseLayerWitness 117)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement182 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 182 = logical 182 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 182) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[182]'(by decide) = (182, (.BaseLayerWitness 118)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement183 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 183 = logical 183 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 183) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[183]'(by decide) = (183, (.BaseLayerWitness 119)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement184 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 184 = logical 184 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 184) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[184]'(by decide) = (184, (.BaseLayerWitness 120)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement185 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 185 = logical 185 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 185) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[185]'(by decide) = (185, (.BaseLayerWitness 121)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement186 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 186 = logical 186 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 186) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[186]'(by decide) = (186, (.BaseLayerWitness 122)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement187 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 187 = logical 187 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 187) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[187]'(by decide) = (187, (.BaseLayerWitness 123)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement188 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 188 = logical 188 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 188) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[188]'(by decide) = (188, (.BaseLayerWitness 124)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement189 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 189 = logical 189 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 189) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[189]'(by decide) = (189, (.BaseLayerMemory 0)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement190 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 190 = logical 190 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 190) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[190]'(by decide) = (190, (.BaseLayerMemory 1)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement191 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    placed physical logical 191 = logical 191 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries)
    (i := 191) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).placement_data.entries[191]'(by decide) = (191, (.BaseLayerMemory 8)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements011 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical logical) :
    ∀ index ∈ List.range' 176 16, placed physical logical index = logical index :=
  (cons_placements (placement176 physical logical agreement) (cons_placements (placement177 physical logical agreement) (cons_placements (placement178 physical logical agreement) (cons_placements (placement179 physical logical agreement) (cons_placements (placement180 physical logical agreement) (cons_placements (placement181 physical logical agreement) (cons_placements (placement182 physical logical agreement) (cons_placements (placement183 physical logical agreement) (cons_placements (placement184 physical logical agreement) (cons_placements (placement185 physical logical agreement) (cons_placements (placement186 physical logical agreement) (cons_placements (placement187 physical logical agreement) (cons_placements (placement188 physical logical agreement) (cons_placements (placement189 physical logical agreement) (cons_placements (placement190 physical logical agreement) (cons_placements (placement191 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
