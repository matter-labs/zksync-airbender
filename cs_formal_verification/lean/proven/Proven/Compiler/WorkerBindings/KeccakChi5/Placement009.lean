module
public import Proven.Compiler.WorkerArithmetic.KeccakChi5
public import Human.Compiler.Captures.KeccakChi5
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.WorkerBindings.KeccakChi5.Data
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakChi5
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- This source column has its actual captured physical placement. -/
theorem placement144 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 144 = logical 144 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 144) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[144]'(by decide) = (144, (.BaseLayerWitness 90)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement145 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 145 = logical 145 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 145) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[145]'(by decide) = (145, (.BaseLayerWitness 91)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement146 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 146 = logical 146 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 146) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[146]'(by decide) = (146, (.BaseLayerWitness 92)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement147 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 147 = logical 147 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 147) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[147]'(by decide) = (147, (.BaseLayerWitness 93)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement148 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 148 = logical 148 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 148) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[148]'(by decide) = (148, (.BaseLayerWitness 94)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement149 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 149 = logical 149 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 149) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[149]'(by decide) = (149, (.BaseLayerWitness 95)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement150 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 150 = logical 150 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 150) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[150]'(by decide) = (150, (.BaseLayerWitness 96)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement151 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 151 = logical 151 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 151) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[151]'(by decide) = (151, (.BaseLayerWitness 97)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement152 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 152 = logical 152 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 152) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[152]'(by decide) = (152, (.BaseLayerWitness 98)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement153 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 153 = logical 153 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 153) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[153]'(by decide) = (153, (.BaseLayerWitness 99)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement154 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 154 = logical 154 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 154) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[154]'(by decide) = (154, (.BaseLayerWitness 100)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement155 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 155 = logical 155 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 155) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[155]'(by decide) = (155, (.BaseLayerWitness 101)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement156 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 156 = logical 156 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 156) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[156]'(by decide) = (156, (.BaseLayerWitness 102)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement157 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 157 = logical 157 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 157) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[157]'(by decide) = (157, (.BaseLayerWitness 103)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement158 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 158 = logical 158 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 158) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[158]'(by decide) = (158, (.BaseLayerWitness 104)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement159 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 159 = logical 159 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 159) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[159]'(by decide) = (159, (.BaseLayerWitness 105)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements009 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    ∀ index ∈ List.range' 144 16, placed physical logical index = logical index :=
  (cons_placements (placement144 physical logical agreement) (cons_placements (placement145 physical logical agreement) (cons_placements (placement146 physical logical agreement) (cons_placements (placement147 physical logical agreement) (cons_placements (placement148 physical logical agreement) (cons_placements (placement149 physical logical agreement) (cons_placements (placement150 physical logical agreement) (cons_placements (placement151 physical logical agreement) (cons_placements (placement152 physical logical agreement) (cons_placements (placement153 physical logical agreement) (cons_placements (placement154 physical logical agreement) (cons_placements (placement155 physical logical agreement) (cons_placements (placement156 physical logical agreement) (cons_placements (placement157 physical logical agreement) (cons_placements (placement158 physical logical agreement) (cons_placements (placement159 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakChi5
