module
public import Proven.Compiler.WorkerArithmetic.KeccakColumnParity
public import Human.Compiler.Captures.KeccakColumnParity
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Data
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakColumnParity
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- This source column has its actual captured physical placement. -/
theorem placement48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 48 = logical 48 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 48) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[48]'(by decide) = (48, (.BaseLayerWitness 1)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 49 = logical 49 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 49) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[49]'(by decide) = (49, (.BaseLayerWitness 2)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 50 = logical 50 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 50) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[50]'(by decide) = (50, (.BaseLayerWitness 3)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 51 = logical 51 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 51) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[51]'(by decide) = (51, (.BaseLayerWitness 4)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement52 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 52 = logical 52 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 52) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[52]'(by decide) = (52, (.BaseLayerWitness 5)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement53 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 53 = logical 53 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 53) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[53]'(by decide) = (53, (.BaseLayerWitness 6)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement54 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 54 = logical 54 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 54) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[54]'(by decide) = (54, (.BaseLayerWitness 7)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement55 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 55 = logical 55 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 55) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[55]'(by decide) = (55, (.BaseLayerWitness 8)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement56 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 56 = logical 56 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 56) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[56]'(by decide) = (56, (.BaseLayerWitness 9)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement57 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 57 = logical 57 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 57) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[57]'(by decide) = (57, (.BaseLayerWitness 10)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement58 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 58 = logical 58 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 58) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[58]'(by decide) = (58, (.BaseLayerWitness 11)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement59 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 59 = logical 59 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 59) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[59]'(by decide) = (59, (.BaseLayerWitness 12)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement60 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 60 = logical 60 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 60) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[60]'(by decide) = (60, (.BaseLayerWitness 13)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement61 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 61 = logical 61 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 61) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[61]'(by decide) = (61, (.BaseLayerWitness 14)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement62 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 62 = logical 62 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 62) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[62]'(by decide) = (62, (.BaseLayerWitness 15)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement63 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 63 = logical 63 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 63) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[63]'(by decide) = (63, (.BaseLayerWitness 16)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    ∀ index ∈ List.range' 48 16, placed physical logical index = logical index :=
  (cons_placements (placement48 physical logical agreement) (cons_placements (placement49 physical logical agreement) (cons_placements (placement50 physical logical agreement) (cons_placements (placement51 physical logical agreement) (cons_placements (placement52 physical logical agreement) (cons_placements (placement53 physical logical agreement) (cons_placements (placement54 physical logical agreement) (cons_placements (placement55 physical logical agreement) (cons_placements (placement56 physical logical agreement) (cons_placements (placement57 physical logical agreement) (cons_placements (placement58 physical logical agreement) (cons_placements (placement59 physical logical agreement) (cons_placements (placement60 physical logical agreement) (cons_placements (placement61 physical logical agreement) (cons_placements (placement62 physical logical agreement) (cons_placements (placement63 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakColumnParity
