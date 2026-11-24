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
theorem placement16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 16 = logical 16 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 16) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[16]'(by decide) = (16, (.BaseLayerMemory 13)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 17 = logical 17 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 17) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[17]'(by decide) = (17, (.BaseLayerMemory 14)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 18 = logical 18 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 18) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[18]'(by decide) = (18, (.BaseLayerMemory 15)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 19 = logical 19 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 19) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[19]'(by decide) = (19, (.BaseLayerMemory 16)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 20 = logical 20 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 20) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[20]'(by decide) = (20, (.BaseLayerMemory 17)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 21 = logical 21 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 21) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[21]'(by decide) = (21, (.BaseLayerMemory 18)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 22 = logical 22 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 22) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[22]'(by decide) = (22, (.BaseLayerMemory 21)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 23 = logical 23 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 23) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[23]'(by decide) = (23, (.BaseLayerMemory 22)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 24 = logical 24 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 24) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[24]'(by decide) = (24, (.BaseLayerMemory 24)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 25 = logical 25 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 25) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[25]'(by decide) = (25, (.BaseLayerMemory 25)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 26 = logical 26 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 26) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[26]'(by decide) = (26, (.BaseLayerMemory 26)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 27 = logical 27 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 27) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[27]'(by decide) = (27, (.BaseLayerMemory 27)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 28 = logical 28 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 28) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[28]'(by decide) = (28, (.BaseLayerMemory 28)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 29 = logical 29 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 29) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[29]'(by decide) = (29, (.BaseLayerMemory 29)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 30 = logical 30 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 30) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[30]'(by decide) = (30, (.BaseLayerMemory 32)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 31 = logical 31 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 31) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[31]'(by decide) = (31, (.BaseLayerMemory 33)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    ∀ index ∈ List.range' 16 16, placed physical logical index = logical index :=
  (cons_placements (placement16 physical logical agreement) (cons_placements (placement17 physical logical agreement) (cons_placements (placement18 physical logical agreement) (cons_placements (placement19 physical logical agreement) (cons_placements (placement20 physical logical agreement) (cons_placements (placement21 physical logical agreement) (cons_placements (placement22 physical logical agreement) (cons_placements (placement23 physical logical agreement) (cons_placements (placement24 physical logical agreement) (cons_placements (placement25 physical logical agreement) (cons_placements (placement26 physical logical agreement) (cons_placements (placement27 physical logical agreement) (cons_placements (placement28 physical logical agreement) (cons_placements (placement29 physical logical agreement) (cons_placements (placement30 physical logical agreement) (cons_placements (placement31 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakChi5
