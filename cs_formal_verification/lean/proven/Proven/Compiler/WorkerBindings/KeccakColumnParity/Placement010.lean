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
theorem placement160 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 160 = logical 160 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 160) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[160]'(by decide) = (160, (.BaseLayerMemory 60)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement161 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 161 = logical 161 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 161) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[161]'(by decide) = (161, (.BaseLayerWitness 88)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement162 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 162 = logical 162 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 162) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[162]'(by decide) = (162, (.BaseLayerMemory 66)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement163 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 163 = logical 163 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 163) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[163]'(by decide) = (163, (.BaseLayerMemory 67)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement164 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 164 = logical 164 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 164) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[164]'(by decide) = (164, (.BaseLayerWitness 89)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement165 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 165 = logical 165 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 165) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[165]'(by decide) = (165, (.BaseLayerWitness 90)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement166 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 166 = logical 166 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 166) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[166]'(by decide) = (166, (.BaseLayerWitness 91)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements010 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    ∀ index ∈ List.range' 160 7, placed physical logical index = logical index :=
  (cons_placements (placement160 physical logical agreement) (cons_placements (placement161 physical logical agreement) (cons_placements (placement162 physical logical agreement) (cons_placements (placement163 physical logical agreement) (cons_placements (placement164 physical logical agreement) (cons_placements (placement165 physical logical agreement) (cons_placements (placement166 physical logical agreement) (by intro index member; cases member))))))))
end Airbender.Compiler.WorkerBindings.KeccakColumnParity
