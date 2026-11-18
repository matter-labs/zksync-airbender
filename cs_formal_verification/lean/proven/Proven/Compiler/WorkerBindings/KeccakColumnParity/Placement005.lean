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
theorem placement80 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 80 = logical 80 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 80) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[80]'(by decide) = (80, (.BaseLayerWitness 33)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement81 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 81 = logical 81 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 81) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[81]'(by decide) = (81, (.BaseLayerWitness 34)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement82 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 82 = logical 82 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 82) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[82]'(by decide) = (82, (.BaseLayerWitness 35)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement83 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 83 = logical 83 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 83) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[83]'(by decide) = (83, (.BaseLayerWitness 36)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement84 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 84 = logical 84 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 84) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[84]'(by decide) = (84, (.BaseLayerWitness 37)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement85 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 85 = logical 85 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 85) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[85]'(by decide) = (85, (.BaseLayerWitness 38)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement86 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 86 = logical 86 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 86) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[86]'(by decide) = (86, (.BaseLayerWitness 39)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement87 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 87 = logical 87 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 87) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[87]'(by decide) = (87, (.BaseLayerWitness 40)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement88 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 88 = logical 88 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 88) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[88]'(by decide) = (88, (.BaseLayerWitness 41)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement89 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 89 = logical 89 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 89) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[89]'(by decide) = (89, (.BaseLayerWitness 42)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement90 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 90 = logical 90 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 90) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[90]'(by decide) = (90, (.BaseLayerWitness 43)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement91 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 91 = logical 91 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 91) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[91]'(by decide) = (91, (.BaseLayerWitness 44)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement92 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 92 = logical 92 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 92) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[92]'(by decide) = (92, (.BaseLayerWitness 45)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement93 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 93 = logical 93 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 93) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[93]'(by decide) = (93, (.BaseLayerWitness 46)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement94 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 94 = logical 94 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 94) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[94]'(by decide) = (94, (.BaseLayerWitness 47)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement95 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    placed physical logical 95 = logical 95 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries)
    (i := 95) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).placement_data.entries[95]'(by decide) = (95, (.BaseLayerWitness 48)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements005 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical logical) :
    ∀ index ∈ List.range' 80 16, placed physical logical index = logical index :=
  (cons_placements (placement80 physical logical agreement) (cons_placements (placement81 physical logical agreement) (cons_placements (placement82 physical logical agreement) (cons_placements (placement83 physical logical agreement) (cons_placements (placement84 physical logical agreement) (cons_placements (placement85 physical logical agreement) (cons_placements (placement86 physical logical agreement) (cons_placements (placement87 physical logical agreement) (cons_placements (placement88 physical logical agreement) (cons_placements (placement89 physical logical agreement) (cons_placements (placement90 physical logical agreement) (cons_placements (placement91 physical logical agreement) (cons_placements (placement92 physical logical agreement) (cons_placements (placement93 physical logical agreement) (cons_placements (placement94 physical logical agreement) (cons_placements (placement95 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakColumnParity
