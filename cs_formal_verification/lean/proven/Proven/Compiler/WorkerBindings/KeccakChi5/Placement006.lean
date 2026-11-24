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
theorem placement96 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 96 = logical 96 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 96) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[96]'(by decide) = (96, (.BaseLayerWitness 42)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement97 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 97 = logical 97 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 97) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[97]'(by decide) = (97, (.BaseLayerWitness 43)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement98 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 98 = logical 98 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 98) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[98]'(by decide) = (98, (.BaseLayerWitness 44)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement99 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 99 = logical 99 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 99) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[99]'(by decide) = (99, (.BaseLayerWitness 45)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement100 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 100 = logical 100 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 100) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[100]'(by decide) = (100, (.BaseLayerWitness 46)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement101 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 101 = logical 101 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 101) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[101]'(by decide) = (101, (.BaseLayerWitness 47)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement102 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 102 = logical 102 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 102) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[102]'(by decide) = (102, (.BaseLayerWitness 48)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement103 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 103 = logical 103 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 103) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[103]'(by decide) = (103, (.BaseLayerWitness 49)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement104 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 104 = logical 104 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 104) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[104]'(by decide) = (104, (.BaseLayerWitness 50)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement105 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 105 = logical 105 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 105) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[105]'(by decide) = (105, (.BaseLayerWitness 51)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement106 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 106 = logical 106 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 106) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[106]'(by decide) = (106, (.BaseLayerWitness 52)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement107 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 107 = logical 107 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 107) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[107]'(by decide) = (107, (.BaseLayerWitness 53)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement108 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 108 = logical 108 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 108) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[108]'(by decide) = (108, (.BaseLayerWitness 54)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement109 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 109 = logical 109 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 109) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[109]'(by decide) = (109, (.BaseLayerWitness 55)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement110 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 110 = logical 110 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 110) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[110]'(by decide) = (110, (.BaseLayerWitness 56)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
/-- This source column has its actual captured physical placement. -/
theorem placement111 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    placed physical logical 111 = logical 111 := by
  have member := Array.getElem_mem (xs := (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries)
    (i := 111) (by decide)
  have entry : (Airbender.Compiler.Captures.KeccakChi5.imported.circuit).placement_data.entries[111]'(by decide) = (111, (.BaseLayerWitness 57)) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
theorem placements006 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical logical) :
    ∀ index ∈ List.range' 96 16, placed physical logical index = logical index :=
  (cons_placements (placement96 physical logical agreement) (cons_placements (placement97 physical logical agreement) (cons_placements (placement98 physical logical agreement) (cons_placements (placement99 physical logical agreement) (cons_placements (placement100 physical logical agreement) (cons_placements (placement101 physical logical agreement) (cons_placements (placement102 physical logical agreement) (cons_placements (placement103 physical logical agreement) (cons_placements (placement104 physical logical agreement) (cons_placements (placement105 physical logical agreement) (cons_placements (placement106 physical logical agreement) (cons_placements (placement107 physical logical agreement) (cons_placements (placement108 physical logical agreement) (cons_placements (placement109 physical logical agreement) (cons_placements (placement110 physical logical agreement) (cons_placements (placement111 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.WorkerBindings.KeccakChi5
