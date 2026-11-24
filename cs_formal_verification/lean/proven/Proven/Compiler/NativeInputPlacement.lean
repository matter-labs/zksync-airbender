module
public import Proven.Compiler.PlacementWitness
public import Proven.GKRProtocol.BaseAssignment
@[expose] public section
namespace Airbender.Compiler.NativePlacementWitness
open NativeArithmetic

/-- Ordered source inputs bind every logical placement to its preserved physical value. -/
theorem agrees_with_ordered_inputs (sourceInputs : List GKRAddress) (positive : 0 < sourceInputs.length)
    (circuit : Circuit)
    (binding : circuit.placement_data.entries.toList = sourceInputs.zipIdx.map Prod.swap)
    (physical : GKRAddress → F) (logical : Nat → F)
    (preserved : ∀ index, physical ((WireBank.ofList sourceInputs positive).address index) = logical index.val) :
    PlacementAgreement circuit physical logical := by
  intro entry member
  have listed : entry ∈ circuit.placement_data.entries.toList := by simpa using member
  rw [binding] at listed
  obtain ⟨⟨address, index⟩, zipMember, rfl⟩ := List.mem_map.mp listed
  obtain ⟨bound, addressBinding⟩ := List.mem_zipIdx' zipMember
  have value := preserved ⟨index, bound⟩
  change physical sourceInputs[index] = logical index at value
  rw [← addressBinding] at value
  exact value.symm

/-- A physical input permutation retains each logical value at its captured placement. -/
theorem agrees_with_reindexed_inputs (sourceInputs : List GKRAddress) (positive : 0 < sourceInputs.length)
    (inputOrder : Array Nat) (circuit : Circuit)
    (binding : circuit.placement_data.entries.toList.Perm (sourceInputs.zipIdx.map fun entry =>
      ((inputOrder[entry.2]?).getD 0, entry.1)))
    (physical : GKRAddress → F) (logical : Nat → F)
    (preserved : ∀ index, physical ((WireBank.ofList sourceInputs positive).address index) =
      logical ((inputOrder[index.val]?).getD 0)) : PlacementAgreement circuit physical logical := by
  intro entry member
  have listed : entry ∈ circuit.placement_data.entries.toList := by simpa using member
  have listed := binding.mem_iff.mp listed
  obtain ⟨⟨address, index⟩, zipMember, rfl⟩ := List.mem_map.mp listed
  obtain ⟨bound, addressBinding⟩ := List.mem_zipIdx' zipMember
  have value := preserved ⟨index, bound⟩
  change physical sourceInputs[index] = logical ((inputOrder[index]?).getD 0) at value
  rw [← addressBinding] at value
  exact value.symm

end Airbender.Compiler.NativePlacementWitness
