import Airbender.Proofs.Delegation.BoundaryInputs

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem boundary_image_restriction {tokens : List (MemoryToken p)} {state : State} {cells : List Cell}
    (image : BoundaryImage tokens state cells) (keep : Nat → Bool) :
    BoundaryImage (tokens.filter fun token => keep token.address) state
      (cells.filter fun cell => keep cell.addressCode) := by
  refine ⟨?_, ?_⟩
  · have keys := image.addresses.filter keep
    simpa only [List.filter_map, Function.comp_def] using keys
  · intro token member
    obtain ⟨present, selected⟩ := List.mem_filter.mp member
    obtain ⟨cell, cellMember, value, address, read, word⟩ := image.values token present
    exact ⟨cell, List.mem_filter.mpr ⟨cellMember, address ▸ selected⟩, value, address, read, word⟩

end Airbender.Delegation.Proofs
