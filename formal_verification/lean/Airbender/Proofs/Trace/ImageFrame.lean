import Airbender.Proofs.Trace.InitialImage

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

theorem image_frame {cells : List Cell} {tokens : List (MemoryToken p)} {before after : State}
    (image : initialImage before cells = some tokens)
    (frame : ∀ cell ∈ cells, ∀ value,
      cell.read before = .ok value before → cell.read after = .ok value after) :
    initialImage after cells = some tokens := by
  have reads := image_reads image
  clear image
  induction reads with
  | nil => rfl
  | @cons cell token cells tokens head tail ih =>
    obtain ⟨value, read, same⟩ := head
    have current := frame cell List.mem_cons_self value read
    have rest := ih (fun actual member => frame actual (List.mem_cons_of_mem _ member))
    dsimp only [initialImage] at rest
    simp only [initialImage, List.mapM_cons, current, bind, Option.bind, pure, same]
    rw [rest]

end Airbender.Trace.Proofs
