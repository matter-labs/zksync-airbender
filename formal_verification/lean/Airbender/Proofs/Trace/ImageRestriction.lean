import Airbender.Proofs.Trace.InitialImage

namespace Airbender.Trace.Proofs
set_option warningAsError true

theorem image_restriction {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens)
    (keep : Nat → Bool) :
    initialImage before (cells.filter fun cell => keep cell.addressCode) =
      some (tokens.filter fun token => keep token.address) := by
  have reads := image_reads image
  clear image
  induction reads with
  | nil => rfl
  | @cons cell token cells tokens head tail ih =>
    obtain ⟨value, read, rfl⟩ := head
    simp only [initialImage, Cell.initialToken] at ih
    cases selected : keep cell.addressCode <;>
      simp [Cell.initialToken, selected, initialImage, List.mapM_cons, read, ih]

end Airbender.Trace.Proofs
