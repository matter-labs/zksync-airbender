import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Sail.WordMemoryState

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false

/-- A finite physical image exists whenever the actual runtime reads succeed.
The proof follows the symbolic domain and evaluates no concrete large list. -/
theorem image_exists_of_reads {p : Nat} {before : State} {domain : List Cell}
    (reads : ∀ cell ∈ domain, ∃ value, cell.read before = .ok value before) :
    ∃ image : List (MemoryToken p), initialImage before domain = some image := by
  induction domain with
  | nil => exact ⟨[], rfl⟩
  | cons cell rest ih =>
    obtain ⟨value, current⟩ := reads cell List.mem_cons_self
    obtain ⟨image, remaining⟩ := ih (fun other member => reads other (List.mem_cons_of_mem cell member))
    refine ⟨cell.initialToken value :: image, ?_⟩
    simp only [initialImage, List.mapM_cons, current, bind, Option.bind]
    change (some (cell.initialToken value)).bind (fun token =>
      (initialImage before rest).bind (fun tokens => some (token :: tokens))) = _
    rw [remaining]
    rfl

/-- Installing one aligned public ROM word preserves existence of the physical
image: a tracked aligned word is either the written word or byte-disjoint.
This does not change native zero ROM-shadow tokens or runtime missing-byte rules. -/
theorem image_word_write_exists {p : Nat} {before : State} {domain : List Cell}
    {image : List (MemoryToken p)} (source : initialImage before domain = some image)
    (aligned : ∀ cell ∈ domain, cell.Aligned)
    (address : Nat) (addressAligned : address % 4 = 0) (value : BitVec 32) :
    ∃ updated : List (MemoryToken p),
      initialImage (wordWriteState before address value) domain = some updated := by
  apply image_exists_of_reads
  intro cell member
  obtain ⟨_, _, oldValue, read, _⟩ := image_cell_source source cell member
  cases cell with
  | register index => exact ⟨oldValue, rX_register_frame (before := before) (after := wordWriteState before address value) rfl index read⟩
  | ram other =>
    by_cases same : other.toNat = address
    · exact ⟨value, by simpa only [Cell.read, same] using written_word_read before address value⟩
    · have otherAligned : other.toNat % 4 = 0 := aligned (.ram other) member
      have disjoint : other.toNat + 4 ≤ address ∨ address + 4 ≤ other.toNat := by omega
      exact ⟨oldValue, written_word_disjoint address value disjoint read⟩

end Airbender.Trace.Proofs
