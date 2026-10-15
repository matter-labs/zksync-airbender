import Airbender.Review.Helpers.Memory.AtomicWrites
import Airbender.Proofs.Trace.SailCells

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

theorem history_cell_writes {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after) :
    ∃ writes, CellWrites writes before after ∧
      writes.map (fun entry => (entry.1.addressCode, entry.2)) =
        events.map (fun event => (event.2.1, memoryWord event.2.2.2)) := by
  induction history with
  | nil => exact ⟨[], .nil _, rfl⟩
  | cons past cell member address read written ih =>
    obtain ⟨writes, execution, equal⟩ := ih
    exact ⟨(_, _) :: writes, .cons execution written, by simp [address, equal]⟩

theorem atomic_writes_of_history {cells : List Cell} {events : List MemoryAccess}
    {before after : State} {writes : List (Cell × BitVec 32)}
    (history : SailHistory cells events before after)
    (projection : (events.map fun event => (event.2.1, memoryWord event.2.2.2)).Perm
      (writes.map fun entry => (entry.1.addressCode, entry.2))) :
    AtomicWrites writes before after := by
  obtain ⟨actual, execution, equal⟩ := history_cell_writes history
  exact ⟨actual, equal.symm ▸ projection, execution⟩

theorem cell_writes_frame {writes : List (Cell × BitVec 32)} {before after : State}
    (execution : CellWrites writes before after)
    (aligned : ∀ entry ∈ writes, entry.1.Aligned) {cell : Cell} (cellAligned : cell.Aligned)
    (untouched : ∀ entry ∈ writes, cell ≠ entry.1) {value : BitVec 32}
    (read : cell.read before = .ok value before) : cell.read after = .ok value after := by
  induction execution with
  | nil => exact read
  | @cons written word rest before middle after past write ih =>
    apply cell_write_frame write (untouched _ List.mem_cons_self)
      (aligned _ List.mem_cons_self) cellAligned
    exact ih (fun e m => aligned e (List.mem_cons_of_mem _ m))
      (fun e m => untouched e (List.mem_cons_of_mem _ m)) read

theorem atomic_writes_frame {writes : List (Cell × BitVec 32)} {before after : State}
    (execution : AtomicWrites writes before after)
    (aligned : ∀ entry ∈ writes, entry.1.Aligned) {cell : Cell} (cellAligned : cell.Aligned)
    (untouched : ∀ entry ∈ writes, cell ≠ entry.1) {value : BitVec 32}
    (read : cell.read before = .ok value before) : cell.read after = .ok value after := by
  obtain ⟨actual, permutation, execution⟩ := execution
  have source (entry : Cell × BitVec 32) (member : entry ∈ actual) :
      ∃ expected ∈ writes, entry.1 = expected.1 := by
    have present := permutation.mem_iff.mp (List.mem_map.mpr ⟨entry, member, rfl⟩)
    obtain ⟨expected, present, same⟩ := List.mem_map.mp present
    exact ⟨expected, present, cell_address_injective (Prod.mk.inj same).1.symm⟩
  apply cell_writes_frame execution _ cellAligned _ read
  · intro entry present
    obtain ⟨expected, member, same⟩ := source entry present
    exact same ▸ aligned expected member
  · intro entry present
    obtain ⟨expected, member, same⟩ := source entry present
    exact same ▸ untouched expected member

end Airbender.Trace.Proofs
