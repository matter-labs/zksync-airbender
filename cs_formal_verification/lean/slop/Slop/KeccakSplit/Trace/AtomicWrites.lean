import Human.Helpers.Memory.AtomicWrites
import Slop.Trace.SailCells

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

private theorem cell_writes_reads {writes : List (Cell × BitVec 32)} {before after : State}
    (execution : CellWrites writes before after) :
    (∀ entry ∈ writes, entry.1.Aligned) →
    (writes.map (fun entry => entry.1.addressCode)).Nodup →
    ∀ {cell : Cell} {value : BitVec 32}, (cell, value) ∈ writes → cell ≠ .register 0 →
      cell.read after = .ok value after := by
  induction execution with
  | nil =>
    intro _ _ cell value member _
    cases member
  | @cons written word rest before middle after past write ih =>
    intro aligned distinct cell value member nonzero
    have keys : written.addressCode ∉ rest.map (fun entry => entry.1.addressCode) ∧
        (rest.map (fun entry => entry.1.addressCode)).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using distinct
    rcases List.mem_cons.mp member with same | member
    · cases same
      obtain ⟨result, actual, readback⟩ := cell_write_readback written word middle
        (fun zero => False.elim (nonzero zero))
      have equal := (EStateM.Result.ok.inj (actual.symm.trans write)).2
      exact equal ▸ readback
    · have earlier := ih (fun entry included => aligned entry (List.mem_cons_of_mem _ included))
        keys.2 member nonzero
      have different : cell ≠ written := by
        intro same
        subst cell
        exact keys.1 (List.mem_map.mpr ⟨(written, value), member, rfl⟩)
      exact cell_write_frame write different (aligned _ List.mem_cons_self)
        (aligned _ (List.mem_cons_of_mem _ member)) earlier

/-- Every distinct declared destination has its actual final written value.
The address distinctness is derived from native matching by callers of this
adapter; existing independent call references and their ABI remain unchanged. -/
theorem atomic_writes_reads {writes : List (Cell × BitVec 32)} {before after : State}
    {cell : Cell} {value : BitVec 32}
    (execution : AtomicWrites writes before after)
    (aligned : ∀ entry ∈ writes, entry.1.Aligned)
    (distinct : (writes.map (fun entry => entry.1.addressCode)).Nodup)
    (member : (cell, value) ∈ writes) (nonzero : cell ≠ .register 0) :
    cell.read after = .ok value after := by
  obtain ⟨actual, permutation, execution⟩ := execution
  have addresses : (actual.map (fun entry => entry.1.addressCode)).Perm
      (writes.map (fun entry => entry.1.addressCode)) := by
    simpa only [List.map_map, Function.comp_def] using permutation.map Prod.fst
  have actualDistinct := addresses.nodup_iff.mpr distinct
  have actualAligned : ∀ entry ∈ actual, entry.1.Aligned := by
    intro entry present
    have mapped := permutation.mem_iff.mp (List.mem_map.mpr ⟨entry, present, rfl⟩)
    obtain ⟨expected, included, same⟩ := List.mem_map.mp mapped
    have equal := cell_address_injective (congrArg Prod.fst same)
    exact equal ▸ aligned expected included
  have mapped := permutation.mem_iff.mpr (List.mem_map.mpr ⟨(cell, value), member, rfl⟩)
  obtain ⟨entry, present, same⟩ := List.mem_map.mp mapped
  have cellEqual := cell_address_injective (congrArg Prod.fst same)
  have valueEqual := congrArg Prod.snd same
  have equal : entry = (cell, value) := Prod.ext cellEqual valueEqual
  subst entry
  exact cell_writes_reads execution actualAligned actualDistinct present nonzero

end Airbender.Trace.Proofs
