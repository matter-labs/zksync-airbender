module
public import Human.Helpers.Memory.RVAtomicWrites
public import Slop.Delegation.RVCallHistory

@[expose] public section

/-! RV twins of `Trace/AtomicWrites.lean`: an `RVHistory` is an atomic list of RV cell writes; untouched aligned cells
    keep their reads and every declared destination reads its written value. -/

namespace Airbender.Trace.Proofs
set_option warningAsError true

theorem rv_history_cell_writes {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (history : RVHistory cells events before after) :
    ∃ writes, RVCellWrites writes before after ∧
      writes.map (fun entry => (entry.1.addressCode, entry.2)) =
        events.map (fun event => (event.2.1, memoryWord event.2.2.2)) := by
  induction history with
  | nil => exact ⟨[], .nil _, rfl⟩
  | cons past cell member address read written ih =>
    obtain ⟨writes, execution, equal⟩ := ih
    exact ⟨(_, _) :: writes, .cons execution written, by simp [address, equal]⟩

theorem rv_atomic_writes_of_history {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} {writes : List (Cell × BitVec 32)}
    (history : RVHistory cells events before after)
    (projection : (events.map fun event => (event.2.1, memoryWord event.2.2.2)).Perm
      (writes.map fun entry => (entry.1.addressCode, entry.2))) :
    RVAtomicWrites writes before after := by
  obtain ⟨actual, execution, equal⟩ := rv_history_cell_writes history
  exact ⟨actual, equal.symm ▸ projection, execution⟩

theorem rv_cell_writes_frame {writes : List (Cell × BitVec 32)} {before after : RV.State}
    (execution : RVCellWrites writes before after)
    (aligned : ∀ entry ∈ writes, entry.1.Aligned) {cell : Cell} (cellAligned : cell.Aligned)
    (untouched : ∀ entry ∈ writes, cell ≠ entry.1) {value : BitVec 32}
    (read : cell.readRV before = some value) : cell.readRV after = some value := by
  induction execution with
  | nil => exact read
  | @cons written word rest before middle after past write ih =>
    apply applyRV_frame write (untouched _ List.mem_cons_self) (aligned _ List.mem_cons_self) cellAligned
    exact ih (fun e m => aligned e (List.mem_cons_of_mem _ m))
      (fun e m => untouched e (List.mem_cons_of_mem _ m)) read

private theorem source_entry {writes actual : List (Cell × BitVec 32)}
    (permutation : (actual.map fun entry => (entry.1.addressCode, entry.2)).Perm
      (writes.map fun entry => (entry.1.addressCode, entry.2)))
    (entry : Cell × BitVec 32) (member : entry ∈ actual) : ∃ expected ∈ writes, entry = expected := by
  have present := permutation.mem_iff.mp (List.mem_map.mpr ⟨entry, member, rfl⟩)
  obtain ⟨expected, present, same⟩ := List.mem_map.mp present
  exact ⟨expected, present, Prod.ext (cell_address_injective (Prod.mk.inj same).1.symm)
    (Prod.mk.inj same).2.symm⟩

theorem rv_atomic_writes_frame {writes : List (Cell × BitVec 32)} {before after : RV.State}
    (execution : RVAtomicWrites writes before after)
    (aligned : ∀ entry ∈ writes, entry.1.Aligned) {cell : Cell} (cellAligned : cell.Aligned)
    (untouched : ∀ entry ∈ writes, cell ≠ entry.1) {value : BitVec 32}
    (read : cell.readRV before = some value) : cell.readRV after = some value := by
  obtain ⟨actual, permutation, execution⟩ := execution
  apply rv_cell_writes_frame execution _ cellAligned _ read
  · intro entry present
    obtain ⟨expected, member, rfl⟩ := source_entry permutation entry present
    exact aligned _ member
  · intro entry present
    obtain ⟨expected, member, rfl⟩ := source_entry permutation entry present
    exact untouched _ member

private theorem rv_cell_writes_reads {writes : List (Cell × BitVec 32)} {before after : RV.State}
    (execution : RVCellWrites writes before after) :
    (∀ entry ∈ writes, entry.1.Aligned) →
    (writes.map (fun entry => entry.1.addressCode)).Nodup →
    ∀ {cell : Cell} {value : BitVec 32}, (cell, value) ∈ writes → cell ≠ .register 0 →
      cell.readRV after = some value := by
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
      exact Delegation.Proofs.applyRV_readback write nonzero (aligned _ List.mem_cons_self)
    · have earlier := ih (fun entry included => aligned entry (List.mem_cons_of_mem _ included))
        keys.2 member nonzero
      have different : cell ≠ written := by
        intro same
        subst cell
        exact keys.1 (List.mem_map.mpr ⟨(written, value), member, rfl⟩)
      exact applyRV_frame write different (aligned _ List.mem_cons_self)
        (aligned _ (List.mem_cons_of_mem _ member)) earlier

theorem rv_atomic_writes_reads {writes : List (Cell × BitVec 32)} {before after : RV.State}
    {cell : Cell} {value : BitVec 32}
    (execution : RVAtomicWrites writes before after)
    (aligned : ∀ entry ∈ writes, entry.1.Aligned)
    (distinct : (writes.map (fun entry => entry.1.addressCode)).Nodup)
    (member : (cell, value) ∈ writes) (nonzero : cell ≠ .register 0) :
    cell.readRV after = some value := by
  obtain ⟨actual, permutation, execution⟩ := execution
  have addresses : (actual.map (fun entry => entry.1.addressCode)).Perm
      (writes.map (fun entry => entry.1.addressCode)) := by
    simpa only [List.map_map, Function.comp_def] using permutation.map Prod.fst
  have actualDistinct := addresses.nodup_iff.mpr distinct
  have actualAligned : ∀ entry ∈ actual, entry.1.Aligned := by
    intro entry present
    obtain ⟨expected, included, rfl⟩ := source_entry permutation entry present
    exact aligned _ included
  have mapped := permutation.mem_iff.mpr (List.mem_map.mpr ⟨(cell, value), member, rfl⟩)
  obtain ⟨entry, present, same⟩ := List.mem_map.mp mapped
  have equal : entry = (cell, value) :=
    Prod.ext (cell_address_injective (Prod.mk.inj same).1) (Prod.mk.inj same).2
  subst entry
  exact rv_cell_writes_reads execution actualAligned actualDistinct present nonzero

end Airbender.Trace.Proofs
