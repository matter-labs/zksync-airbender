import Airbender.Proofs.Trace.AtomicWrites
import Airbender.Proofs.Trace.MemoryFrame

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false

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

/-- A real gap preserves a protected value when every touch refreshes its own
old word. Events at other aligned addresses use the ordinary cell frame rule.
In particular a load can read and refresh a protected token without being
removed from the history. Public instruction syntax must prove the refresh
condition internally; this lemma assumes no desired resulting state. -/
theorem history_cell_frame_of_refresh {cells : List Cell} {events : List MemoryAccess}
    {before after : State} {value : BitVec 32}
    (history : SailHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (other : Cell) (otherAligned : other.Aligned)
    (refresh : ∀ event ∈ events, event.2.1 = other.addressCode →
      memoryWord event.2.2.2 = memoryWord event.2.2.1)
    (read : other.read before = .ok value before) :
    other.read after = .ok value after := by
  induction history with
  | nil => exact read
  | @cons event rest before middle after past cell member address old written ih =>
    have earlier := ih (fun current included => refresh current (List.mem_cons_of_mem _ included)) read
    by_cases sameAddress : event.2.1 = other.addressCode
    · have sameCell := cell_address_injective (address.trans sameAddress)
      subst cell
      have unchanged : run (other.write (memoryWord event.2.2.2)) middle = .ok () middle := by
        rw [refresh event List.mem_cons_self sameAddress]
        exact cell_write_same old
      have sameState := (EStateM.Result.ok.inj (unchanged.symm.trans written)).2
      exact sameState ▸ earlier
    · apply cell_write_frame written _ (aligned cell member) otherAligned earlier
      intro sameCell
      exact sameAddress (address.symm.trans (congrArg Cell.addressCode sameCell).symm)

end Airbender.Trace.Proofs
