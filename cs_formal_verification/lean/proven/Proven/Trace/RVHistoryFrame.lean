module
public import Proven.Trace.RVCells
public import Human.Helpers.Memory.RVHistory

@[expose] public section

/-! RV twins of `MemoryFrame.history_cell_frame` and `AccessExecution.history_access_execution`: an `RVHistory`
    leaves untouched aligned cells' reads unchanged and exposes each access's position. A RAM cell is RAM at any
    address, the shadow RAM below `ROM_END` included (`Cell.applyRV` never fails on RAM). -/

namespace Airbender.Trace.Proofs
set_option warningAsError true

/-- One `Cell.applyRV` update leaves every other aligned cell's RV read unchanged. -/
theorem applyRV_frame {before after : RV.State} {cell other : Cell} {value old : BitVec 32}
    (applied : cell.applyRV value before = some after) (different : other ≠ cell)
    (aligned : cell.Aligned) (otherAligned : other.Aligned)
    (read : other.readRV before = some old) : other.readRV after = some old := by
  unfold Cell.applyRV at applied
  by_cases unchanged : cell.readRV before = some value
  · simp only [unchanged, ↓reduceIte] at applied
    cases Option.some.inj applied
    exact read
  · simp only [unchanged, ↓reduceIte] at applied
    exact writeRV_frame applied different aligned otherAligned read

theorem rv_history_cell_frame {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (history : RVHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (other : Cell) (otherAligned : other.Aligned)
    (untouched : ∀ event ∈ events, event.2.1 ≠ other.addressCode)
    {value : BitVec 32} (read : other.readRV before = some value) :
    other.readRV after = some value := by
  induction history with
  | nil => exact read
  | @cons event rest before middle after past cell member address old written ih =>
    have earlier := ih (fun e m => untouched e (List.mem_cons_of_mem _ m)) read
    apply applyRV_frame written _ (aligned cell member) otherAligned earlier
    intro same
    exact untouched event List.mem_cons_self (by rw [same, address])

theorem rv_history_access_execution {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (history : RVHistory cells events before after)
    {event : MemoryAccess} (present : event ∈ events) :
    ∃ cell ∈ cells, ∃ earlier middle later newer,
      events = newer ++ event :: earlier ∧
      RVHistory cells earlier before middle ∧
      cell.addressCode = event.2.1 ∧
      cell.readRV middle = some (memoryWord event.2.2.1) ∧
      cell.applyRV (memoryWord event.2.2.2) middle = some later ∧
      RVHistory cells newer later after := by
  induction history with
  | nil => cases present
  | @cons head rest before middle after past cell member address read write ih =>
    rcases List.mem_cons.mp present with rfl | previous
    · exact ⟨cell, member, rest, middle, after, [], rfl, past, address, read, write, .nil after⟩
    · obtain ⟨other, domain, earlier, start, finish, newer, shape, old, location, actualRead,
        actualWrite, future⟩ := ih previous
      exact ⟨other, domain, earlier, start, finish, head :: newer, by rw [shape]; rfl,
        old, location, actualRead, actualWrite, .cons future cell member address read write⟩

end Airbender.Trace.Proofs
