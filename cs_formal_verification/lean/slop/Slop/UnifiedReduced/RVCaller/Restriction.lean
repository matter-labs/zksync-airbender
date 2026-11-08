import Slop.UnifiedReduced.RVCaller.HistoryWindow
import Human.Helpers.Delegation.RVBoundaryMemory

/-! RV siblings of `ImageRestriction`, `HistoryRestriction` and `BoundaryRestriction`: restricting an RV seed image,
    an RV history and an RV boundary image to a sub-domain of cells (here: dropping x0). -/

namespace Airbender.Trace.Proofs
set_option warningAsError true

theorem rv_image_restriction {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens)
    (keep : Nat → Bool) :
    initialImageRV before (cells.filter fun cell => keep cell.addressCode) =
      some (tokens.filter fun token => keep token.address) := by
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => rfl
  | @cons cell token cells tokens head tail ih =>
    obtain ⟨value, read, rfl⟩ := head
    simp only [initialImageRV, Cell.initialToken] at ih
    cases selected : keep cell.addressCode <;>
      simp [Cell.initialToken, selected, initialImageRV, List.mapM_cons, read, ih]

theorem rv_history_restriction {cells : List Cell} {events : List MemoryAccess} {before after : RV.State}
    (history : RVHistory cells events before after) (keep : Nat → Bool)
    (selected : ∀ event ∈ events, keep event.2.1 = true) :
    RVHistory (cells.filter fun cell => keep cell.addressCode) events before after := by
  induction history with
  | nil => exact .nil _
  | @cons event rest initial middle finalState past cell member address read written ih =>
    refine .cons (ih (fun previous present => selected previous (List.mem_cons_of_mem event present))) cell ?_
      address read written
    exact List.mem_filter.mpr ⟨member, address ▸ selected event (List.mem_cons_self)⟩

/-- RV sibling of `history_worker_cells`, given that x0 accesses write zero. -/
theorem rv_history_worker_cells {cells : List Cell} {events : List MemoryAccess} {before after : RV.State}
    (history : RVHistory cells events before after)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0) :
    RVHistory (cells.filter fun cell => cell.addressCode != (Cell.register 0).addressCode)
      (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after := by
  apply rv_history_restriction (rv_history_without_zero history zero)
    (fun address => address != (Cell.register 0).addressCode)
  intro event member
  exact bne_iff_ne.mpr (of_decide_eq_true (List.mem_filter.mp member).2)

end Airbender.Trace.Proofs

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs

theorem rv_boundary_image_restriction {tokens : List (MemoryToken p)} {state : RV.State} {cells : List Cell}
    (image : RVBoundaryImage tokens state cells) (keep : Nat → Bool) :
    RVBoundaryImage (tokens.filter fun token => keep token.address) state
      (cells.filter fun cell => keep cell.addressCode) := by
  refine ⟨?_, ?_⟩
  · have keys := image.addresses.filter keep
    simpa only [List.filter_map, Function.comp_def] using keys
  · intro token member
    obtain ⟨present, selected⟩ := List.mem_filter.mp member
    obtain ⟨cell, cellMember, value, address, read, word⟩ := image.values token present
    exact ⟨cell, List.mem_filter.mpr ⟨cellMember, address ▸ selected⟩, value, address, read, word⟩

end Airbender.Delegation.Proofs
