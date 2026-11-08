module
public import Slop.KeccakSplit.Memory.History
public import Slop.Delegation.CallGroups

@[expose] public section

/- One split row's accesses happen at one clock, so the memory argument makes
   their addresses distinct; in any Sail history of exactly those accesses every
   port reads its native value in the row's start state (as
   Slop.Delegation.AtomicHistory does for the other workers). -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs
set_option warningAsError true

private theorem member_flatMap_sublist (f : α → List β) {items : List α} {item : α}
    (member : item ∈ items) : (f item).Sublist (items.flatMap f) := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst first
      exact List.sublist_append_left _ _
    · exact (ih member).trans (List.sublist_append_right _ _)

private theorem row_events_sublist {data : MemoryData p} {row : Row p} (member : row ∈ data.rows) :
    (row.memorySteps.map transferEvent).Sublist (Transfer.rawEvents (transferData data)) := by
  simp only [Transfer.rawEvents, transferData, MemoryData.steps, List.map_flatMap]
  apply List.Sublist.trans ?_ (List.sublist_append_right _ _)
  exact member_flatMap_sublist (fun r : Row p => r.memorySteps.map transferEvent) member

theorem row_no_zero {row : Row p} :
    ∀ event ∈ row.memorySteps.map transferEvent, event.2.1 ≠ (Cell.register 0).addressCode := by
  intro event included
  obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp included
  change edge ∈ row.ports.toList.map (fun port => (readToken row.assignment port, row.writeToken port)) at edgeMember
  obtain ⟨port, portMember, rfl⟩ : ∃ port ∈ row.ports.toList,
    (readToken row.assignment port, row.writeToken port) = edge := List.mem_map.mp edgeMember
  exact port_not_zero row (by simpa only [Array.mem_toList_iff] using portMember)

end Airbender.Keccak.Split.Native.Proofs
