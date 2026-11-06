import Slop.KeccakSplit.Memory.History
import Slop.Delegation.Atomic
import Slop.Delegation.CallBoundaries

/- One split row's accesses happen at one clock, so the memory argument makes
   their addresses distinct; in any Sail history of exactly those accesses every
   port reads its native value in the row's start state (as
   Slop.Delegation.AtomicHistory does for the other workers). -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
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

theorem row_addresses_distinct [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (control : Split.Proofs.ControlFacts p) {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    {row : Row p} (member : row ∈ data.rows) :
    (row.memorySteps.map fun edge => edge.1.address).Nodup := by
  have unique := (Transfer.raw_address_clocks_distinct (transfer_facts hp control accepted active inputs)
    inputs.toNativeInputs.toBoundaryInputs).sublist
    ((row_events_sublist member).map (fun event => (event.1, event.2.1)))
  let clock := (decodeTimestamp row.assignment row.columns.invocation).value + 3
  have times : (row.memorySteps.map transferEvent).map (fun event => (event.1, event.2.1)) =
      (row.memorySteps.map fun edge => edge.1.address).map (fun address => (clock, address)) := by
    simp only [Row.memorySteps, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro port portMember
    have present : port ∈ row.ports := by simpa only [Array.mem_toList_iff] using portMember
    have time := (writes_bounded (by omega) inputs member present).2
    rw [port_offset row present] at time
    simp only [transferEvent, clock, time]
  rw [times] at unique
  exact unique.of_map _

theorem row_no_zero {row : Row p} :
    ∀ event ∈ row.memorySteps.map transferEvent, event.2.1 ≠ (Cell.register 0).addressCode := by
  intro event included
  obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp included
  change edge ∈ row.ports.toList.map (fun port => (readToken row.assignment port, row.writeToken port)) at edgeMember
  obtain ⟨port, portMember, rfl⟩ : ∃ port ∈ row.ports.toList,
    (readToken row.assignment port, row.writeToken port) = edge := List.mem_map.mp edgeMember
  exact port_not_zero row (by simpa only [Array.mem_toList_iff] using portMember)

theorem row_atomic_observations [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (control : Split.Proofs.ControlFacts p) {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {initial before after : State} {cells : List Cell} (inputs : BoundaryInputs data initial cells)
    {row : Row p} (member : row ∈ data.rows) {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
      cell.read before = .ok (memoryWord (port.readCode row.assignment)) before ∧
      cell.read after = .ok (memoryWord (port.writeCode row.assignment)) after := by
  have distinct : (events.map fun event => event.2.1).Nodup := by
    apply (permutation.map (fun event => event.2.1)).nodup_iff.mpr
    simpa only [List.map_map, Function.comp_def, transferEvent] using
      row_addresses_distinct hp control accepted active inputs member
  have noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode :=
    fun event present => row_no_zero event (permutation.mem_iff.mp present)
  have observations := Delegation.Proofs.atomic_observations history aligned noZero readable distinct
  intro port portMember
  have present : transferEvent (readToken row.assignment port, row.writeToken port) ∈ events := by
    apply permutation.mem_iff.mpr
    apply List.mem_map.mpr
    refine ⟨(readToken row.assignment port, row.writeToken port), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨port, by simpa only [Array.mem_toList_iff] using portMember, rfl⟩
  exact observations _ present

end Airbender.Keccak.Split.Native.Proofs
