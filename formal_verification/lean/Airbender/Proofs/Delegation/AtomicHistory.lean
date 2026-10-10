import Airbender.Proofs.Delegation.History
import Airbender.Proofs.Delegation.Atomic
import Airbender.Proofs.Delegation.SailHistory
import Airbender.Proofs.Delegation.CallState

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

private theorem address_clocks_distinct (events : List MemoryAccess)
    (perAddress : ∀ address, ((events.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup) :
    (events.map fun event => (event.1, event.2.1)).Nodup := by
  induction events with
  | nil => simp
  | cons first rest ih =>
    have tailLocal : ∀ address,
        ((rest.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup := by
      intro address
      have unique := perAddress address
      by_cases same : first.2.1 = address
      · simp only [List.filter_cons, same, decide_true, if_true] at unique
        change (first.1 :: (rest.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup at unique
        exact (List.nodup_cons.mp unique).2
      · simpa [same] using unique
    refine List.nodup_cons.mpr ⟨?_, ih tailLocal⟩
    intro present
    obtain ⟨other, member, equal⟩ := List.mem_map.mp present
    change (other.1, other.2.1) = (first.1, first.2.1) at equal
    have sameTime := (Prod.mk.inj equal).1
    have sameAddress := (Prod.mk.inj equal).2
    have unique := perAddress first.2.1
    have excluded : first.1 ∉ (rest.filter fun event => decide (event.2.1 = first.2.1)).map Prod.fst := by
      simp only [List.filter_cons, decide_true, if_true] at unique
      change (first.1 :: (rest.filter fun event => decide (event.2.1 = first.2.1)).map Prod.fst).Nodup at unique
      exact (List.nodup_cons.mp unique).1
    exact excluded (List.mem_map.mpr ⟨other,
      List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using sameAddress⟩,
      sameTime⟩)

theorem raw_address_clocks_distinct [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    ((rawEvents data).map fun event => (event.1, event.2.1)).Nodup := by
  apply address_clocks_distinct
  intro address
  obtain ⟨history, permutation, _⟩ := raw_cell_history hp accepted inputs address
  have unique : (history.val.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    exact history.property.imp (by
      intro a b less equal
      change b.1 < a.1 at less
      omega)
  exact (permutation.map Prod.fst).nodup_iff.mp unique

private theorem member_flatMap_sublist (f : α → List β) {items : List α} {item : α}
    (member : item ∈ items) : (f item).Sublist (items.flatMap f) := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst first
      exact List.sublist_append_left _ _
    · exact (ih member).trans (List.sublist_append_right _ _)

private theorem row_events_sublist {data : MemoryData p} {row : Row p}
    (member : row ∈ data.rows) : (row.memorySteps.map transferEvent).Sublist (rawEvents data) := by
  simp only [rawEvents, MemoryData.steps, List.map_flatMap]
  apply List.Sublist.trans ?_ (List.sublist_append_right _ _)
  exact member_flatMap_sublist (fun r : Row p => r.memorySteps.map transferEvent) member

theorem row_addresses_distinct [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {row : Row p} (member : row ∈ data.rows) :
    (row.memorySteps.map fun edge => edge.1.address).Nodup := by
  have unique := (raw_address_clocks_distinct hp accepted inputs).sublist
    ((row_events_sublist member).map (fun event => (event.1, event.2.1)))
  let clock := (decodeTimestamp row.assignment row.columns.invocation).value + 3
  have times : (row.memorySteps.map transferEvent).map (fun event => (event.1, event.2.1)) =
      (row.memorySteps.map fun edge => edge.1.address).map (fun address => (clock, address)) := by
    simp only [Row.memorySteps, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro port portMember
    have present : port ∈ row.ports := by simpa only [Array.mem_toList_iff] using portMember
    have time := (writes_bounded (by omega) accepted inputs member present).2
    rw [port_offset row present] at time
    simp only [transferEvent, clock, time]
  rw [times] at unique
  exact unique.of_map _

theorem row_atomic_observations [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {initial before after : State} {cells : List Cell} (inputs : MemoryInputs data initial cells)
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
      row_addresses_distinct hp accepted inputs member
  have noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event eventMember
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp eventMember)
    change edge ∈ row.ports.toList.map (fun port => (readToken row.assignment port, row.writeToken port)) at edgeMember
    obtain ⟨port, portMember, rfl⟩ : ∃ port ∈ row.ports.toList,
      (readToken row.assignment port, row.writeToken port) = edge := List.mem_map.mp edgeMember
    exact port_not_zero row (by simpa only [Array.mem_toList_iff] using portMember)
  have observations := atomic_observations history aligned noZero readable distinct
  intro port portMember
  have present : transferEvent (readToken row.assignment port, row.writeToken port) ∈ events := by
    apply permutation.mem_iff.mpr
    apply List.mem_map.mpr
    refine ⟨(readToken row.assignment port, row.writeToken port), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨port, by simpa only [Array.mem_toList_iff] using portMember, rfl⟩
  exact observations _ present

theorem grouped_atomic_observations [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {initial after : State} {cells : List Cell} (inputs : MemoryInputs data initial cells)
    {ordered : List (Row p)} (permutation : ordered.Perm data.rows)
    (history : GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∀ row ∈ ordered, ∃ events start finish, events.Perm (row.memorySteps.map transferEvent) ∧
      SailHistory cells events start finish ∧
      ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
        cell.read start = .ok (memoryWord (port.readCode row.assignment)) start ∧
        cell.read finish = .ok (memoryWord (port.writeCode row.assignment)) finish := by
  have noZero : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent,
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro row _ event included
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp included
    change edge ∈ row.ports.toList.map (fun port => (readToken row.assignment port, row.writeToken port)) at edgeMember
    obtain ⟨port, portMember, rfl⟩ : ∃ port ∈ row.ports.toList,
      (readToken row.assignment port, row.writeToken port) = edge := List.mem_map.mp edgeMember
    exact port_not_zero row (by simpa only [Array.mem_toList_iff] using portMember)
  have readable : ∀ cell ∈ cells, ∃ value, cell.read initial = .ok value initial := by
    intro cell cellMember
    obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.initialization cell cellMember
    exact ⟨value, read⟩
  have positions := grouped_positions history aligned noZero readable
  intro row rowMember
  obtain ⟨events, start, finish, eventsPerm, current, readable⟩ := positions row rowMember
  exact ⟨events, start, finish, eventsPerm, current,
    row_atomic_observations hp accepted inputs (permutation.mem_iff.mp rowMember) current eventsPerm aligned readable⟩

end Airbender.Delegation.Proofs
