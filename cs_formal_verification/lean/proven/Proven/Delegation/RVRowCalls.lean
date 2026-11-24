module
public import Proven.Delegation.RVCallHistory

@[expose] public section

/-! Every worker row of a delegation pool is one contiguous call inside a realized RV history of the pool: its
    accesses share one native clock that no other row uses (every family's first port is x10), so in native timestamp
    order they form one block between the call's pre-state and post-state. RAM cells are RAM at any address, the
    shadow RAM below `ROM_END` included. -/

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs
set_option warningAsError true

/-- RV `clock_slice`: a timestamp-ordered RV history splits at one clock into older, current and newer parts. -/
theorem rv_clock_slice {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells events before after) (clock : Nat) :
    ∃ start finish,
      events = (events.filter fun event => decide (clock < event.1)) ++
        (events.filter fun event => decide (event.1 = clock)) ++
        (events.filter fun event => decide (event.1 < clock)) ∧
      RVHistory cells (events.filter fun event => decide (event.1 < clock)) before start ∧
      RVHistory cells (events.filter fun event => decide (event.1 = clock)) start finish ∧
      RVHistory cells (events.filter fun event => decide (clock < event.1)) finish after := by
  have outer := split_clock events ordered (clock + 1)
  have inner := split_clock (events.filter fun event => decide (event.1 < clock + 1))
    (ordered.sublist List.filter_sublist) clock
  have recent : (events.filter fun event => decide (clock + 1 ≤ event.1)) =
      (events.filter fun event => decide (clock < event.1)) := by
    apply List.filter_congr
    intro event _
    simp only [decide_eq_decide]
    omega
  have equal : ((events.filter fun event => decide (event.1 < clock + 1)).filter
      fun event => decide (clock ≤ event.1)) = (events.filter fun event => decide (event.1 = clock)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro event _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have old : ((events.filter fun event => decide (event.1 < clock + 1)).filter
      fun event => decide (event.1 < clock)) = (events.filter fun event => decide (event.1 < clock)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro event _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [equal, old] at inner
  rw [recent, ← inner] at outer
  obtain ⟨finish, earlier, newer⟩ := rv_history_append.mp (outer.symm ▸ history)
  obtain ⟨start, past, current⟩ := rv_history_append.mp earlier
  exact ⟨start, finish, by simpa only [List.append_assoc] using outer.symm, past, current, newer⟩

/-- The native clock of every access of a delegation row (invocation plus the port offset two, plus one). -/
def rowClock (row : Row p) : Nat := (decodeTimestamp row.assignment row.columns.invocation).value + 3

theorem row_event_clock [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedProofs.SeedInputs data cells) {row : Row p} (member : row ∈ data.rows) :
    ∀ event ∈ row.memorySteps.map transferEvent, event.1 = rowClock row := by
  intro event present
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
  have ported : port ∈ row.ports := by simpa only [Array.mem_toList_iff] using portMember
  have time := (SeedProofs.writes_bounded hp accepted inputs member ported).2
  rw [port_offset row ported] at time
  simp only [transferEvent, time, rowClock]

/-- Every delegation family's first port is the register x10. -/
theorem row_register_ten (row : Row p) : ∃ port ∈ row.ports, port.address = .constantRegister 10 := by
  have first : (row.ports.toList.head?.map MemoryPort.address) = some (.constantRegister 10) := by
    cases row with
    | mk family w => cases family <;> rfl
  obtain ⟨port, head, address⟩ := Option.map_eq_some_iff.mp first
  exact ⟨port, by simpa only [Array.mem_toList_iff] using List.mem_of_head? head, address⟩

private theorem keyed_nodup {rows : List α} (clock : α → Nat) (accesses : α → List (Nat × Nat)) (key : Nat)
    (unique : (rows.flatMap accesses).Nodup) (keyed : ∀ row ∈ rows, (clock row, key) ∈ accesses row) :
    (rows.map clock).Nodup := by
  induction rows with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
    rw [List.flatMap_cons] at unique
    have split := List.nodup_append.mp unique
    refine List.nodup_cons.mpr ⟨?_, ih split.2.1 (fun row member => keyed row (List.mem_cons_of_mem _ member))⟩
    intro present
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp present
    have mine := keyed first List.mem_cons_self
    have theirs : (clock first, key) ∈ rest.flatMap accesses :=
      List.mem_flatMap.mpr ⟨other, otherMember, same ▸ keyed other (List.mem_cons_of_mem _ otherMember)⟩
    exact split.2.2 _ mine _ theirs rfl

/-- No two rows of a pool share a native clock. -/
theorem seed_row_clocks_distinct [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedProofs.SeedInputs data cells) :
    (data.rows.map rowClock).Nodup := by
  have raw := seed_raw_address_clocks_distinct hp accepted inputs
  have steps : ((data.steps.map transferEvent).map fun event => (event.1, event.2.1)).Nodup := by
    refine List.Nodup.sublist ?_ raw
    simp only [rawEvents, Trace.Proofs.Transfer.rawEvents, transferData]
    exact (List.sublist_append_right _ _).map _
  have pooled : (data.steps.map transferEvent).map (fun event => (event.1, event.2.1)) =
      data.rows.flatMap (fun row => (row.memorySteps.map transferEvent).map fun event => (event.1, event.2.1)) := by
    simp only [MemoryData.steps, List.map_flatMap]
  rw [pooled] at steps
  apply keyed_nodup rowClock _ (Nat.pair 0 (Nat.pair 10 0)) steps
  intro row member
  obtain ⟨port, portMember, address⟩ := row_register_ten row
  have event : transferEvent (readToken row.assignment port, row.writeToken port) ∈
      row.memorySteps.map transferEvent :=
    List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨port, by simpa only [Array.mem_toList_iff] using portMember, rfl⟩, rfl⟩
  have time := row_event_clock (by omega) accepted inputs member _ event
  refine List.mem_map.mpr ⟨_, event, ?_⟩
  rw [time]
  simp only [transferEvent, readToken, address, MemoryAddress.code]

/-- Each pool row is one contiguous call of a timestamp-ordered RV history of all the pool's accesses. -/
theorem rv_row_call [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedProofs.SeedInputs data cells)
    {events : List MemoryAccess} {before after : RV.State}
    (permutation : events.Perm (data.steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : RVHistory cells events before after)
    {row : Row p} (member : row ∈ data.rows) :
    ∃ earlier current newer start finish,
      events = newer ++ current ++ earlier ∧
      current.Perm (row.memorySteps.map transferEvent) ∧
      RVHistory cells earlier before start ∧
      RVHistory cells current start finish ∧
      RVHistory cells newer finish after := by
  obtain ⟨start, finish, split, past, call, newer⟩ := rv_clock_slice ordered history (rowClock row)
  have pooled : data.steps.map transferEvent = data.rows.flatMap (fun row => row.memorySteps.map transferEvent) := by
    simp only [MemoryData.steps, List.map_flatMap]
  have grouped := call_group_perm rowClock (fun row => row.memorySteps.map transferEvent)
    (seed_row_clocks_distinct hp accepted inputs) (pooled ▸ permutation)
    (fun row member => row_event_clock (by omega) accepted inputs member) member
  exact ⟨_, _, _, start, finish, split, grouped, past, call, newer⟩

end Airbender.Delegation.Proofs
