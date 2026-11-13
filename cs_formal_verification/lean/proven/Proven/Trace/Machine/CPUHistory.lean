module
public import Proven.Trace.Machine.CPUEvents
public import Proven.Trace.Machine.HistoryOrder

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

variable {Kind : Type} [CircuitLayout Kind] [ClockLaws Kind babyBearModulus]

/-- The three native CPU ports have successive event clocks. -/
theorem cpu_event_clocks {row : Trace.Row babyBearModulus Kind}
    (clock : (decodeTimestamp row.assignment row.columns.initialTime).Bounded ∧
      (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0) :
    (cpuEvents row row.ports).map Prod.fst = [row.clock + 1, row.clock + 2, row.clock + 3] := by
  calc
    _ = (row.ports.toList.map fun port => port.clock.offset).map (fun offset => row.clock + offset + 1) := by
      simp only [cpuEvents, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro port present
      have time := native_row_write_time clock (by simpa using present)
      change (timeOfPair (writeToken row.columns row.assignment port).time).value + 1 = row.clock + port.clock.offset + 1
      rw [time]
      rfl
    _ = _ := by rw [ClockLaws.offsets row]; simp [Nat.add_assoc]

/-- Reverse native CPU order is strict, so the shared history fixes all three port positions. -/
theorem cpu_events_strict {row : Trace.Row babyBearModulus Kind}
    (clock : (decodeTimestamp row.assignment row.columns.initialTime).Bounded ∧
      (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0) :
    (cpuEvents row row.ports).reverse.Pairwise (fun a b => b.1 < a.1) := by
  have strict : ((cpuEvents row row.ports).reverse.map Prod.fst).Pairwise (fun a b : Nat => b < a) := by
    rw [List.map_reverse, cpu_event_clocks clock]
    simp
  exact List.pairwise_map.mp strict

omit [ClockLaws Kind babyBearModulus] in
/-- Native transfer events and row events have the same address/value payloads. -/
theorem cpu_event_payloads (row : Trace.Row babyBearModulus Kind) (epoch : Nat) :
    (cpuEvents row row.ports).map Prod.snd = (rowEvents epoch row).map Prod.snd := by
  simp only [cpuEvents, rowEvents, nativeRowEvents, List.map_map, Function.comp_def,
    transferEvent, readToken, writeToken, MemoryPort.event]

/-- A sorted ordinary cycle is the existing row history at any history epoch. -/
theorem cpu_row_history {row : Trace.Row babyBearModulus Kind} {cells : List Cell}
    {events : List MemoryAccess} {before after : RV.State} (epoch : Nat)
    (clock : (decodeTimestamp row.assignment row.columns.initialTime).Bounded ∧
      (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0)
    (permutation : events.Perm (cpuEvents row row.ports))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : RVHistory cells events before after) :
    RVHistory cells (rowEvents epoch row).reverse before after := by
  have same := events_eq_of_sorted (permutation.trans (List.reverse_perm _).symm) ordered (cpu_events_strict clock)
  apply history_of_payloads history
  rw [same, List.map_reverse, List.map_reverse, cpu_event_payloads row epoch]

end Airbender.Trace.Machine.Proofs
