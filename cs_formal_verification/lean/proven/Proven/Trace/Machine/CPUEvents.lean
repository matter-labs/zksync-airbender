module
public import Proven.Trace.Machine.MemoryClocks

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Architectural events retain each native port's write time and value. -/
def cpuEvents {Kind : Type} [CircuitLayout Kind] (row : Trace.Row babyBearModulus Kind)
    (ports : Array MemoryPort) : List MemoryAccess :=
  ports.toList.map fun port => transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port)

variable {Kind : Type} [CircuitLayout Kind] [ClockLaws Kind babyBearModulus]

/-- Native CPU events occupy the first three ticks of their four-tick cycle. -/
theorem cpu_event_time {trace : Data babyBearModulus Kind}
    (constraints : ∀ row ∈ trace.rows, FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus Kind} (member : row ∈ trace.rows) {ports : Array MemoryPort}
    (native : ∀ port ∈ ports, port ∈ row.ports) {event : MemoryAccess} (present : event ∈ cpuEvents row ports) :
    ∃ offset < 3, event.1 = row.clock + offset + 1 := by
  obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
  have portMember := native port (by simpa using included)
  have clock := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1) constraints states initial aligned row member
  have offsets : row.ports.toList.map (fun port => port.clock.offset) = [0, 1, 2] := ClockLaws.offsets row
  have selected : port.clock.offset ∈ row.ports.toList.map (fun port => port.clock.offset) :=
    List.mem_map.mpr ⟨port, by simpa using portMember, rfl⟩
  rw [offsets] at selected
  have bound : port.clock.offset < 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
    omega
  have time := (write_time (by decide : timestampBase < babyBearModulus)
    (base := rawPair row.assignment row.columns.initialTime) clock.1 clock.2
    (by omega : port.clock.offset < 4)).2
  exact ⟨port.clock.offset, bound, by
    simpa only [transferEvent, Trace.Row.clock, writeToken, decodeTimestamp, timeOfPair, rawPair]
      using congrArg (fun n => n + 1) time⟩

/-- An architectural event belongs to exactly one CPU cycle, even when PCs repeat. -/
theorem cpu_event_window {trace : Data babyBearModulus Kind}
    (constraints : ∀ row ∈ trace.rows, FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row other : Trace.Row babyBearModulus Kind} (member : row ∈ trace.rows) (included : other ∈ trace.rows)
    {ports : Array MemoryPort} (native : ∀ port ∈ ports, port ∈ other.ports)
    {event : MemoryAccess} (present : event ∈ cpuEvents other ports) :
    (row.clock < event.1 ∧ event.1 ≤ row.clock + 4) ↔ other = row := by
  have clocks := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1) constraints states initial aligned
  have rankAligned : ∀ source ∈ trace.rows, source.clock % 4 = 0 := by
    intro source present
    have clock := (clocks source present).2
    simpa [Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using clock
  have current := rankAligned row member
  have previous := rankAligned other included
  obtain ⟨offset, bound, time⟩ := cpu_event_time constraints states initial aligned included native present
  constructor
  · intro interval
    have same : other.clock = row.clock := by omega
    have unique := state_clocks_unique (by decide : 2 * timestampBase + 4 < babyBearModulus)
      (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1) constraints states initial aligned
    exact List.inj_on_of_nodup_map unique included member same
  · intro same
    subst other
    omega

end Airbender.Trace.Machine.Proofs
