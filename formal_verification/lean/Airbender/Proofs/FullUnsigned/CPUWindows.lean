import Airbender.Proofs.FullUnsigned.MemoryWindows
import Airbender.Proofs.Reduced.NativeClocks

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
open AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Every actual CPU event uses one of its native three access slots. -/
theorem unrolled_cpu_event_time
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (event : MemoryAccess) (present : event ∈ machineEvents row) :
    ∃ offset < 3, event.1 =
      (decodeTimestamp row.assignment row.columns.initialTime).value + offset + 1 := by
  unfold machineEvents at present
  obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
  have native := Delegation.Caller.Proofs.machine_port_native row (by simpa using included)
  have clock := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned row member
  have offsets : row.ports.toList.map (fun port => port.clock.offset) = [0, 1, 2] :=
    @ClockLaws.offsets PooledFamily inferInstance babyBearModulus inferInstance inferInstance row
  have selected : port.clock.offset ∈ row.ports.toList.map (fun port => port.clock.offset) :=
    List.mem_map.mpr ⟨port, by simpa using native, rfl⟩
  rw [offsets] at selected
  have bound : port.clock.offset < 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
    omega
  have time := (write_time (by decide)
    (base := rawPair row.assignment row.columns.initialTime)
    clock.1 clock.2 (by omega : port.clock.offset < 4)).2
  exact ⟨port.clock.offset, bound, congrArg (fun value : Nat => value + 1) time⟩

/-- An actual CPU event lies in exactly its own instruction window. This
holds for all six families and both full unsigned caller forms. -/
theorem unrolled_cpu_event_window
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row other : Trace.Row babyBearModulus PooledFamily)
    (member : row ∈ trace.rows) (included : other ∈ trace.rows)
    (event : MemoryAccess) (present : event ∈ machineEvents other) :
    ((decodeTimestamp row.assignment row.columns.initialTime).value < event.1 ∧
      event.1 ≤ (decodeTimestamp row.assignment row.columns.initialTime).value + 4) ↔ other = row := by
  obtain ⟨offset, bound, time⟩ :=
    unrolled_cpu_event_time accepted initialClock initialAligned other included event present
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have aligned (current : Trace.Row babyBearModulus PooledFamily) (currentMember : current ∈ trace.rows) :
      (decodeTimestamp current.assignment current.columns.initialTime).value % 4 = 0 := by
    simpa [Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using
      (clocks current currentMember).2
  have rowAligned := aligned row member
  have otherAligned := aligned other included
  constructor
  · intro interval
    have same : (decodeTimestamp other.assignment other.columns.initialTime).value =
        (decodeTimestamp row.assignment row.columns.initialTime).value := by omega
    have unique := state_clocks_unique (by decide)
      (by decide +kernel : SerializedInverse.Clock babyBearModulus)
      accepted.cpuEquations accepted.states initialClock initialAligned
    exact List.inj_on_of_nodup_map unique included member same
  · intro same
    subst other
    omega

end Airbender.Compiler.MachineTargets.Proofs
