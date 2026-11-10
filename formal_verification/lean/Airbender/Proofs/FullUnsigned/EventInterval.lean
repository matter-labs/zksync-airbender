import Airbender.Proofs.FullUnsigned.CPUWindows

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Every CPU, standard-worker and split-worker event lies within the same
native path endpoints. Exact combined matching supplies each worker's slot. -/
theorem unrolled_full_event_interval
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {event : MemoryAccess}
    (member : event ∈ (unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent) :
    (timeOfPair trace.initial.timestamp).value < event.1 ∧
      event.1 ≤ (timeOfPair trace.terminal.timestamp).value := by
  have intervals := state_clock_interval (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
  change edge ∈ pooledSteps trace ++ workers.steps ++ splitWorkers.steps at included
  rw [List.append_assoc] at included
  rcases List.mem_append.mp included with machine | rest
  · obtain ⟨row, present, native⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp native
    have actual : transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port) ∈
        AddSub.Modular.External.Caller.Proofs.machineEvents row :=
      List.mem_map.mpr ⟨port, portMember, rfl⟩
    obtain ⟨offset, small, time⟩ := unrolled_cpu_event_time
      accepted initialClock initialAligned row present _ actual
    have lower := (intervals row present).1
    have upper := (intervals row present).2
    change (timeOfPair trace.initial.timestamp).value ≤ row.clock at lower
    change row.clock + 4 ≤ (timeOfPair trace.terminal.timestamp).value at upper
    change (transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port)).1 =
      row.clock + offset + 1 at time
    omega
  · rcases List.mem_append.mp rest with standard | split
    · obtain ⟨worker, present, native⟩ := List.mem_flatMap.mp standard
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp native
      obtain ⟨row, member, _, _, _, slot⟩ := unrolled_full_standard_worker_slot
        accepted equations active initialClock initialAligned worker present
      have time := slot port (by simpa using portMember)
      have lower := (intervals row member).1
      have upper := (intervals row member).2
      change (timeOfPair trace.initial.timestamp).value ≤ row.clock at lower
      change row.clock + 4 ≤ (timeOfPair trace.terminal.timestamp).value at upper
      change (transferEvent (readToken worker.assignment port, worker.writeToken port)).1 = row.clock + 4 at time
      constructor <;> omega
    · obtain ⟨worker, present, native⟩ := List.mem_flatMap.mp split
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp native
      obtain ⟨row, member, _, _, _, slot⟩ := unrolled_full_split_worker_slot
        accepted equations active initialClock initialAligned worker present
      have time := slot port (by simpa using portMember)
      have lower := (intervals row member).1
      have upper := (intervals row member).2
      change (timeOfPair trace.initial.timestamp).value ≤ row.clock at lower
      change row.clock + 4 ≤ (timeOfPair trace.terminal.timestamp).value at upper
      change (transferEvent (readToken worker.assignment port,
        worker.writeToken splitWorkers.cached port)).1 = row.clock + 4 at time
      constructor <;> omega

end Airbender.Compiler.MachineTargets.Proofs
