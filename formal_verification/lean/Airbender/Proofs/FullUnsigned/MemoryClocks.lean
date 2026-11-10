import Airbender.Proofs.FullUnsigned.RequestClocks
import Airbender.Proofs.Delegation.MixedClocks
import Airbender.Proofs.Keccak.SplitMemory

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The full machine uses one exact architectural RAM pool for all rows. -/
def unrolledFullMemoryData (trace : PooledTrace babyBearModulus)
    (workers : Delegation.MemoryData babyBearModulus)
    (splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus) :
    Transfer.Data babyBearModulus :=
  ⟨trace.initialMemory, trace.terminalMemory,
    pooledSteps trace ++ workers.steps ++ splitWorkers.steps⟩

/-- The combined request permutation bounds every produced architectural
clock. CPU clocks and worker invocation clocks need no separate RAM pool. -/
theorem unrolled_full_write_clocks
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps,
      (timeOfPair edge.2.time).Bounded := by
  have hp : FieldCapacity.NoWrap babyBearModulus timestampBase := by decide
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have requests := (unrolled_request_clock_bounds accepted initialClock initialAligned).2.1
  intro edge present
  change edge ∈ pooledSteps trace ++ workers.steps ++ splitWorkers.steps at present
  rw [List.append_assoc] at present
  rcases List.mem_append.mp present with machine | rest
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have clock := clocks row member
    have offset := Trace.Proofs.port_offset row port
      (Delegation.Caller.Proofs.machine_port_native row (by simpa using portMember))
    exact (write_time hp (base := rawPair row.assignment row.columns.initialTime)
      clock.1 clock.2 offset).1
  · rcases List.mem_append.mp rest with standard | split
    · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp standard
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
      have invocation := requests _ (List.mem_append.mpr
        (Or.inl (List.mem_map.mpr ⟨row, member, rfl⟩)))
      have offset := Delegation.Proofs.port_offset row (by simpa using portMember)
      exact (write_time_of_room hp (base := rawPair row.assignment row.columns.invocation)
        invocation.1 (by simpa only [offset, Delegation.Requests.fulfillment,
          decodeTimestamp, rawPair, timeOfPair] using invocation.2)).1
    · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp split
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
      have invocation := requests _ (List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨row, member, rfl⟩)))
      have offset := Keccak.Split.Native.Proofs.port_offset splitWorkers.cached row
        (by simpa using portMember)
      exact (write_time_of_room hp
        (base := rawPair row.assignment (row.columns splitWorkers.cached).invocation)
        invocation.1 (by simpa only [offset, Keccak.Split.Native.Row.fulfillment,
          decodeTimestamp, rawPair, timeOfPair] using invocation.2)).1

/-- Exact combined RAM matching transfers produced clock bounds to every
read. This includes grouped split reads and all standard worker ports. -/
theorem unrolled_full_memory_clocks
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (seed : ∀ token ∈ trace.initialMemory, (timeOfPair token.time).Bounded) :
    ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps,
      (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have written := unrolled_full_write_clocks accepted initialClock initialAligned
  have produced : ∀ token ∈ trace.initialMemory ++
      (unrolledFullMemoryData trace workers splitWorkers).steps.map Prod.snd,
      (timeOfPair token.time).Bounded := by
    intro token member
    rcases List.mem_append.mp member with initial | output
    · exact seed token initial
    · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp output
      exact written edge present
  intro edge member
  exact ⟨produced edge.1 (accepted.ram.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))),
    written edge member⟩

end Airbender.Compiler.MachineTargets.Proofs
