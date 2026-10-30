import Airbender.Proofs.FullUnsigned.MemoryClocks
import Airbender.Proofs.Keccak.SplitPortOrder

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Native CPU, standard worker and split worker equations give one ordered
RAM history. Fixed controller provenance and seed clock bounds stay explicit. -/
theorem unrolled_full_memory_facts
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (splitEquations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (splitActive : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (control : Keccak.Split.Native.ControlSetupFacts splitWorkers.setup)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (seed : ∀ token ∈ trace.initialMemory, (timeOfPair token.time).Bounded) :
    Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers) := by
  have hp : FieldCapacity.ClockNoWrap babyBearModulus timestampBase := by decide
  have noWrap : FieldCapacity.NoWrap babyBearModulus timestampBase := by decide
  have inverse : SerializedInverse.Clock babyBearModulus := by decide +kernel
  have clocks := state_clock_inputs hp inverse accepted.cpuEquations accepted.states
    initialClock initialAligned
  have bounded := unrolled_full_memory_clocks accepted initialClock initialAligned seed
  have requests := (unrolled_request_clock_bounds accepted initialClock initialAligned).2.1
  let callers : Delegation.Caller.RequestTrace babyBearModulus := ⟨trace, workers, []⟩
  refine ⟨accepted.ram, ?_, ?_⟩
  · intro edge member
    change edge ∈ pooledSteps trace ++ workers.steps ++ splitWorkers.steps at member
    rw [List.append_assoc] at member
    rcases List.mem_append.mp member with machine | rest
    · obtain ⟨_, _, step⟩ := List.mem_flatMap.mp machine
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp step
      rfl
    · rcases List.mem_append.mp rest with standard | split
      · exact Delegation.Proofs.preserved_addresses edge standard
      · exact Keccak.Split.Native.Proofs.preserved_addresses edge split
  · intro edge member
    have previous := (bounded edge member).1
    change edge ∈ pooledSteps trace ++ workers.steps ++ splitWorkers.steps at member
    rw [List.append_assoc] at member
    rcases List.mem_append.mp member with machine | rest
    · obtain ⟨row, present, step⟩ := List.mem_flatMap.mp machine
      obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
      have clock := clocks row present
      have allPrevious : ∀ timePort ∈ row.columns.ports,
          (decodeTimestamp row.assignment timePort.previous).Bounded := by
        intro timePort timeMember
        rw [← ports_clocks row] at timeMember
        obtain ⟨source, sourceMember, rfl⟩ := Array.mem_map.mp timeMember
        by_cases physical : source ∈ machinePorts row
        · have inMachine : (readToken row.assignment source,
              writeToken row.columns row.assignment source) ∈ pooledSteps trace :=
            List.mem_flatMap.mpr ⟨row, present,
              List.mem_map.mpr ⟨source, by simpa using physical, rfl⟩⟩
          have inPool : (readToken row.assignment source,
              writeToken row.columns row.assignment source) ∈
                (unrolledFullMemoryData trace workers splitWorkers).steps :=
            List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inMachine)))
          exact (bounded _ inPool).1
        · by_cases caller : row ∈ callers.callers
          · have family := (caller_member caller).2
            rw [machine_ports_caller caller] at physical
            have native : source ∈ AddSub.importedConstraintsMemoryPorts := by
              simpa [Trace.Row.ports, family, CircuitLayout.ports] using sourceMember
            simp [AddSub.importedConstraintsMemoryPorts] at native
            rcases native with rfl | rfl | rfl
            · exact False.elim (physical (by simp [architecturalPorts, AddSub.importedConstraintsMemoryPorts]))
            · have selected : Delegation.Requests.Selected row.assignment := by
                have filtered := (List.mem_filter.mp caller).2
                have both : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by
                  simpa only [Delegation.Caller.RequestTrace.callers, Bool.and_eq_true,
                    beq_iff_eq, decide_eq_true_eq] using filtered
                exact both.2
              have core := accepted.cpuEquations row present
              simp only [Trace.Row.constraints, family, CircuitLayout.constraints] at core
              have native := Verification.holds_of_sublist core
                (List.sublist_append_left _ AddSub.importedConstraintsTimestampLookups)
              have empty := congrArg MemoryToken.time
                (Delegation.Requests.Proofs.caller_tokens native selected).1
              change rawPair row.assignment #v[27, 28] = (0, 0) at empty
              change (timeOfPair (rawPair row.assignment #v[27, 28])).Bounded
              rw [empty]
              norm_num [timeOfPair, Timestamp.Bounded, timestampBase]
            · exact False.elim (physical (by simp [architecturalPorts, AddSub.importedConstraintsMemoryPorts]))
          · exact False.elim (physical (by rwa [machine_ports_ordinary present caller]))
      have effects := ClockLaws.effects hp inverse trace.rom row
        (accepted.cpuEquations row present) ⟨clock.1, clock.2, allPrevious⟩
      have native := machine_port_native row (by simpa using included)
      have inClocks : port.clock ∈ row.columns.ports := by
        rw [← ports_clocks row]
        exact Array.mem_map.mpr ⟨port, native, rfl⟩
      exact (effects.accesses port.clock inClocks).1.trans_eq
        (write_time noWrap (base := rawPair row.assignment row.columns.initialTime)
          clock.1 clock.2 (Trace.Proofs.port_offset row port native)).2.symm
    · rcases List.mem_append.mp rest with standard | split
      · obtain ⟨row, present, step⟩ := List.mem_flatMap.mp standard
        obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
        have invocation := requests _ (List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨row, present, rfl⟩)))
        have native : port ∈ row.ports := by simpa using included
        have facts := Delegation.Proofs.row_facts workers.setup row (accepted.workerEquations row present)
        have checked := facts.comparisons port.clock (Delegation.Proofs.clock_member row native)
        have room : (decodeTimestamp row.assignment row.columns.invocation).lo +
            port.clock.offset < timestampBase := by
          rw [Delegation.Proofs.port_offset row native]
          exact invocation.2
        have order := native_port_order_of_room hp invocation.1 previous
          (facts.offsets port.clock (Delegation.Proofs.clock_member row native)) room checked.1
          (by simpa [Delegation.Requests.fulfillment, decodeTimestamp, timeOfPair, readToken, rawPair] using checked.2.1)
          (by simpa [Delegation.Requests.fulfillment, decodeTimestamp, timeOfPair, readToken, rawPair] using checked.2.2)
        exact order.trans_eq (write_time_of_room noWrap
          (base := rawPair row.assignment row.columns.invocation) invocation.1 room).2.symm
      · obtain ⟨row, present, step⟩ := List.mem_flatMap.mp split
        obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
        have invocation := requests _ (List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨row, present, rfl⟩)))
        have native : port ∈ row.ports splitWorkers.cached := by simpa using included
        have room : (decodeTimestamp row.assignment (row.columns splitWorkers.cached).invocation).lo +
            port.clock.offset < timestampBase := by
          rw [Keccak.Split.Native.Proofs.port_offset splitWorkers.cached row native]
          exact invocation.2
        have order := Keccak.Split.Proofs.split_physical_port_order hp control
          splitWorkers.cached row (splitEquations.rowsHold row present) (splitActive row present)
          native invocation.1 previous room
        exact order.trans_eq (write_time_of_room noWrap
          (base := rawPair row.assignment (row.columns splitWorkers.cached).invocation)
          invocation.1 room).2.symm

end Airbender.Compiler.MachineTargets.Proofs
