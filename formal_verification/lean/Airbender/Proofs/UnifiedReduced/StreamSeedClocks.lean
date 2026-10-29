import Airbender.Proofs.UnifiedReduced.UnissuedWorkers

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Trace Arithmetic Trace.Proofs Caller.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem mixed_memory_clocks_of_seed [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State}
    {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (seed : ∀ token ∈ data.machine.initialMemory, (timeOfPair token.time).Bounded)
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.mixedSteps, (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.machine.initialMemory ++ data.mixedSteps.map Prod.snd,
      (timeOfPair token.time).Bounded := by
    intro token present
    rcases List.mem_append.mp present with initial | written
    · exact seed token initial
    · obtain ⟨edge, member, rfl⟩ := List.mem_map.mp written
      exact mixed_write_clocks hp inverse accepted publicProgram requests edge member
  intro edge member
  exact ⟨produced edge.1 (accepted.memory.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))),
    mixed_write_clocks hp inverse accepted publicProgram requests edge member⟩

theorem mixed_memory_facts_of_seed [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State}
    {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (seed : ∀ token ∈ data.machine.initialMemory, (timeOfPair token.time).Bounded)
    (requests : RequestBinding data before) : Transfer.Facts (mixedData data) := by
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    publicProgram.initialClock publicProgram.initialAligned
  refine ⟨accepted.memory, ?_, ?_⟩
  · intro edge member
    rcases List.mem_append.mp member with machine | worker
    · obtain ⟨_, _, step⟩ := List.mem_flatMap.mp machine
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp step
      rfl
    · exact Delegation.Proofs.preserved_addresses edge worker
  · intro edge present
    have previous := (mixed_memory_clocks_of_seed hp inverse accepted publicProgram seed requests edge present).1
    rcases List.mem_append.mp present with machine | worker
    · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
      have clock := clocks row member
      have allPrevious : ∀ timePort ∈ row.columns.ports,
          (decodeTimestamp row.assignment timePort.previous).Bounded := by
        intro timePort timeMember
        rw [← ports_clocks row] at timeMember
        obtain ⟨source, sourceMember, rfl⟩ := Array.mem_map.mp timeMember
        by_cases included : source ∈ machinePorts row
        · exact (mixed_memory_clocks_of_seed hp inverse accepted publicProgram seed requests _
            (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, member,
              List.mem_map.mpr ⟨source, by simpa using included, rfl⟩⟩)))).1
        · by_cases caller : row ∈ data.callers
          · rw [machine_ports_caller caller] at included
            have native : source ∈ importedConstraintsMemoryPorts := sourceMember
            simp [importedConstraintsMemoryPorts] at native
            rcases native with rfl | rfl | rfl
            · exact False.elim (included (by simp [architecturalPorts, importedConstraintsMemoryPorts]))
            · have empty := congrArg MemoryToken.time (requests.callers row caller).virtual.1
              change rawPair row.assignment #v[40, 41] = (0, 0) at empty
              change (timeOfPair (rawPair row.assignment #v[40, 41])).Bounded
              rw [empty]
              norm_num [timeOfPair, Timestamp.Bounded, timestampBase]
            · exact False.elim (included (by simp [architecturalPorts, importedConstraintsMemoryPorts]))
          · exact False.elim (included (by rwa [machine_ports_ordinary member caller]))
      have effects := ClockLaws.effects hp inverse data.machine.rom row
        (accepted.constraints row member) ⟨clock.1, clock.2, allPrevious⟩
      have native := machine_port_native row (by simpa using portMember)
      have inClocks : port.clock ∈ row.columns.ports := by
        rw [← ports_clocks row]
        exact Array.mem_map.mpr ⟨port, native, rfl⟩
      exact (effects.accesses port.clock inClocks).1.trans_eq
        (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
          clock.1 clock.2 (Trace.Proofs.port_offset row port native)).2.symm
    · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp worker
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
      have native : port ∈ row.ports := by simpa using portMember
      have facts := Delegation.Proofs.row_facts data.workers.setup row (accepted.workerConstraints row member)
      have checked := facts.comparisons port.clock (Delegation.Proofs.clock_member row native)
      have room : (decodeTimestamp row.assignment row.columns.invocation).lo + port.clock.offset < timestampBase := by
        rw [Delegation.Proofs.port_offset row native]
        exact (requests.clocks row member).2
      have order := native_port_order_of_room hp (requests.clocks row member).1 previous
        (facts.offsets port.clock (Delegation.Proofs.clock_member row native)) room checked.1
        (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using checked.2.1)
        (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using checked.2.2)
      exact order.trans_eq (write_time_of_room (by omega)
        (base := rawPair row.assignment row.columns.invocation) (requests.clocks row member).1 room).2.symm

private theorem first_machine_port (row : Trace.Row p UnifiedFamily) :
    importedConstraintsMemoryPorts[0] ∈ machinePorts row := by
  unfold machinePorts
  split
  · simp [architecturalPorts]
  · cases row with
    | mk kind w => cases kind; simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]

/-- The mandatory offset-zero access has a strictly earlier read. Native
    four-alignment therefore places every machine row at clock four or later,
    even when no positive public initial-clock premise is supplied. -/
theorem machine_native_clock_positive_of_seed [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (seed : ∀ token ∈ data.machine.initialMemory, (timeOfPair token.time).Bounded)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows) :
    4 ≤ Delegation.Caller.startClock row := by
  have requests := request_binding hp inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts_of_seed hp inverse accepted publicProgram seed requests
  have first := first_machine_port row
  have positive := facts.order _ (mixed_machine_member member first)
  have time := mixed_machine_time_of_program hp inverse accepted publicProgram member
    (machine_port_native row first)
  have alignment := (machine_clock_facts hp inverse accepted.toRequestChecks publicProgram member).1
  have base : (timeOfPair (writeToken row.columns row.assignment importedConstraintsMemoryPorts[0]).time).value =
      Delegation.Caller.startClock row := by
    simpa [MemoryPort.event, importedConstraintsMemoryPorts, Delegation.Caller.startClock, Trace.Row.clock] using time
  rw [base] at positive
  omega

end Airbender.UnifiedReduced.Caller.Stream.Proofs
