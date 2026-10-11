import Airbender.Review.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.RequestTrace
import Airbender.Proofs.Trace.TransferHistory

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384


def mixedData [Fact p.Prime] (data : RequestTrace p) : Transfer.Data p :=
  ⟨data.machine.initialMemory, data.machine.terminalMemory, data.mixedSteps⟩

theorem machine_ports_caller [Fact p.Prime] {data : RequestTrace p}
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.callers) :
    machinePorts row = architecturalPorts := by
  have selected : Selected row.assignment := of_decide_eq_true (List.mem_filter.mp member).2
  simp only [machinePorts, if_pos selected]

theorem machine_ports_ordinary [Fact p.Prime] {data : RequestTrace p}
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (ordinary : row ∉ data.callers) : machinePorts row = row.ports := by
  have notSelected : ¬ Selected row.assignment := by
    intro selected
    exact ordinary (List.mem_filter.mpr ⟨member, decide_eq_true selected⟩)
  simp only [machinePorts, if_neg notSelected]

theorem machine_port_native (row : Trace.Row p UnifiedFamily)
    {port : MemoryPort} (member : port ∈ machinePorts row) : port ∈ row.ports := by
  unfold machinePorts at member
  split at member
  next =>
    simp [architecturalPorts] at member
    rcases member with rfl | rfl
    all_goals simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  next => exact member

theorem mixed_write_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.mixedSteps, (timeOfPair edge.2.time).Bounded := by
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned
  intro edge present
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have clock := clocks row member
    have offset := Trace.Proofs.port_offset row port (machine_port_native row (by simpa using portMember))
    exact (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime) clock.1 clock.2 offset).1
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have offset := Delegation.Proofs.port_offset row (by simpa using portMember)
    exact (write_time_of_room (by omega) (base := rawPair row.assignment row.columns.invocation) (requests.clocks row member).1
      (by simpa only [offset, decodeTimestamp, rawPair] using (requests.clocks row member).2)).1

theorem mixed_memory_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.mixedSteps, (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.machine.initialMemory ++ data.mixedSteps.map Prod.snd,
      (timeOfPair token.time).Bounded := by
    intro token present
    rcases List.mem_append.mp present with initial | written
    · exact image_clocks inputs.initialization token initial
    · obtain ⟨edge, member, rfl⟩ := List.mem_map.mp written
      exact mixed_write_clocks hp inverse accepted inputs requests edge member
  intro edge member
  exact ⟨produced edge.1 (accepted.memory.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))),
    mixed_write_clocks hp inverse accepted inputs requests edge member⟩

theorem mixed_memory_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (requests : RequestBinding data before) : Transfer.Facts (mixedData data) := by
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned
  refine ⟨accepted.memory, ?_, ?_⟩
  · intro edge member
    rcases List.mem_append.mp member with machine | worker
    · obtain ⟨_, _, step⟩ := List.mem_flatMap.mp machine
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp step
      rfl
    · exact Delegation.Proofs.preserved_addresses edge worker
  · intro edge present
    have previous := (mixed_memory_clocks hp inverse accepted inputs requests edge present).1
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
        · exact (mixed_memory_clocks hp inverse accepted inputs requests _
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

end Airbender.UnifiedReduced.Caller.Proofs
