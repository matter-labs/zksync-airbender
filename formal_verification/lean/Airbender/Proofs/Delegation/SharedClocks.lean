import Airbender.Review.Trace.Delegation.SharedMemory
import Airbender.Proofs.Delegation.RequestTrace
import Airbender.Proofs.Trace.TransferHistory

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

private theorem architectural_member {port : MemoryPort} (member : port ∈ architecturalPorts) :
    port ∈ AddSub.importedConstraintsMemoryPorts := by
  simp [architecturalPorts] at member
  rcases member with rfl | rfl
  all_goals simp [AddSub.importedConstraintsMemoryPorts]

def sharedData [Fact p.Prime] (data : RequestTrace p) : Transfer.Data p :=
  ⟨data.machine.initialMemory, data.machine.terminalMemory, data.sharedSteps⟩

def sharedInputs [Fact p.Prime] {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (inputs : SharedMemoryInputs data before addresses cells) : Transfer.Inputs (sharedData data) before cells :=
  ⟨inputs.initialization, inputs.distinct⟩

theorem shared_write_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedMemoryInputs data before addresses cells)
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.sharedSteps, (timeOfPair edge.2.time).Bounded := by
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned
  intro edge present
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := accepted.callerRows.symm ▸ member
    have family := (caller_member caller).2
    have portIn := architectural_member (by simpa using portMember)
    have nativePort : port ∈ row.ports := by
      simpa [Trace.Row.ports, family, CircuitLayout.ports] using portIn
    have clock := clocks row member
    have offset := Trace.Proofs.port_offset row port nativePort
    simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock offset
    exact (write_time (by omega) (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime) clock.1 clock.2 offset).1
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have room := requests.clockRoom row member
    have offset := Delegation.Proofs.port_offset row (by simpa using portMember)
    exact (write_time_of_room (by omega) (base := rawPair row.assignment row.columns.invocation) (requests.clocks row member)
      (by simpa only [offset, decodeTimestamp, rawPair] using room)).1

theorem shared_memory_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedMemoryInputs data before addresses cells)
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.sharedSteps,
      (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.machine.initialMemory ++ data.sharedSteps.map Prod.snd,
      (timeOfPair token.time).Bounded := by
    intro token present
    rcases List.mem_append.mp present with initial | written
    · exact image_clocks inputs.initialization token initial
    · obtain ⟨edge, member, rfl⟩ := List.mem_map.mp written
      exact shared_write_clocks hp inverse accepted inputs requests edge member
  intro edge member
  exact ⟨produced edge.1 (accepted.memory.mem_iff.mpr
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))),
    shared_write_clocks hp inverse accepted inputs requests edge member⟩

theorem shared_memory_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedMemoryInputs data before addresses cells)
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.sharedSteps,
      (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned
  intro edge edgeMember
  have previous := (shared_memory_clocks hp inverse accepted inputs requests edge edgeMember).1
  rcases List.mem_append.mp edgeMember with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := accepted.callerRows.symm ▸ rowMember
    have family := (caller_member caller).2
    have nativePort := architectural_member (by simpa using portMember)
    have clock := clocks row rowMember
    simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock
    have core := accepted.constraints row rowMember
    simp only [Trace.Row.constraints, family, CircuitLayout.constraints] at core
    have previousClocks : ∀ timePort ∈ AddSub.importedConstraintsTraceColumns.ports,
        (decodeTimestamp row.assignment timePort.previous).Bounded := by
      intro timePort present
      simp [AddSub.importedConstraintsTraceColumns] at present
      rcases present with rfl | rfl | rfl
      · exact (shared_memory_clocks hp inverse accepted inputs requests _
          (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, rowMember,
            List.mem_map.mpr ⟨AddSub.importedConstraintsMemoryPorts[0], by
              simp [architecturalPorts], rfl⟩⟩)))).1
      · have empty := congrArg MemoryToken.time (requests.callers row caller).1.emptyRead
        change rawPair row.assignment #v[27, 28] = (0, 0) at empty
        change (timeOfPair (rawPair row.assignment #v[27, 28])).Bounded
        rw [empty]
        norm_num [timeOfPair, Timestamp.Bounded, timestampBase]
      · exact (shared_memory_clocks hp inverse accepted inputs requests _
          (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, rowMember,
            List.mem_map.mpr ⟨AddSub.importedConstraintsMemoryPorts[2], by
              simp [architecturalPorts], rfl⟩⟩)))).1
    have effects := addSub_clock hp inverse core ⟨clock.1, clock.2, previousClocks⟩
    have inClocks : port.clock ∈ AddSub.importedConstraintsTraceColumns.ports := by
      rw [← AddSub.memory_clocks]
      exact Array.mem_map.mpr ⟨port, nativePort, rfl⟩
    have order := (effects.accesses port.clock inClocks).1
    have offset : port.clock.offset < 4 := by
      have rowPort : port ∈ row.ports := by
        simpa [Trace.Row.ports, family, CircuitLayout.ports] using nativePort
      exact Trace.Proofs.port_offset row port rowPort
    exact order.trans_eq (write_time (by omega)
      (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime)
      clock.1 clock.2 offset).2.symm
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have inArray : port ∈ row.ports := by simpa using portMember
    have facts := Delegation.Proofs.row_facts data.workers.setup row (accepted.workerConstraints row rowMember)
    have native := facts.comparisons port.clock (Delegation.Proofs.clock_member row inArray)
    have room : (decodeTimestamp row.assignment row.columns.invocation).lo + port.clock.offset < timestampBase := by
      rw [Delegation.Proofs.port_offset row inArray]
      exact requests.clockRoom row rowMember
    have order := native_port_order_of_room hp (requests.clocks row rowMember) previous
      (facts.offsets port.clock (Delegation.Proofs.clock_member row inArray)) room native.1
      (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using native.2.1)
      (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using native.2.2)
    exact order.trans_eq (write_time_of_room (by omega)
      (base := rawPair row.assignment row.columns.invocation)
      (requests.clocks row rowMember) room).2.symm

theorem shared_memory_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedMemoryInputs data before addresses cells)
    (requests : RequestBinding data before) : Transfer.Facts (sharedData data) := by
  refine ⟨accepted.memory, ?_, shared_memory_order hp inverse accepted inputs requests⟩
  intro edge member
  rcases List.mem_append.mp member with machine | worker
  · obtain ⟨_, _, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp step
    rfl
  · exact Delegation.Proofs.preserved_addresses edge worker

end Airbender.Delegation.Caller.Proofs
