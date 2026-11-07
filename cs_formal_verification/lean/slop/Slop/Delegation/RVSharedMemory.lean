import Human.Trace.Delegation.RVSharedMemory
import Slop.Delegation.RVRequestTrace
import Slop.Delegation.RVSharedImage
import Slop.Delegation.SharedClocks
import Slop.Trace.TransferValues

/-! RV siblings of the caller-only shared pool proofs (`SharedClocks.lean`, `SharedMemory.lean`) over `RVRequestTrace`:
    the clock and transfer arguments are the Sail ones; the public seeds are `initialImageRV` reads and the history is
    an `RVHistory` (`Transfer.rv_native_history_at_boundary`). -/

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

private theorem rv_architectural_member {port : MemoryPort} (member : port ∈ architecturalPorts) :
    port ∈ AddSub.importedConstraintsMemoryPorts := by
  simp [architecturalPorts] at member
  rcases member with rfl | rfl
  all_goals simp [AddSub.importedConstraintsMemoryPorts]

def rvSharedData [Fact p.Prime] (data : RVRequestTrace p) : Transfer.Data p :=
  ⟨data.machine.initialMemory, data.machine.terminalMemory, data.sharedSteps⟩

theorem rv_shared_write_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedMemoryInputs data before addresses cells)
    (requests : RVRequestBinding data before) :
    ∀ edge ∈ data.sharedSteps, (timeOfPair edge.2.time).Bounded := by
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned
  intro edge present
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := accepted.callerRows.symm ▸ member
    have family := (rv_caller_member caller).2
    have portIn := rv_architectural_member (by simpa using portMember)
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

theorem rv_shared_memory_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedMemoryInputs data before addresses cells)
    (requests : RVRequestBinding data before) :
    ∀ edge ∈ data.sharedSteps,
      (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.machine.initialMemory ++ data.sharedSteps.map Prod.snd,
      (timeOfPair token.time).Bounded := by
    intro token present
    rcases List.mem_append.mp present with initial | written
    · exact Transfer.rv_image_clocks inputs.initialization token initial
    · obtain ⟨edge, member, rfl⟩ := List.mem_map.mp written
      exact rv_shared_write_clocks hp inverse accepted inputs requests edge member
  intro edge member
  exact ⟨produced edge.1 (accepted.memory.mem_iff.mpr
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))),
    rv_shared_write_clocks hp inverse accepted inputs requests edge member⟩

theorem rv_shared_memory_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedMemoryInputs data before addresses cells)
    (requests : RVRequestBinding data before) :
    ∀ edge ∈ data.sharedSteps,
      (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned
  intro edge edgeMember
  have previous := (rv_shared_memory_clocks hp inverse accepted inputs requests edge edgeMember).1
  rcases List.mem_append.mp edgeMember with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := accepted.callerRows.symm ▸ rowMember
    have family := (rv_caller_member caller).2
    have nativePort := rv_architectural_member (by simpa using portMember)
    have clock := clocks row rowMember
    simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock
    have core := accepted.constraints row rowMember
    simp only [Trace.Row.constraints, family, CircuitLayout.constraints] at core
    have previousClocks : ∀ timePort ∈ AddSub.importedConstraintsTraceColumns.ports,
        (decodeTimestamp row.assignment timePort.previous).Bounded := by
      intro timePort present
      simp [AddSub.importedConstraintsTraceColumns] at present
      rcases present with rfl | rfl | rfl
      · exact (rv_shared_memory_clocks hp inverse accepted inputs requests _
          (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, rowMember,
            List.mem_map.mpr ⟨AddSub.importedConstraintsMemoryPorts[0], by
              simp [architecturalPorts], rfl⟩⟩)))).1
      · have empty := congrArg MemoryToken.time (requests.callers row caller).1.emptyRead
        change rawPair row.assignment #v[27, 28] = (0, 0) at empty
        change (timeOfPair (rawPair row.assignment #v[27, 28])).Bounded
        rw [empty]
        norm_num [timeOfPair, Timestamp.Bounded, timestampBase]
      · exact (rv_shared_memory_clocks hp inverse accepted inputs requests _
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

theorem rv_shared_memory_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedMemoryInputs data before addresses cells)
    (requests : RVRequestBinding data before) : Transfer.Facts (rvSharedData data) := by
  refine ⟨accepted.memory, ?_, rv_shared_memory_order hp inverse accepted inputs requests⟩
  intro edge member
  rcases List.mem_append.mp member with machine | worker
  · obtain ⟨_, _, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp step
    rfl
  · exact Delegation.Proofs.preserved_addresses edge worker



theorem rv_shared_zero_closed [Fact p.Prime]
    {data : RVRequestTrace p} {before : RV.State} (accepted : RVSharedMemoryAccepted data)
    (requests : RVRequestBinding data before) :
    ∀ edge ∈ data.sharedSteps, edge.1.address = (Cell.register 0).addressCode →
      edge.1.value = 0 → edge.2.value = 0 := by
  intro edge member same old
  rcases List.mem_append.mp member with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := accepted.callerRows.symm ▸ rowMember
    have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
        port = AddSub.importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using portMember
    rcases modes with rfl | rfl
    · exact old
    · have zero := (requests.callers row caller).1.zeroDestination
      have encoded := congrArg (fun word : Word => Nat.pair word.lo word.hi) zero
      change _ = Nat.pair 0 0
      simpa only [destination, MemoryToken.word, Nat.pair_unpair] using encoded
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact False.elim (Delegation.Proofs.port_not_zero row (by simpa using present) same)

theorem rv_shared_source_values [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedMemoryInputs data before addresses cells)
    (requests : RVRequestBinding data before) :
    ∀ row ∈ data.callers, (sourceToken row.assignment).value = 0 := by
  have facts := rv_shared_memory_facts hp inverse accepted inputs requests
  have closed := rv_shared_zero_closed accepted requests
  have reads := Transfer.read_cell_values facts (Cell.register 0).addressCode 0
    (Transfer.rv_initial_zero inputs.initialization) closed
  intro row member
  have step : (sourceToken row.assignment,
      writeToken AddSub.importedConstraintsTraceColumns row.assignment
        AddSub.importedConstraintsMemoryPorts[0]) ∈ data.sharedSteps := by
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_flatMap.mpr
    refine ⟨row, accepted.callerRows ▸ member, ?_⟩
    apply List.mem_map.mpr
    exact ⟨AddSub.importedConstraintsMemoryPorts[0], by simp [architecturalPorts], rfl⟩
  exact reads _ step (requests.callers row member).1.sourceAddress

theorem rv_shared_memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedMemoryInputs data before addresses cells) :
    RVSharedMemoryEffects data before cells := by
  have requests := rv_request_binding_checks hp clockInverse pcInverse accepted.toRVRequestChecks inputs.publicProgram
  have facts := rv_shared_memory_facts hp clockInverse accepted inputs requests
  have initialized : Transfer.RVBoundaryInputs (rvSharedData data) before cells :=
    Transfer.rv_boundary_inputs inputs.initialization inputs.distinct
  have zero : ∀ edge ∈ (rvSharedData data).steps,
      edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
    have reads := Transfer.read_cell_values facts (Cell.register 0).addressCode 0
      (Transfer.rv_initial_zero inputs.initialization) (rv_shared_zero_closed accepted requests)
    intro edge present same
    have value := rv_shared_zero_closed accepted requests edge present same (reads edge present same)
    rw [value]
    rfl
  obtain ⟨history, events, after, bound, permutation, order, realized, final⟩ :=
    Transfer.rv_native_history_at_boundary facts initialized inputs.aligned zero
  refine ⟨requests, rv_shared_source_values hp clockInverse accepted inputs requests, ?_, ?_⟩
  · intro row present port member
    have step : (readToken row.assignment port, row.writeToken port) ∈ (rvSharedData data).steps :=
      List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, present,
        List.mem_map.mpr ⟨port, by simpa using member, rfl⟩⟩))
    obtain ⟨cell, _, same⟩ := SeedTransfer.initialized_cell facts initialized.toSeedInputs step
    rw [address_word same.symm]
    exact cell_address_bound cell
  · refine ⟨events, after, permutation, order, realized, ?_⟩
    intro token member
    obtain ⟨cell, present, same, read⟩ :=
      Transfer.rv_terminal_reads_at_boundary facts initialized bound final token member
    exact ⟨cell, present, same, by simpa [memoryWord, MemoryToken.word] using read⟩


end Airbender.Delegation.Caller.Proofs
