import Human.Trace.Delegation.RVMixedMemory
import Slop.Delegation.RVSharedOperations
import Slop.Delegation.MixedClocks
import Slop.Trace.RVValuesPooled
import Slop.Trace.RVZeroPooled

/-! RV siblings of the mixed-pool proofs (`MixedClocks.lean`, `MixedMemory.lean`) over `RVRequestTrace`: ordinary rows
    come from the RV six-family table (`rv_pooled_row_zero_preserving`, `rv_pooled_row_write_rule`), the seeds are
    `initialImageRV` reads and the history is an `RVHistory`. -/

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

def rvMixedData [Fact p.Prime] (data : RVRequestTrace p) : Transfer.Data p :=
  ⟨data.machine.initialMemory, data.machine.terminalMemory, data.mixedSteps⟩

theorem rv_machine_ports_caller [Fact p.Prime] {data : RVRequestTrace p}
    {row : Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    machinePorts row = architecturalPorts := by
  obtain ⟨_, selected⟩ := List.mem_filter.mp member
  simp only [machinePorts, selected, ↓reduceIte]

theorem rv_machine_ports_ordinary [Fact p.Prime] {data : RVRequestTrace p}
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    (ordinary : row ∉ data.callers) : machinePorts row = row.ports := by
  have notSelected : ¬ (row.family == .addSub && decide (Requests.Selected row.assignment)) = true := by
    intro selected
    exact ordinary (List.mem_filter.mpr ⟨member, selected⟩)
  simp only [machinePorts, ite_eq_right notSelected]

theorem rv_mixed_write_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {program : List RVPooledProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells)
    (requests : RVRequestBinding data before) :
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
    exact (write_time_of_room (by omega) (base := rawPair row.assignment row.columns.invocation) (requests.clocks row member)
      (by simpa only [offset, decodeTimestamp, rawPair] using requests.clockRoom row member)).1

theorem rv_mixed_memory_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {program : List RVPooledProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells)
    (requests : RVRequestBinding data before) :
    ∀ edge ∈ data.mixedSteps, (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.machine.initialMemory ++ data.mixedSteps.map Prod.snd,
      (timeOfPair token.time).Bounded := by
    intro token present
    rcases List.mem_append.mp present with initial | written
    · exact Transfer.rv_image_clocks inputs.initialization token initial
    · obtain ⟨edge, member, rfl⟩ := List.mem_map.mp written
      exact rv_mixed_write_clocks hp inverse accepted inputs requests edge member
  intro edge member
  exact ⟨produced edge.1 (accepted.memory.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))),
    rv_mixed_write_clocks hp inverse accepted inputs requests edge member⟩

theorem rv_mixed_memory_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {program : List RVPooledProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells)
    (requests : RVRequestBinding data before) : Transfer.Facts (rvMixedData data) := by
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
    have previous := (rv_mixed_memory_clocks hp inverse accepted inputs requests edge present).1
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
        · exact (rv_mixed_memory_clocks hp inverse accepted inputs requests _
            (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, member,
              List.mem_map.mpr ⟨source, by simpa using included, rfl⟩⟩)))).1
        · by_cases caller : row ∈ data.callers
          · have family := (rv_caller_member caller).2
            rw [rv_machine_ports_caller caller] at included
            have native : source ∈ AddSub.importedConstraintsMemoryPorts := by
              simpa [Trace.Row.ports, family, CircuitLayout.ports] using sourceMember
            simp [AddSub.importedConstraintsMemoryPorts] at native
            rcases native with rfl | rfl | rfl
            · exact False.elim (included (by simp [architecturalPorts, AddSub.importedConstraintsMemoryPorts]))
            · have empty := congrArg MemoryToken.time (requests.callers row caller).1.emptyRead
              change rawPair row.assignment #v[27, 28] = (0, 0) at empty
              change (timeOfPair (rawPair row.assignment #v[27, 28])).Bounded
              rw [empty]
              norm_num [timeOfPair, Timestamp.Bounded, timestampBase]
            · exact False.elim (included (by simp [architecturalPorts, AddSub.importedConstraintsMemoryPorts]))
          · exact False.elim (included (by rwa [rv_machine_ports_ordinary member caller]))
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
        exact requests.clockRoom row member
      have order := native_port_order_of_room hp (requests.clocks row member) previous
        (facts.offsets port.clock (Delegation.Proofs.clock_member row native)) room checked.1
        (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using checked.2.1)
        (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using checked.2.2)
      exact order.trans_eq (write_time_of_room (by omega)
        (base := rawPair row.assignment row.columns.invocation) (requests.clocks row member) room).2.symm


theorem rv_mixed_machine_member [Fact p.Prime] {data : RVRequestTrace p}
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    {port : MemoryPort} (present : port ∈ machinePorts row) :
    (readToken row.assignment port, writeToken row.columns row.assignment port) ∈ data.mixedSteps :=
  List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, member,
    List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))

theorem rv_mixed_worker_member [Fact p.Prime] {data : RVRequestTrace p}
    {row : Delegation.Row p} (member : row ∈ data.workers.rows)
    {port : MemoryPort} (present : port ∈ row.ports) :
    (readToken row.assignment port, row.writeToken port) ∈ data.mixedSteps :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, member,
    List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))

theorem rv_mixed_ordinary_source [Fact p.Prime]
    {data : RVRequestTrace p} {program : List RVPooledProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    ∃ entry ∈ program, ∃ i : RV.Instr, rvPooledDecoderFields i = some entry.data ∧
      entry.data.family = row.family ∧ row.decoderQuery = entry.query := by
  obtain ⟨entry, present, family, query⟩ := rv_decoder_member (accepted.ordinaryDecoded row member ordinary)
  obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch inputs.ordinaryProgram entry present
  exact ⟨entry, present, i, fields, family, query⟩

theorem rv_mixed_machine_time [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {program : List RVPooledProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (writeToken row.columns row.assignment port).time).value =
      (port.event row.columns row.assignment).1 := by
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned row member
  exact (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
    clock.1 clock.2 (Trace.Proofs.port_offset row port present)).2

theorem rv_mixed_zero_rules [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {program : List RVPooledProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells)
    (requests : RVRequestBinding data before) :
    Transfer.CellWriteRules (rvMixedData data) (Cell.register 0).addressCode 0 := by
  intro edge present same reads
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := machine_port_native row (by simpa using portMember)
    by_cases caller : row ∈ data.callers
    · have family := (rv_caller_member caller).2
      rw [rv_machine_ports_caller caller] at portMember
      have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
          port = AddSub.importedConstraintsMemoryPorts[2] := by simpa [architecturalPorts] using portMember
      rcases modes with rfl | rfl
      · exact reads _ present (Nat.le_refl _) same
      · have zero := congrArg (fun word : Word => Nat.pair word.lo word.hi)
          (requests.callers row caller).1.zeroDestination
        simp only [Trace.Row.columns, family, CircuitLayout.columns]
        change _ = Nat.pair 0 0
        simpa only [destination, MemoryToken.word, Nat.pair_unpair] using zero
    · obtain ⟨entry, _, i, fields, family, query⟩ := rv_mixed_ordinary_source accepted inputs member caller
      have preserving := RVZero.rv_pooled_row_zero_preserving
        (by dsimp [timestampBase] at hp; omega) data.machine.rom row
        (accepted.constraints row member) fields family query
      apply preserving port native same
      intro earlier earlierMember order zero
      have included := rv_mixed_machine_member member (by rwa [rv_machine_ports_ordinary member caller])
      apply reads _ included
      · rw [rv_mixed_machine_time hp inverse accepted inputs member earlierMember,
          rv_mixed_machine_time hp inverse accepted inputs member native]
        exact order
      · exact zero
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    exact False.elim (Delegation.Proofs.port_not_zero row (by simpa using portMember) same)

theorem rv_mixed_write_rules [Fact p.Prime] (hp : 33554432 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RVRequestTrace p} {program : List RVPooledProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells)
    (requests : RVRequestBinding data before) : Transfer.WriteRules (rvMixedData data) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have workerRules := Delegation.Proofs.operation_rules_of_queries (by omega : 8388608 ≤ p)
    rotationInverse accepted.workerConstraints inputs.tables inputs.rounds (by
      intro row member family
      have active := accepted.workerActive row member
      rwa [Delegation.Row.columns, family] at active)
  intro edge present reads
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := machine_port_native row (by simpa using portMember)
    by_cases caller : row ∈ data.callers
    · have family := (rv_caller_member caller).2
      rw [rv_machine_ports_caller caller] at portMember
      have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
          port = AddSub.importedConstraintsMemoryPorts[2] := by simpa [architecturalPorts] using portMember
      rcases modes with rfl | rfl
      · exact reads _ present (Nat.le_refl _)
      · simp only [Trace.Row.columns, family, CircuitLayout.columns]
        change (destination row.assignment).Bounded
        rw [(requests.callers row caller).1.zeroDestination]
        norm_num [Word.Bounded, limbBase]
    · obtain ⟨entry, _, i, fields, family, query⟩ := rv_mixed_ordinary_source accepted inputs member caller
      have rules := RVValues.rv_pooled_row_write_rule hp (accepted.constraints row member)
        (accepted.active row member) inputs.wordTable inputs.subwordTable fields family query
      apply rules port native
      intro earlier earlierMember order
      have included := rv_mixed_machine_member member (by rwa [rv_machine_ports_ordinary member caller])
      apply reads _ included
      rw [rv_mixed_machine_time size clockInverse accepted inputs member earlierMember,
        rv_mixed_machine_time size clockInverse accepted inputs member native]
      exact order
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    apply workerRules row member ?_ port (by simpa using portMember)
    intro source sourceMember
    apply reads _ (rv_mixed_worker_member member sourceMember)
    have same : (row.writeToken source).time = (row.writeToken port).time := by
      simp only [Delegation.Row.writeToken, Delegation.Proofs.port_offset row sourceMember,
        Delegation.Proofs.port_offset row (by simpa using portMember)]
    rw [same]

theorem rv_mixed_memory_effects
    {data : RVRequestTrace babyBearModulus} {program : List RVPooledProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells) :
    RVMixedMemoryEffects data before cells := by
  have requests := rv_request_binding_checks (by decide) (by decide) (by decide)
    accepted.toRVRequestChecks inputs.publicProgram
  have facts := rv_mixed_memory_facts (by decide) (by decide) accepted inputs requests
  have initialized : Transfer.RVBoundaryInputs (rvMixedData data) before cells :=
    Transfer.rv_boundary_inputs inputs.initialization inputs.distinct
  have zeroRules := rv_mixed_zero_rules (by decide) (by decide) accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Transfer.rv_initial_zero inputs.initialization) zeroRules
  have rules := rv_mixed_write_rules (by decide) (by decide) (by decide) accepted inputs requests
  have bounds := rv_transfer_bounds facts (RVValues.rv_image_bounds inputs.initialization) rules
  have words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded := bounds.1
  have zero : ∀ edge ∈ (rvMixedData data).steps,
      edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
    intro edge present same
    have value := zeroRules edge present same (by
      intro previous member _ key
      exact zeroReads previous member key)
    rw [value]
    rfl
  obtain ⟨history, events, after, bound, permutation, order, realized, final⟩ :=
    Transfer.rv_native_history_at_boundary facts initialized inputs.aligned zero
  refine ⟨requests, zeroReads, words, bounds.2, ?_, ?_, ?_⟩
  · intro edge present
    obtain ⟨cell, member, same⟩ := SeedTransfer.initialized_cell facts initialized.toSeedInputs present
    exact ⟨cell, member, same, cell_address_bound cell⟩
  · apply worker_effects_of_reads accepted.workerConstraints inputs.tables inputs.rounds accepted.workerActive
    intro row member port present
    exact (words _ (rv_mixed_worker_member member present)).1
  · refine ⟨events, after, permutation, order, realized, ?_⟩
    intro token member
    obtain ⟨cell, present, same, read⟩ :=
      Transfer.rv_terminal_reads_at_boundary facts initialized bound final token member
    exact ⟨cell, present, same, by simpa [memoryWord, MemoryToken.word] using read⟩

end Airbender.Delegation.Caller.Proofs
