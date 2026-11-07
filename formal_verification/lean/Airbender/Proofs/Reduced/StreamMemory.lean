import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Reduced.StreamMemoryClocks
import Airbender.Proofs.AddSub.ModularExternalDecoder
import Airbender.Proofs.Delegation.SharedOperations
import Airbender.Proofs.Trace.PooledHistory

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000


theorem mixed_machine_member [Fact p.Prime] {data : RequestTrace p}
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    {port : MemoryPort} (present : port ∈ machinePorts row) :
    (readToken row.assignment port, writeToken row.columns row.assignment port) ∈ data.mixedSteps :=
  List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, member,
    List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))

theorem mixed_worker_member [Fact p.Prime] {data : RequestTrace p}
    {row : Delegation.Row p} (member : row ∈ data.workers.rows)
    {port : MemoryPort} (present : port ∈ row.ports) :
    (readToken row.assignment port, row.writeToken port) ∈ data.mixedSteps :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, member,
    List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))

theorem mixed_ordinary_source [Fact p.Prime]
    {data : RequestTrace p} {program : List PooledProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program before ca oa cells)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    ∃ entry ∈ program, entry.SourceWith before AddSub.Modular.External.decoderFields ∧
      entry.data.family = row.family ∧ row.decoderQuery = entry.query := by
  obtain ⟨entry, present, family, query⟩ := decoder_member (accepted.ordinaryDecoded row member ordinary)
  exact ⟨entry, present, run_program_sources inputs.ordinaryProgram entry present, family, query⟩

theorem mixed_machine_time [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List PooledProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program before ca oa cells)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (writeToken row.columns row.assignment port).time).value =
      (port.event row.columns row.assignment).1 := by
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned row member
  exact (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
    clock.1 clock.2 (Trace.Proofs.port_offset row port present)).2

theorem mixed_zero_rules [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List PooledProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program before ca oa cells)
    (requests : RequestBinding data before) :
    Transfer.CellWriteRules (mixedData data) (Cell.register 0).addressCode 0 := by
  intro edge present same reads
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := machine_port_native row (by simpa using portMember)
    by_cases caller : row ∈ data.callers
    · have family := (caller_member caller).2
      rw [machine_ports_caller caller] at portMember
      have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
          port = AddSub.importedConstraintsMemoryPorts[2] := by simpa [architecturalPorts] using portMember
      rcases modes with rfl | rfl
      · exact reads _ present (Nat.le_refl _) same
      · have zero := congrArg (fun word : Word => Nat.pair word.lo word.hi)
          (requests.callers row caller).1.zeroDestination
        simp only [Trace.Row.columns, family, CircuitLayout.columns]
        change _ = Nat.pair 0 0
        simpa only [destination, MemoryToken.word, Nat.pair_unpair] using zero
    · obtain ⟨entry, _, source, family, query⟩ := mixed_ordinary_source accepted inputs member caller
      have preserving := pooled_row_zero_preserving AddSub.Modular.External.Proofs.decoderRules
        (by dsimp [timestampBase] at hp; omega) data.machine.rom row
        (accepted.constraints row member) (AddSub.Modular.External.Proofs.source_cases source) family query
      apply preserving port native same
      intro earlier earlierMember order zero
      have included := mixed_machine_member member (by rwa [machine_ports_ordinary member caller])
      apply reads _ included
      · rw [mixed_machine_time hp inverse accepted inputs member earlierMember,
          mixed_machine_time hp inverse accepted inputs member native]
        exact order
      · exact zero
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    exact False.elim (Delegation.Proofs.port_not_zero row (by simpa using portMember) same)

theorem mixed_write_rules [Fact p.Prime] (hp : FieldCapacity.NoWrap p 33554432)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : RequestTrace p} {program : List PooledProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program before ca oa cells)
    (rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round)
    (requests : RequestBinding data before) : Transfer.WriteRules (mixedData data) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have workerRules := Delegation.Proofs.operation_rules_of_queries (by omega : 8388608 ≤ p)
    rotationInverse accepted.workerConstraints inputs.tables rounds (by
      intro row member family
      have active := accepted.workerActive row member
      rwa [Delegation.Row.columns, family] at active)
  intro edge present reads
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := machine_port_native row (by simpa using portMember)
    by_cases caller : row ∈ data.callers
    · have family := (caller_member caller).2
      rw [machine_ports_caller caller] at portMember
      have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
          port = AddSub.importedConstraintsMemoryPorts[2] := by simpa [architecturalPorts] using portMember
      rcases modes with rfl | rfl
      · exact reads _ present (Nat.le_refl _)
      · simp only [Trace.Row.columns, family, CircuitLayout.columns]
        change (destination row.assignment).Bounded
        rw [(requests.callers row caller).1.zeroDestination]
        norm_num [Word.Bounded, limbBase]
    · obtain ⟨entry, _, source, family, query⟩ := mixed_ordinary_source accepted inputs member caller
      have rules := pooled_row_write_rule hp (accepted.constraints row member) (accepted.active row member)
        inputs.initialization inputs.wordTable inputs.subwordTable (AddSub.Modular.External.Proofs.source_cases source) family query
      apply rules port native
      intro earlier earlierMember order
      have included := mixed_machine_member member (by rwa [machine_ports_ordinary member caller])
      apply reads _ included
      rw [mixed_machine_time size clockInverse accepted inputs member earlierMember,
        mixed_machine_time size clockInverse accepted inputs member native]
      exact order
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    apply workerRules row member ?_ port (by simpa using portMember)
    intro source sourceMember
    apply reads _ (mixed_worker_member member sourceMember)
    have same : (row.writeToken source).time = (row.writeToken port).time := by
      simp only [Delegation.Row.writeToken, Delegation.Proofs.port_offset row sourceMember,
        Delegation.Proofs.port_offset row (by simpa using portMember)]
    rw [same]

theorem mixed_memory_effects
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program before ca oa cells)
    (rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round) :
    MixedMemoryEffects data before cells := by
  have requests := request_binding_checks (by decide) (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts (by decide) (by decide) accepted inputs requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨inputs.initialization, inputs.distinct⟩
  have zeroRules := mixed_zero_rules (by decide) (by decide) accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (initial_zero inputs.initialization) zeroRules
  have rules := mixed_write_rules (by decide) (by decide) (by decide) accepted inputs rounds requests
  have words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded := by
    intro edge present
    exact ⟨Transfer.read_bounds facts initialized rules edge present,
      Transfer.produced_bounds facts initialized rules edge.2
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩)))⟩
  have zero : ∀ edge ∈ (mixedData data).steps,
      edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
    intro edge present same
    have value := zeroRules edge present same (by
      intro previous member _ key
      exact zeroReads previous member key)
    rw [value]
    rfl
  obtain ⟨history, events, after, bound, permutation, order, realized, final⟩ :=
    Transfer.native_sail_history facts initialized inputs.aligned zero
  refine ⟨requests, zeroReads, words, Transfer.terminal_bounds facts initialized rules, ?_, ?_, ?_⟩
  · intro edge present
    obtain ⟨cell, member, same⟩ := Transfer.initialized_cell facts initialized.toBoundaryInputs present
    exact ⟨cell, member, same, cell_address_bound cell⟩
  · apply worker_effects_of_reads accepted.workerConstraints inputs.tables rounds accepted.workerActive
    intro row member port present
    exact (words _ (mixed_worker_member member present)).1
  · exact ⟨events, after, permutation, order, realized,
      Transfer.terminal_sail_reads facts initialized bound final⟩

end Airbender.AddSub.Modular.External.Caller.Proofs
