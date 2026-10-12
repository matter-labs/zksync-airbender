import Airbender.Proofs.UnifiedReduced.MixedCycles
import Airbender.Proofs.UnifiedReduced.MixedHistory
import Airbender.Proofs.Delegation.SharedOperations
import Airbender.Proofs.Delegation.SharedMemory

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem mixed_machine_member [Fact p.Prime] {data : RequestTrace p}
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
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

theorem mixed_machine_time [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (writeToken row.columns row.assignment port).time).value = (port.event row.columns row.assignment).1 := by
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.publicProgram.initialClock inputs.publicProgram.initialAligned row member
  exact (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
    clock.1 clock.2 (Trace.Proofs.port_offset row port present)).2

theorem ordinary_zero_preserving [Fact p.Prime] (hp : 524288 < p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    RowZeroPreserving row := by
  cases row with
  | mk kind w =>
    cases kind
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
    obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded _ member ordinary)
    have source := run_program_sources inputs.ordinaryProgram entry present
    rcases Mixed.Proofs.fields_cases source.fields with standard | custom
    · have fetched : Fetched w before :=
        ⟨entry, ⟨source.bytes, source.decoded, standard⟩, query,
          UnifiedReduced.Proofs.decoder_selectors hp core
            (UnifiedReduced.Proofs.decoder_field_bounds standard).2.1 query⟩
      exact UnifiedReduced.Proofs.row_zero_preserving hp core (accepted.active _ member) fetched
    · exact UnifiedReduced.Proofs.custom_row_zero_preserving hp core custom query

theorem mixed_zero_rules [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (requests : RequestBinding data before) : Transfer.CellWriteRules (mixedData data) (Cell.register 0).addressCode 0 := by
  intro edge present same reads
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := machine_port_native row (by simpa using portMember)
    by_cases caller : row ∈ data.callers
    · rw [machine_ports_caller caller] at portMember
      have modes : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
        simpa [architecturalPorts] using portMember
      rcases modes with rfl | rfl
      · exact reads _ present (Nat.le_refl _) same
      · have zero := congrArg (fun word : Word => Nat.pair word.lo word.hi)
          (requests.callers row caller).registers.2.2
        change _ = Nat.pair 0 0
        simpa only [destinationToken, MemoryToken.word, Nat.pair_unpair,
          Trace.Row.columns, CircuitLayout.columns] using zero
    · have preserving := ordinary_zero_preserving (by dsimp [timestampBase] at hp; omega) accepted inputs member caller
      apply preserving port native same
      intro earlier earlierMember order zero
      apply reads _ (mixed_machine_member member (by rwa [machine_ports_ordinary member caller]))
      · rw [mixed_machine_time hp inverse accepted inputs member earlierMember,
          mixed_machine_time hp inverse accepted inputs member native]
        exact order
      · exact zero
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    exact False.elim (Delegation.Proofs.port_not_zero row (by simpa using portMember) same)

theorem mixed_write_rules [Fact p.Prime] (hp : 8388608 ≤ p)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells) :
    Transfer.WriteRules (mixedData data) := by
  have workerRules := Delegation.Proofs.operation_rules_of_queries hp rotationInverse
    accepted.workerConstraints inputs.tables inputs.rounds (by
      intro row member family
      have active := accepted.workerActive row member
      rwa [Delegation.Row.columns, family] at active)
  intro edge present reads
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := machine_port_native row (by simpa using portMember)
    have core := Verification.holds_of_sublist (accepted.constraints row member)
      (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
    simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at native
    rcases native with rfl | rfl | rfl
    · exact reads _ present (Nat.le_refl _)
    · exact reads _ present (Nat.le_refl _)
    · simpa [write_word, Word.Bounded] using UnifiedReduced.Proofs.destination_bounds core
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
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells) :
    MixedMemoryEffects data before cells := by
  have requests := request_binding (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts (by decide) (by decide) accepted inputs requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨inputs.initialization, inputs.distinct⟩
  have zeroRules := mixed_zero_rules (by decide) (by decide) accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero inputs.initialization) zeroRules
  have rules := mixed_write_rules (by decide) (by decide) accepted inputs
  have words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded := by
    intro edge present
    exact ⟨Transfer.read_bounds facts initialized rules edge present,
      Transfer.produced_bounds facts initialized rules edge.2
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩)))⟩
  have zero : ∀ edge ∈ (mixedData data).steps, edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
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
    obtain ⟨cell, member, same⟩ := Transfer.initialized_cell facts initialized present
    exact ⟨cell, member, same, cell_address_bound cell⟩
  · apply Delegation.Caller.Proofs.worker_effects_of_reads accepted.workerConstraints inputs.tables inputs.rounds accepted.workerActive
    intro row member port present
    exact (words _ (mixed_worker_member member present)).1
  · exact ⟨events, after, permutation, order, realized,
      mixed_worker_execution (by decide) (by decide) accepted inputs requests permutation order realized,
      mixed_cycle_execution (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram requests
        permutation order realized,
      Transfer.terminal_sail_reads facts initialized bound final⟩

end Airbender.UnifiedReduced.Caller.Proofs
